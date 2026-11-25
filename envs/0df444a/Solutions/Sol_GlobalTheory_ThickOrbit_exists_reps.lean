-- Prove2me | solution 1 for GlobalTheory.ThickOrbit.exists_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:52:48.975253+00:00
-- url     : https://prove2.me/submissions/c284cffb-5415-4bfb-a8e6-62d1859e92dd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryNearIdentityCloseTuplesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryTupleMatrixRightMulNearIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AlgMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ThickOrbitSelfDualUnramifiedLattice
import Theorems.Thm_GlobalTheory_ThickOrbit_pow_mem
import Theorems.Thm_GlobalTheory_ThickOrbit_smul_mem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.ThickOrbit
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.ThickOrbit
theorem _root_.solution (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {n : ℕ}
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (j : ℕ) :
    ∃ R : Set (Fin n → E), R.Finite ∧ ∀ v ∈ Λ, ∃ r ∈ R, ∃ w ∈ Λ,
      v = r + algebraMap F E ((ϖ : F) ^ j) • w := by
  obtain ⟨-, -, -, -, -, hc, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hc := hc j
  set I : Ideal L.O := Ideal.span {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)} with hI
  have hI' : I = Ideal.span {(⟨_, pow_mem L ϖ j⟩ : L.O)} := by
    rw [hI]
    exact congrArg Ideal.span (Set.ext fun y => by simp [Subtype.ext_iff])
  have : Finite (L.O ⧸ I) := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  obtain ⟨k, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hΛ.1
  refine ⟨Set.range fun q : Fin k → L.O ⧸ I => ∑ i, (q i).out • s i, Set.finite_range _,
    fun v hv => ?_⟩
  rw [← hs, Submodule.mem_span_range_iff_exists_fun] at hv
  obtain ⟨c, rfl⟩ := hv
  have h1 : ∀ i, ∃ d : L.O, c i = (Ideal.Quotient.mk I (c i)).out + ⟨_, pow_mem L ϖ j⟩ * d := by
    intro i
    have h2 : c i - (Ideal.Quotient.mk I (c i)).out ∈ I := by
      rw [← Ideal.Quotient.eq]
      exact (Quotient.out_eq' _).symm
    rw [hI', Ideal.mem_span_singleton] at h2
    obtain ⟨d, hd⟩ := h2
    exact ⟨d, by rw [← hd, ← hI']; ring⟩
  choose d hd using h1
  refine ⟨_, ⟨fun i => Ideal.Quotient.mk I (c i), rfl⟩, ∑ i, d i • s i, ?_, ?_⟩
  · refine Submodule.sum_mem _ fun i _ => Λ.smul_mem _ ?_
    rw [← hs]; exact Submodule.subset_span ⟨i, rfl⟩
  · rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [hd i, add_smul, mul_smul]
    rfl
end GlobalTheory.ThickOrbit
