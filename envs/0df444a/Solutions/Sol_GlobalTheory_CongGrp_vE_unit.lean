-- Prove2me | solution 1 for GlobalTheory.CongGrp.vE_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:20:21.396612+00:00
-- url     : https://prove2.me/submissions/dc6a58b1-1e52-4dc3-b3cd-089f263760ec

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbit
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramVal_vE_valuation
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
open GlobalTheory GlobalTheory.CongGrp
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.CongGrp
theorem _root_.solution (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (u : (𝒪[F])ˣ) :
    vE L ϖ (algebraMap F E ((u : 𝒪[F]) : F)) = 0 := by
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  have hne : ∀ w : (𝒪[F])ˣ, ((w : 𝒪[F]) : F) ≠ 0 := fun w h => w.ne_zero (Subtype.ext h)
  have e1 := h1 1 1 one_ne_zero one_ne_zero
  have e2 := h1 _ _ (hne u) (hne u⁻¹)
  have e3 : ((u : 𝒪[F]) : F) * ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) = 1 := by
    rw [← Subring.coe_mul]; simp
  rw [e3] at e2
  rw [mul_one] at e1
  have a1 := (h3 _ (hne u)).2 (u : 𝒪[F]).2
  have a2 := (h3 _ (hne u⁻¹)).2 ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]).2
  omega
end GlobalTheory.CongGrp
