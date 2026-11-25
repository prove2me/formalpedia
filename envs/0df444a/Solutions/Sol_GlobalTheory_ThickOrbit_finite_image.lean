-- Prove2me | solution 1 for GlobalTheory.ThickOrbit.finite_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:10:43.139634+00:00
-- url     : https://prove2.me/submissions/ef10c920-19ed-4a24-805c-16d648911c89

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
import Theorems.Thm_GlobalTheory_ThickOrbit_pow_add_smul
import Theorems.Thm_GlobalTheory_ThickOrbit_exists_reps
import Theorems.Thm_GlobalTheory_ThickOrbit_isUnit_pow
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
theorem _root_.solution (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {n m : ℕ}
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (M e : ℕ)
    (A : AddSubgroup (Fin m → Fin n → E))
    (hA : ∀ w : Fin m → Fin n → E, (∀ a, w a ∈ Λ) → algebraMap F E ((ϖ : F) ^ M) • w ∈ A)
    (S : Set (Fin m → Fin n → E)) (hS : ∀ x ∈ S, ∀ a, algebraMap F E ((ϖ : F) ^ e) • x a ∈ Λ) :
    ((QuotientAddGroup.mk : _ → _ ⧸ A) '' S).Finite := by
  obtain ⟨R, hR, hR'⟩ := exists_reps L hϖ hΛ (e + M)
  obtain ⟨u, hu⟩ := isUnit_pow (E := E) hϖ e
  refine ((Set.Finite.pi' (fun _ : Fin m => hR)).image
    (fun r => (QuotientAddGroup.mk ((↑u⁻¹ : E) • r) : _ ⧸ A))).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  choose r hr w hw h using fun a => hR' _ (hS x hx a)
  refine ⟨r, hr, ?_⟩
  rw [QuotientAddGroup.eq]
  convert hA w hw using 1
  funext a
  have h1 := congrArg (fun t => (↑u⁻¹ : E) • t) (h a)
  simp only [pow_add_smul, ← hu, smul_add, smul_smul (↑u⁻¹ : E) (u : E), Units.inv_mul, one_smul] at h1
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, h1]
  abel
end GlobalTheory.ThickOrbit
