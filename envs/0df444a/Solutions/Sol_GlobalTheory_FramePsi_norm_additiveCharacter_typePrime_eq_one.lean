-- Prove2me | solution 1 for GlobalTheory.FramePsi.norm_additiveCharacter_typePrime_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:46:27.692805+00:00
-- url     : https://prove2.me/submissions/6630d8a0-fb73-4d23-b9aa-a2535cd70b97

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
import Theorems.Thm_GlobalTheory_FramePsi_exists_nsmul_mem
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
open GlobalTheory GlobalTheory.FramePsi
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.FramePsi
theorem _root_.solution [IsNonarchimedeanLocalField F] (L : LocE F E) (y : E) : ‖L.psi0 y‖ = 1 := by
  obtain ⟨n, hn, hy⟩ := exists_nsmul_mem L y
  have h1 : L.psi0 ((n : E) * y) = 1 := by
    simpa using (L.additive_character_dual_ring _).2 hy 1 L.O.one_mem
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow] at h1
  have h2 := congrArg norm h1
  rw [norm_pow, norm_one] at h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h2
end GlobalTheory.FramePsi
