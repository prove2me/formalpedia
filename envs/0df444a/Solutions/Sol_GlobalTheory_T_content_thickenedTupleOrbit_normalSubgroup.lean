-- Prove2me | solution 1 for GlobalTheory.T.content_thickenedTupleOrbit_normalSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:09:24.788411+00:00
-- url     : https://prove2.me/submissions/96915b43-8671-45d2-8c9f-f1b988e89c08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ContentThickenedTupleOrbitNormalSubgroup
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ContentThickenedTupleOrbitNormalSubgroupStatement
import Theorems.Thm_GlobalTheory_HL_cont_thick_torb_normal


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → ∀ K K' : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)), K ≤ isomG L Hm → K' ≤ K → (∀ a ∈ K, MulAut.conj a • K' = K') → K'.relIndex K ≠ 0 → ∀ i : ℕ, 1 ≤ i → (∀ y ∈ torb K' x, ∀ A ∈ congK L ϖ m i, cT L A * gramT L Hm x * A = gramT L Hm x → rmul y A ∈ torb K' x) → IsCO (tupLat L Λs m) (thick L ϖ (torb K' x) i) → cont (tupLat L Λs m) (thick L ϖ (torb K x) i) * ((fixG L Hm (Submodule.span E (Set.range x)) ⊓ K').relIndex (fixG L Hm (Submodule.span E (Set.range x)) ⊓ K) : ℝ) = (K'.relIndex K : ℝ) * cont (tupLat L Λs m) (thick L ϖ (torb K' x) i) := by
  first | exact @GlobalTheory.HL.cont_thick_torb_normal | exact GlobalTheory.HL.cont_thick_torb_normal | (intros; apply GlobalTheory.HL.cont_thick_torb_normal <;> assumption)
end _root_.GlobalTheory.T
