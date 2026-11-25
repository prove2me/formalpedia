-- Prove2me | solution 1 for GlobalTheory.T.hermitianEichlerProduct_continuous_on_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:54:35.850997+00:00
-- url     : https://prove2.me/submissions/d1f0c4bb-efd0-46d2-90bd-b82e30241f3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianEichlerProductContinuousOnLattice
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianEichlerProductContinuousOnLatticeStatement
import Theorems.Thm_GlobalTheory_HL_EichCont_prod_eich_cont


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (N r : ℕ) (Hm : Matrix (Fin N) (Fin N) E) (X u : Fin r → Fin N → E) (s : Fin r → E) (e : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)) (he : ∀ i v, e i v = eich L Hm (X i) (u i) (s i) v) (Λ : Submodule L.O (Fin N → E)) (hΛ : IsLat L Λ) (c : Fˣ), ∃ d : Fˣ, ∀ (u' : Fin r → Fin N → E) (s' : Fin r → E) (e' : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)), (∀ i v, e' i v = eich L Hm (X i) (u' i) (s' i) v) → (∀ i j, ∃ o ∈ L.O, u' i j - u i j = algebraMap F E d * o) → (∀ i, ∃ o ∈ L.O, s' i - s i = algebraMap F E d * o) → ∀ x ∈ Λ, ∃ y ∈ Λ, ((List.ofFn e).prod).symm ((List.ofFn e').prod x) - x = algebraMap F E c • y := by
  first | exact @GlobalTheory.HL.EichCont.prod_eich_cont | exact GlobalTheory.HL.EichCont.prod_eich_cont | (intros; apply GlobalTheory.HL.EichCont.prod_eich_cont <;> assumption)
end _root_.GlobalTheory.T
