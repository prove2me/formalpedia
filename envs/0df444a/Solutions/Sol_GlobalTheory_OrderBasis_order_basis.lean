-- Prove2me | solution 1 for GlobalTheory.OrderBasis.order_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:24:25.063648+00:00
-- url     : https://prove2.me/submissions/9c845b5d-4f1f-4952-9b8d-2910a6f10d70

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsBasisFgMaximalOrderSpanningFree
import Theorems.Thm_GlobalTheory_OrderBasis_exists_basis
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts


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
open GlobalTheory GlobalTheory.OrderBasis
namespace GlobalTheory.OrderBasis
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n m : ℕ} (y : Fin m → Fin n → E), LinearIndependent E y → ∀ Q : Submodule L.O (Fin n → E), Q.FG → Submodule.span E (Q : Set (Fin n → E)) = Submodule.span E (Set.range y) → ∃ b : Fin m → Fin n → E, LinearIndependent E b ∧ Q = Submodule.span L.O (Set.range b) := by
  intro F _ _ _ _ _ E _ _ _ L n m y hy Q hQ hs
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  haveI : IsPrincipalIdealRing L.O := (GlobalTheory.UnramOrder.order_facts L ϖ hϖ).2.2.2.1
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  refine exists_basis L.O (fun x => ?_) y hy Q hQ hs
  obtain ⟨d, hd⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors 𝒪[F]) (Rₘ := F) x (Algebra.IsIntegral.isIntegral x)
  refine ⟨algebraMap 𝒪[F] E d, (L.O_def _).mpr isIntegral_algebraMap, ?_, (L.O_def _).mpr ?_⟩
  · rw [IsScalarTower.algebraMap_apply 𝒪[F] F E]
    exact (IsLocalization.map_units F d).map _
  · rwa [Submonoid.smul_def, Algebra.smul_def] at hd
end GlobalTheory.OrderBasis
