-- Prove2me | solution 1 for GlobalTheory.HL.DualInter.exists_denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:35:15.020589+00:00
-- url     : https://prove2.me/submissions/655ed251-5420-41d9-968f-c234c154608d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff


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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.DualInter
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
variable {L Hm}
variable [IsNonarchimedeanLocalField F]
namespace GlobalTheory.HL.DualInter
theorem _root_.solution (L : LocE F E) (x : E) : ∃ d ∈ L.O, IsUnit d ∧ d * x ∈ L.O := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; omega)
  have hx : IsAlgebraic 𝒪[F] x :=
    (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨d, hd0, hd⟩ := hx.exists_integral_multiple
  refine ⟨algebraMap F E d, (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 d.2,
    (IsUnit.mk0 (d : F) fun h => hd0 (Subtype.ext h)).map _, (L.O_def _).2 ?_⟩
  rwa [Algebra.smul_def] at hd
end GlobalTheory.HL.DualInter
