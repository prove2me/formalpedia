-- Prove2me | solution 1 for GlobalTheory.HL.CloseTuples.exists_pow_denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:41:14.788015+00:00
-- url     : https://prove2.me/submissions/d1401fbb-5f6c-43d5-88a9-7dcc9b90bc2c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryNearIdentityCloseTuples

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CloseTuples
open GlobalTheory.HL.Eichler GlobalTheory.HL.DualInter
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}
namespace GlobalTheory.HL.CloseTuples
theorem _root_.solution [IsNonarchimedeanLocalField F] (L : LocE F E) {ϖ : 𝒪[F]}
    (hϖ : Irreducible ϖ) (x : E) : ∃ k : ℕ, algebraMap F E ϖ ^ k * x ∈ L.O := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; omega)
  have hx : IsAlgebraic 𝒪[F] x :=
    (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨d, hd0, hd⟩ := hx.exists_integral_multiple
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hϖ
  refine ⟨k, (L.O_def _).2 ?_⟩
  have h2 := hd.smul ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F])
  rw [smul_smul, Units.inv_mul_cancel_left, Algebra.smul_def, map_pow] at h2
  exact h2
end GlobalTheory.HL.CloseTuples
