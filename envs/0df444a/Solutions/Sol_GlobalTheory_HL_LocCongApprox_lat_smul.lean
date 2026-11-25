-- Prove2me | solution 1 for GlobalTheory.HL.LocCongApprox.lat_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:04:21.707823+00:00
-- url     : https://prove2.me/submissions/72c9ceab-0032-4161-b908-fd7a58c84af2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLatIffMemLocP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntCastIsUnitCompletionAlmostAllPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsGlobalUnitriangularOfLocalCongruence

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LocCongApprox
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}
variable (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {N : ℕ}
namespace GlobalTheory.HL.LocCongApprox
theorem _root_.solution (Λ : Submodule (𝓞 E) (Fin N → E)) (t : 𝓞 E) (v : Fin N → (A.loc p).Ep)
    (hv : v ∈ A.lat p Λ) : (A.loc p).ιE (t : E) • v ∈ A.lat p (Ideal.span {t} • Λ) := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨u, hu, rfl⟩ := hw
    have e : (A.loc p).ιE (t : E) • A.bc p u = A.bc p (t • u) := by
      funext i
      change (A.loc p).ιE (t : E) * (A.loc p).ιE (u i) = (A.loc p).ιE (t • u i)
      rw [Algebra.smul_def, map_mul]
    rw [e]
    exact Submodule.subset_span ⟨_, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) hu, rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul o a _ ha =>
    have e : (A.loc p).ιE (t : E) • (o • a) = o • ((A.loc p).ιE (t : E) • a) := by
      change (A.loc p).ιE (t : E) • ((o : (A.loc p).Ep) • a) = (o : (A.loc p).Ep) • ((A.loc p).ιE (t : E) • a)
      rw [smul_smul, smul_smul, mul_comm]
    rw [e]
    exact Submodule.smul_mem _ o ha
end GlobalTheory.HL.LocCongApprox
