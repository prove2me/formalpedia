-- Prove2me | solution 1 for GlobalTheory.HL.LatDet.relIndex_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:12:43.947834+00:00
-- url     : https://prove2.me/submissions/f02dcf26-eea3-44cd-9837-bf61b54344d7

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardQuotPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardQuotPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuation
import Theorems.Thm_UpperTheory_Reformulated_B_Yzb5_relIndex_map


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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LatDet
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.HL.LatDet
theorem _root_.solution {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {W : Type} [AddCommGroup W] [Module F W]
    {ι : Type} [Fintype ι] (b : Module.Basis ι F W) (ψ : W →ₗ[F] W) (a : ℤ) (u : (𝒪[F])ˣ)
    (hd : LinearMap.det ψ = (ϖ : F) ^ a * ((u : 𝒪[F]) : F)) (W0 : AddSubgroup W)
    (hW : ∀ x, x ∈ W0 ↔ ∀ i, b.repr x i ∈ 𝒪[F]) (hψ : ∀ i j, b.repr (ψ (b j)) i ∈ 𝒪[F]) :
    ∃ m : ℕ, a = m ∧ (W0.map ψ.toAddMonoidHom).relIndex W0 = resQ ϖ ^ m :=
  _root_.UpperTheory.Reformulated.B.Yzb5.relIndex_map hϖ b ψ a u hd W0 hW hψ
end GlobalTheory.HL.LatDet
