-- Prove2me | solution 1 for GlobalTheory.HL.CloseTuples.mem_jac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:31:51.299939+00:00
-- url     : https://prove2.me/submissions/61c587f4-5f02-4026-8726-4272e41190e5

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
theorem _root_.solution [IsNonarchimedeanLocalField F] (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : ¬ IsUnit ϖ)
    (p : L.O) (hp : (p : E) = algebraMap F E ϖ) : p ∈ Ideal.jacobson (⊥ : Ideal L.O) := by
  have hm : ∀ c : 𝒪[F], algebraMap 𝒪[F] E c ∈ L.O := fun c =>
    (L.O_def _).2 isIntegral_algebraMap
  let f : 𝒪[F] →+* L.O := (algebraMap 𝒪[F] E).codRestrict L.O hm
  have hf : f.IsIntegral := fun x => by
    obtain ⟨p, hp, h⟩ := (L.O_def x).1 x.2
    refine ⟨p, hp, Subtype.ext ?_⟩
    change L.O.subtype _ = 0
    rw [Polynomial.hom_eval₂]
    exact h
  rw [Ideal.jacobson, Ideal.mem_sInf]
  rintro m ⟨-, hm⟩
  have h := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hf m
  have h2 : ϖ ∈ m.comap f := by
    rw [IsLocalRing.eq_maximalIdeal h]; exact hϖ
  have h3 : p = f ϖ := Subtype.ext hp
  rw [h3]
  exact h2
end GlobalTheory.HL.CloseTuples
