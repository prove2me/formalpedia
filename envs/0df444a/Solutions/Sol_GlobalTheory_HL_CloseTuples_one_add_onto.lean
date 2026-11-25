-- Prove2me | solution 1 for GlobalTheory.HL.CloseTuples.one_add_onto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:25:43.459936+00:00
-- url     : https://prove2.me/submissions/d801c4a8-03ea-48c6-9809-bbcbef61054b

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
theorem _root_.solution {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (p : L.O)
    (hp : p ∈ Ideal.jacobson (⊥ : Ideal L.O)) (A : (Fin n → E) →ₗ[E] (Fin n → E))
    (hA : ∀ v ∈ Λ, A v ∈ Λ) :
    Function.Bijective (LinearMap.id + (p : E) • A : (Fin n → E) →ₗ[E] (Fin n → E)) ∧
      ∀ v ∈ Λ, ∃ u ∈ Λ, u + (p : E) • A u = v := by
  set T : (Fin n → E) →ₗ[E] (Fin n → E) := LinearMap.id + (p : E) • A with hT
  have key : Λ ≤ Λ.map (T.restrictScalars L.O) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot hΛ.1 le_rfl fun z hz => ?_
    have hz' : z = T z + (-p) • A z := by
      change z = (z + (p : E) • A z) + (-(p : E)) • A z
      module
    rw [hz']
    exact Submodule.add_mem_sup ⟨z, hz, rfl⟩
      (Submodule.smul_mem_smul (Submodule.neg_mem _ hp) (hA z hz))
  have hs : Function.Surjective T := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hΛ.2, Submodule.span_le]
    intro v hv
    obtain ⟨u, -, hu⟩ := key hv
    exact ⟨u, hu⟩
  exact ⟨⟨OrzechProperty.injective_of_surjective_endomorphism T hs, hs⟩, fun v hv => key hv⟩
end GlobalTheory.HL.CloseTuples
