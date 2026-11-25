-- Prove2me | solution 1 for GlobalTheory.PowSmulMemLattice.exists_pow_mul_mem_O
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:47:22.871905+00:00
-- url     : https://prove2.me/submissions/b4da424a-db5f-4e5b-ab82-34a0c91a8adc

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPowSmulMemOfIsLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.PowSmulMemLattice
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.PowSmulMemLattice
theorem _root_.solution [IsNonarchimedeanLocalField F] (L : LocE F E)
    (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (c : E) :
    ∃ k : ℕ, algebraMap F E ((ϖ : F) ^ k) * c ∈ L.O := by
  haveI : IsFractionRing 𝒪[F] F := (Valuation.integer.integers (valuation F)).isFractionRing
  haveI : Module.Free F E := L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have hc : IsIntegral F c := Algebra.IsIntegral.isIntegral c
  obtain ⟨⟨m, hm⟩, hmc⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors 𝒪[F]) c hc
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hm0 hϖ
  refine ⟨k, (L.O_def _).2 ?_⟩
  have h2 : IsIntegral 𝒪[F] ((u : 𝒪[F]) • (m • c)) := hmc.smul _
  convert h2 using 1
  have e1 : (ϖ : F) ^ k = ((ϖ ^ k : 𝒪[F]) : F) := by push_cast; rfl
  rw [e1, ← hu, smul_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply 𝒪[F] F E, mul_comm u.1 m]
  rfl
end GlobalTheory.PowSmulMemLattice
