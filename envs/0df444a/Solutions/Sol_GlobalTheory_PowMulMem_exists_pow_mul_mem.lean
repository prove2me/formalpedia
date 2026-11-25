-- Prove2me | solution 1 for GlobalTheory.PowMulMem.exists_pow_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:59:02.310567+00:00
-- url     : https://prove2.me/submissions/a5f2f6be-b941-4308-ac77-4ecdc8ee48f2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AlgMem
import Theorems.Thm_GlobalTheory_PowMulMem_alg_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.PowMulMem
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.PowMulMem
theorem _root_.solution [IsNonarchimedeanLocalField F] (L : LocE F E) {ϖ : 𝒪[F]}
    (hϖ : Irreducible ϖ) (e : E) : ∃ k : ℕ, algebraMap F E ((ϖ : F) ^ k) * e ∈ L.O := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have h1 : IsAlgebraic F e := Algebra.IsAlgebraic.isAlgebraic e
  have h2 : IsAlgebraic 𝒪[F] e := (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 h1
  obtain ⟨c, hc0, hc⟩ := h2.exists_integral_multiple
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hϖ
  refine ⟨k, ?_⟩
  have h3 : c • e ∈ L.O := (L.O_def _).2 hc
  have h4 := L.O.mul_mem (alg_mem L ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F])) h3
  have h5 : ϖ ^ k = ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * c := by
    rw [hu, ← mul_assoc, Units.inv_mul, one_mul]
  have h6 : (ϖ : F) ^ k = (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) * (c : F) := by
    exact_mod_cast congrArg (fun x : 𝒪[F] => (x : F)) h5
  have h7 : c • e = algebraMap F E (c : F) * e := by
    rw [← Algebra.smul_def]; rfl
  rw [h6, map_mul, mul_assoc, ← h7]
  exact h4
end GlobalTheory.PowMulMem
