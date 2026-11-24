-- Prove2me | solution 1 for GlobalTheory.UnRep.Compare.exists_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:39:38.278615+00:00
-- url     : https://prove2.me/submissions/25411f38-21be-4051-a7c2-184896bcc8da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSplitPlaceOfSplitPl
import Theorems.Thm_GlobalTheory_UnRep_Compare_ind_pos
import Theorems.Thm_GlobalTheory_UnRep_Compare_ind_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.Compare
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.UnRep.Compare
theorem _root_.solution (m : ℕ) (hm : m ≠ 0) (S : Set (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∈ S, (m : 𝓞 F) ∉ v.asIdeal) :
    ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
      (m : RA F E) * (a ⊗ₜ[F] (1 : E)) = ind S ⊗ₜ[F] (1 : E) := by
  have hm' : (m : F) ≠ 0 := by exact_mod_cast hm
  refine ⟨ind S * algebraMap F _ (m : F)⁻¹, fun v => ?_, ?_⟩
  · have : (ind S * algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F)⁻¹) v
        = ind S v * (((m : F)⁻¹ : F) : v.adicCompletion F) := rfl
    rw [this]
    by_cases hv : v ∈ S
    · rw [ind_pos hv, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀]
      have h1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) v).2 (hS v hv)
      rw [map_natCast] at h1
      rw [h1, inv_one]
    · rw [ind_neg hv, zero_mul]; exact zero_mem _
  · rw [← nsmul_eq_mul, TensorProduct.smul_tmul', nsmul_eq_mul,
      ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) m, mul_left_comm, ← map_mul,
      mul_inv_cancel₀ hm', map_one, mul_one]
end GlobalTheory.UnRep.Compare
