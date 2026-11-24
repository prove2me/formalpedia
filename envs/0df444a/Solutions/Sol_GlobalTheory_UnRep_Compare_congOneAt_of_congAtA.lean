-- Prove2me | solution 1 for GlobalTheory.UnRep.Compare.congOneAt_of_congAtA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:58:06.524462+00:00
-- url     : https://prove2.me/submissions/08b55471-f00f-4d89-b764-c2369e5c632c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSplitPlaceOfSplitPl
import Theorems.Thm_GlobalTheory_UnRep_Compare_loc_ind_pos
import Theorems.Thm_GlobalTheory_UnRep_Compare_exists_inv
import Theorems.Thm_GlobalTheory_UnRep_Compare_notMem_of_coprime
import Theorems.Thm_GlobalTheory_AdLat_Translate_hat_smul_int
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.Compare
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.UnRep.Compare
theorem _root_.solution {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (N D : ℕ)
    (k : Matrix (Fin n) (Fin n) (RA F E)) (h : CongAtA F L N D k) :
    CongOneAt N D (L : Set (Fin n → E)) k := by
  obtain ⟨t, ht, h⟩ := h
  intro v hv z hz
  obtain ⟨w, hw, e⟩ := h z hz
  have htv := notMem_of_coprime ht hv
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact htv (by simp)
  obtain ⟨a, ha, hat'⟩ := exists_inv (E := E) t ht0 {v} (fun u hu => by rw [hu]; exact htv)
  refine ⟨_, Translate.hat_smul_int ha hw, fun i => ?_⟩
  have e1 := congrArg (loc E v) (congrFun e i)
  have e2 := congrArg (loc E v) hat'
  rw [loc_ind_pos (Set.mem_singleton v)] at e2
  simp only [Pi.smul_apply, Pi.sub_apply, nsmul_eq_mul, smul_eq_mul, map_mul] at e1 e2 ⊢
  linear_combination (loc E v (a ⊗ₜ[F] (1 : E))) * e1 - (loc E v ((k *ᵥ z) i - z i)) * e2
end GlobalTheory.UnRep.Compare
