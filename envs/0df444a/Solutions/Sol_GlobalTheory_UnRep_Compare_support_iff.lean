-- Prove2me | solution 1 for GlobalTheory.UnRep.Compare.support_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:23:19.476801+00:00
-- url     : https://prove2.me/submissions/2b22dc7b-89fd-4dff-8935-99948ca5caf9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSplitPlaceOfSplitPl
import Theorems.Thm_GlobalTheory_UnRep_Compare_loc_tmul
import Theorems.Thm_GlobalTheory_UnRep_Compare_eq_of_loc
import Theorems.Thm_GlobalTheory_UnRep_Compare_ind_pos
import Theorems.Thm_GlobalTheory_UnRep_Compare_ind_neg
import Theorems.Thm_GlobalTheory_UnRep_Compare_loc_ind_pos
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
theorem _root_.solution (p : HeightOneSpectrum (𝓞 F) → Prop) {n : ℕ} (h : Matrix (Fin n) (Fin n) (RA F E)) :
    (∃ e : FiniteAdeleRing (𝓞 F) F, e * e = e ∧ {v | e v ≠ 0}.Finite ∧
      (∀ v, e v ≠ 0 → p v) ∧ (e ⊗ₜ[F] (1 : E)) • (h - 1) = h - 1) ↔
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), (∀ v ∈ T, p v) ∧ ∀ v ∉ T, h.map (loc E v) = 1 := by
  have hone : ∀ v : HeightOneSpectrum (𝓞 F), h.map (loc E v) = 1 ↔ ∀ i j, loc E v ((h - 1) i j) = 0 := by
    intro v
    rw [← Matrix.map_one (loc E v) (map_zero _) (map_one _), ← Matrix.ext_iff]
    simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, sub_eq_zero]
  constructor
  · rintro ⟨e, -, hfin, hp, he⟩
    refine ⟨hfin.toFinset, fun v hv => hp v (hfin.mem_toFinset.1 hv), fun v hv => (hone v).2 fun i j => ?_⟩
    have h0 : e v = 0 := by
      by_contra h0
      exact hv (hfin.mem_toFinset.2 h0)
    rw [← he, Matrix.smul_apply, smul_eq_mul, map_mul, loc_tmul, h0, TensorProduct.zero_tmul, zero_mul]
  · rintro ⟨T, hp, hT⟩
    have hs : ∀ v, ind (T : Set (HeightOneSpectrum (𝓞 F))) v ≠ 0 → v ∈ T := fun v hv => by
      by_contra h0
      exact hv (ind_neg h0)
    refine ⟨ind T, ?_, T.finite_toSet.subset hs, fun v hv => hp v (hs v hv), ?_⟩
    · refine DFunLike.ext _ _ fun v => ?_
      change ind _ v * ind _ v = ind _ v
      by_cases hv : v ∈ (T : Set (HeightOneSpectrum (𝓞 F)))
      · rw [ind_pos hv, one_mul]
      · rw [ind_neg hv, zero_mul]
    · ext i j
      refine eq_of_loc fun v => ?_
      rw [Matrix.smul_apply, smul_eq_mul, map_mul]
      by_cases hv : v ∈ (T : Set (HeightOneSpectrum (𝓞 F)))
      · rw [loc_ind_pos hv, one_mul]
      · rw [(hone v).1 (hT v hv), mul_zero]
end GlobalTheory.UnRep.Compare
