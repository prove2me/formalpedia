-- Prove2me | solution 1 for GlobalTheory.UnRep.Compare.exists_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:43:37.173116+00:00
-- url     : https://prove2.me/submissions/6596ffa2-02fc-474a-b3f2-378408c6f701

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSplitPlaceOfSplitPl
import Theorems.Thm_GlobalTheory_UnRep_Compare_ind_int
import Theorems.Thm_GlobalTheory_UnRep_Compare_loc_ind_pos
import Theorems.Thm_GlobalTheory_UnRep_Compare_loc_ind_neg
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
theorem _root_.solution {n : ℕ} (L : Set (Fin n → E)) {N : ℕ} (hN : N ≠ 0) (D : ℕ) (u : Fin n → RA F E)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal →
      ∃ y ∈ hat F L, ∀ i, loc E v (u i) = loc E v ((D • y) i)) :
    ∃ y ∈ hat F L, ∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal →
      ∀ i, loc E v (u i) = loc E v ((D • y) i) := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | (N : 𝓞 F) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(N : 𝓞 F)}) (by simpa using hN)).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  choose! y hy hy' using h
  refine ⟨∑ v ∈ hfin.toFinset, (ind {v} ⊗ₜ[F] (1 : E) : RA F E) • y v,
    sum_mem fun v hv => Translate.hat_smul_int (ind_int _) (hy v (hfin.mem_toFinset.1 hv)), fun v hv i => ?_⟩
  rw [hy' v hv i]
  simp only [Pi.smul_apply, nsmul_eq_mul, map_mul, Finset.sum_apply, map_sum, smul_eq_mul]
  rw [Finset.sum_eq_single v, loc_ind_pos (Set.mem_singleton v), one_mul]
  · intro w _ hw
    rw [loc_ind_neg (fun h => hw (Set.mem_singleton_iff.1 h).symm), zero_mul]
  · intro h
    exact absurd (hfin.mem_toFinset.2 hv) h
end GlobalTheory.UnRep.Compare
