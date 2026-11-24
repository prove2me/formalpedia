-- Prove2me | solution 1 for GlobalTheory.UnRep.SmallMat.exists_coprime_nsmul_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:58:59.813682+00:00
-- url     : https://prove2.me/submissions/edc9bea4-09fa-4b61-a95d-5b73463fa425

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatrices
import Theorems.Thm_GlobalTheory_UnRep_SmallMat_exists_dvd_pow_mul_coprime
import Theorems.Thm_GlobalTheory_UnRep_SmallMat_exists_nsmul_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.SmallMat
open GlobalTheory.AdLat.Translate
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.UnRep.SmallMat
theorem _root_.solution (N : ℕ) (b : FiniteAdeleRing (𝓞 F) F)
    (hb : ∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal → b v = 0) :
    ∃ t : ℕ, t.Coprime N ∧ ∀ v, (t • b) v ∈ v.adicCompletionIntegers F := by
  obtain ⟨m, hm, h⟩ := exists_nsmul_integral b
  obtain ⟨t, k, ht, c, hc⟩ := exists_dvd_pow_mul_coprime N m hm
  refine ⟨t, ht, fun v => ?_⟩
  change t • b v ∈ _
  by_cases hv : (N : 𝓞 F) ∈ v.asIdeal
  · rw [hb v hv, smul_zero]; exact zero_mem _
  · have h1 : c • (m • b v) ∈ v.adicCompletionIntegers F := nsmul_mem (h v) c
    rw [smul_smul, mul_comm, ← hc, mul_smul, nsmul_eq_mul,
      HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, Nat.cast_pow, map_pow] at h1
    have hN : Valued.v ((N : ℕ) : v.adicCompletion F) = 1 := by
      have h1 := (v.valuation_eq_one_iff_notMem (K := F)).mpr hv
      have h2 := v.valuedAdicCompletion_eq_valuation' (K := F) ((N : ℕ) : F)
      have h3 : (algebraMap F (v.adicCompletion F)) ((N : ℕ) : F) =
        ((N : ℕ) : v.adicCompletion F) := map_natCast _ _
      rw [← h3]
      have h4 : (((N : ℕ) : 𝓞 F) : F) = ((N : ℕ) : F) :=
        map_natCast (algebraMap (𝓞 F) F) _
      exact h2.trans (h4 ▸ h1)
    rw [hN, one_pow, one_mul] at h1
    exact h1
end GlobalTheory.UnRep.SmallMat
