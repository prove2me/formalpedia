-- Prove2me | solution 1 for GlobalTheory.UnRep.Compare.congAtA_of_congOneAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:23:16.464664+00:00
-- url     : https://prove2.me/submissions/6a8146f5-0f48-4079-aa7a-d915dc5e43c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSplitPlaceOfSplitPl
import Theorems.Thm_GlobalTheory_UnRep_Compare_eq_of_loc
import Theorems.Thm_GlobalTheory_UnRep_Compare_ind_int
import Theorems.Thm_GlobalTheory_UnRep_Compare_loc_ind_pos
import Theorems.Thm_GlobalTheory_UnRep_Compare_loc_ind_neg
import Theorems.Thm_GlobalTheory_UnRep_Compare_exists_inv
import Theorems.Thm_GlobalTheory_UnRep_Compare_exists_glue
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
theorem _root_.solution {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) {N D d : ℕ} (hN : N ≠ 0) (hD : D ≠ 0)
    (hd : d ≠ 0) (k : Matrix (Fin n) (Fin n) (RA F E))
    (hk : ∀ z ∈ hat F (L : Set (Fin n → E)), d • k *ᵥ z ∈ hat F (L : Set (Fin n → E)))
    (h : CongOneAt N D (L : Set (Fin n → E)) k) {t j : ℕ} (hdvd : D * d ∣ t * N ^ j) :
    ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), t • (k *ᵥ z - z) = D • w := by
  intro z hz
  obtain ⟨r, hr⟩ := hdvd
  obtain ⟨y, hy, hy'⟩ := exists_glue (L : Set (Fin n → E)) hN D (k *ᵥ z - z) fun v hv => h v hv z hz
  set S : Set (HeightOneSpectrum (𝓞 F)) := {v | (N : 𝓞 F) ∈ v.asIdeal} with hS
  obtain ⟨a, ha, ha'⟩ := exists_inv (E := E) (N ^ j) (pow_ne_zero _ hN) Sᶜ (fun v hv h => by
    rw [Nat.cast_pow] at h
    exact hv (v.isPrime.mem_of_pow_mem _ h))
  have hu : d • (k *ᵥ z - z) ∈ hat F (L : Set (Fin n → E)) := by
    rw [smul_sub]; exact sub_mem (hk z hz) (nsmul_mem hz d)
  refine ⟨_, add_mem (Translate.hat_smul_int (ind_int S) (nsmul_mem hy t))
    (Translate.hat_smul_int ha (nsmul_mem hu r)), funext fun i => eq_of_loc fun v => ?_⟩
  have e2 := congrArg (loc E v) ha'
  have e3 : ((t * N ^ j : ℕ) : v.adicCompletion F ⊗[F] E) = (D * d * r : ℕ) := by rw [hr]
  generalize k *ᵥ z - z = u at *
  by_cases hv : v ∈ S
  · have e1 := hy' v hv i
    have e4 : loc E v (a ⊗ₜ[F] (1 : E)) = 0 := by
      rw [loc_ind_neg (Set.notMem_compl_iff.2 hv), map_mul, map_natCast] at e2
      have hu : IsUnit ((N ^ j : ℕ) : v.adicCompletion F ⊗[F] E) := by
        rw [← map_natCast (algebraMap F _)]
        exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (pow_ne_zero _ hN))).map _
      exact (hu.mul_right_eq_zero).1 e2
    simp only [Pi.smul_apply, Pi.add_apply, nsmul_eq_mul, smul_eq_mul, map_mul, map_add, map_natCast,
      Pi.mul_apply, Pi.natCast_apply,
      loc_ind_pos hv, e4] at e1 ⊢
    linear_combination (t : v.adicCompletion F ⊗[F] E) * e1
  · rw [loc_ind_pos (Set.mem_compl hv)] at e2
    simp only [Pi.smul_apply, Pi.add_apply, nsmul_eq_mul, smul_eq_mul, map_mul, map_add, map_natCast,
      Pi.mul_apply, Pi.natCast_apply,
      loc_ind_neg hv] at e2 ⊢
    push_cast at e2 e3
    linear_combination (loc E v (a ⊗ₜ[F] (1 : E)) * loc E v (u i)) * e3 -
      (t : v.adicCompletion F ⊗[F] E) * loc E v (u i) * e2
end GlobalTheory.UnRep.Compare
