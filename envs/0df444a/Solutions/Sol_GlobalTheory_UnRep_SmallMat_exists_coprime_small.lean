-- Prove2me | solution 1 for GlobalTheory.UnRep.SmallMat.exists_coprime_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:10:28.616831+00:00
-- url     : https://prove2.me/submissions/be8db3b2-407f-4aa2-ba55-6adc24fd8b05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatrices
import Theorems.Thm_GlobalTheory_UnRep_SmallMat_exists_coprime_nsmul_integral
import Theorems.Thm_GlobalTheory_UnRep_SmallMat_nsmul_tmul_one
import Theorems.Thm_GlobalTheory_AdLat_Translate_hat_smul_int


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
theorem _root_.solution (S : Set (Fin n → E)) (N D : ℕ) (e : FiniteAdeleRing (𝓞 F) F)
    (M : Matrix (Fin n) (Fin n) (RA F E)) (hD : 0 < D)
    (hM : ∃ d : ℕ, 0 < d ∧ ∀ z ∈ hat F S, d • (M *ᵥ z) ∈ hat F S)
    (he : ∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal → e v = 0) :
    ∃ t : ℕ, t.Coprime N ∧ ∀ z ∈ hat F S, ∃ w ∈ hat F S,
      t • (((e ⊗ₜ[F] (1 : E) : RA F E) • M) *ᵥ z) = D • w := by
  obtain ⟨d, hd, hM⟩ := hM
  have hK : ((D * d : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 (Nat.mul_pos hD hd).ne'
  set b : FiniteAdeleRing (𝓞 F) F :=
    algebraMap F (FiniteAdeleRing (𝓞 F) F) ((D * d : ℕ) : F)⁻¹ * e with hb
  have hbe : e = (D * d) • b := by
    rw [hb, nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)),
      ← map_mul, mul_inv_cancel₀ hK, map_one, one_mul]
  obtain ⟨t, ht, h⟩ := exists_coprime_nsmul_integral N b fun v hv => by
    change _ * e v = 0
    rw [he v hv, mul_zero]
  refine ⟨t, ht, fun z hz => ⟨_, hat_smul_int h (hM z hz), ?_⟩⟩
  rw [hbe, Matrix.smul_mulVec, nsmul_tmul_one, nsmul_tmul_one, smul_assoc, smul_assoc, mul_smul,
    smul_comm t D, smul_comm d]
end GlobalTheory.UnRep.SmallMat
