-- Prove2me | solution 1 for GlobalTheory.AdLat.lim_exists_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:47:25.684853+00:00
-- url     : https://prove2.me/submissions/12fda7cf-ad7c-4524-9493-f6c66ebe9aa6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionLatticeSeparatedCompleteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealDivisibleEqZero
import Theorems.Thm_GlobalTheory_AdLat_lim_nsmul_cancel
import Theorems.Thm_GlobalTheory_AdLat_cap_exists_denom
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
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
variable [NumberField E]
namespace GlobalTheory.AdLat
theorem _root_.solution (L : Submodule (𝓞 E) (Fin n → E))
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (φ : L →+ (Fin n → RA F E))
    (hφ : ∀ (r : 𝓞 E) (a : L), φ (r • a) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (r : E) : RA F E) • φ a) :
    ∃ g : Matrix (Fin n) (Fin n) (RA F E), ∀ a : L, g *ᵥ fv F (a : Fin n → E) = φ a := by
  classical
  choose d hd hdL using fun j : Fin n => cap_exists_denom L hsp (Pi.single j (1 : E))
  refine ⟨Matrix.of fun i j => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((d j : E)⁻¹) : RA F E) *
    φ ⟨_, hdL j⟩ i, fun a => ?_⟩
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun j => (d j : E)⁻¹ * (a : Fin n → E) j)
  have hc : ∀ j, IsIntegral ℤ (y.natAbs • ((d j : E)⁻¹ * (a : Fin n → E) j)) := by
    intro j
    have h1 := hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
    rcases Int.natAbs_eq y with h | h
    · rw [h, natCast_zsmul] at h1; exact h1
    · rw [h, neg_smul, natCast_zsmul] at h1; simpa using h1.neg
  have hD : 0 < y.natAbs := Int.natAbs_pos.mpr hy0
  let r : Fin n → 𝓞 E := fun j => ⟨_, hc j⟩
  have ha : y.natAbs • a = ∑ j, r j • (⟨_, hdL j⟩ : L) := by
    apply Subtype.ext
    funext i
    have hdi : (d i : E) ≠ 0 := Nat.cast_ne_zero.mpr (hd i).ne'
    simp only [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · change y.natAbs • (a : Fin n → E) i = (y.natAbs • ((d i : E)⁻¹ * (a : Fin n → E) i)) *
        (d i • (Pi.single i (1 : E) : Fin n → E) i)
      simp only [Pi.single_eq_same, nsmul_eq_mul]
      field_simp
    · intro j _ hj
      change (y.natAbs • ((d j : E)⁻¹ * (a : Fin n → E) j)) *
        (d j • (Pi.single j (1 : E) : Fin n → E) i) = 0
      simp [hj.symm]
    · simp
  apply lim_nsmul_cancel F hD
  rw [← map_nsmul, ha, map_sum]
  funext i
  simp only [hφ, Pi.smul_apply, Matrix.mulVec, dotProduct, Finset.sum_apply, Finset.smul_sum,
    Matrix.of_apply, fv, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  change _ = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (y.natAbs • ((d j : E)⁻¹ * (a : Fin n → E) j))) * _
  rw [TensorProduct.tmul_smul, smul_mul_assoc, mul_right_comm, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one]
end GlobalTheory.AdLat
