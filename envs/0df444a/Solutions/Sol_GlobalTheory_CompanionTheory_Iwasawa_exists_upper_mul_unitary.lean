-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwasawa.exists_upper_mul_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:56:32.114872+00:00
-- url     : https://prove2.me/submissions/27e8a8ef-89a0-4ee4-aa49-e83137623a8c

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaChol
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUpperMulUnitaryComplex
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwasawa_exists_upper_mul_unitary_complex
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwasawa_evalMat_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwasawa_evalMat_conjTranspose
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwasawa_matrix_ext_eval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwasawa
namespace GlobalTheory.CompanionTheory.Iwasawa
theorem _root_.solution {ι : Type} {n : ℕ} (y : GL (Fin n) (ι → ℂ)) :
    ∃ (b : GL (Fin n) (ι → ℂ)) (k : Matrix.unitaryGroup (Fin n) (ι → ℂ)),
      (∀ i j : Fin n, j < i → b.val i j = 0) ∧ y = b * Unitary.toUnits k := by
  have hu : ∀ w : ι, IsUnit (evalMat w (y : Matrix (Fin n) (Fin n) (ι → ℂ))) :=
    fun w => (Units.isUnit y).map (evalMat w)
  choose B R K hB hBR hRB hKK hKK' hY using fun w => exists_upper_mul_unitary_complex _ (hu w)
  let b : Matrix (Fin n) (Fin n) (ι → ℂ) := fun i j w => B w i j
  let r : Matrix (Fin n) (Fin n) (ι → ℂ) := fun i j w => R w i j
  let k : Matrix (Fin n) (Fin n) (ι → ℂ) := fun i j w => K w i j
  have eb : ∀ w, evalMat w b = B w := fun w => by ext i j; rw [evalMat_apply]
  have er : ∀ w, evalMat w r = R w := fun w => by ext i j; rw [evalMat_apply]
  have ek : ∀ w, evalMat w k = K w := fun w => by ext i j; rw [evalMat_apply]
  have hbr : b * r = 1 := matrix_ext_eval fun w => by rw [map_mul, eb, er, hBR w, map_one]
  have hrb : r * b = 1 := matrix_ext_eval fun w => by rw [map_mul, eb, er, hRB w, map_one]
  have hk1 : k * star k = 1 := matrix_ext_eval fun w => by
    rw [map_mul, Matrix.star_eq_conjTranspose, evalMat_conjTranspose, ek, hKK w, map_one]
  have hk2 : star k * k = 1 := matrix_ext_eval fun w => by
    rw [map_mul, Matrix.star_eq_conjTranspose, evalMat_conjTranspose, ek, hKK' w, map_one]
  refine ⟨⟨b, r, hbr, hrb⟩, ⟨k, Unitary.mem_iff.mpr ⟨hk2, hk1⟩⟩, ?_, ?_⟩
  · intro i j hij
    funext w
    exact hB w hij
  · apply Units.ext
    apply matrix_ext_eval
    intro w
    rw [Units.val_mul]
    show evalMat w (y : Matrix (Fin n) (Fin n) (ι → ℂ)) = evalMat w (b * k)
    rw [map_mul, eb, ek]
    exact hY w
end GlobalTheory.CompanionTheory.Iwasawa
