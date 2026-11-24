-- Prove2me | solution 1 for GlobalTheory.AdLat.Tower.exists_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:23:11.61388+00:00
-- url     : https://prove2.me/submissions/ce28c4c6-969f-46d6-b56c-a72c2d2c4a6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLinearApproxTower
import Theorems.Thm_GlobalTheory_AdLat_Tower_fv_nsmul
import Theorems.Thm_GlobalTheory_AdLat_Tower_nsmul_cancel
import Theorems.Thm_GlobalTheory_AdLat_Translate_fv_nsmul
import Theorems.Thm_GlobalTheory_AdLat_Translate_nsmul_cancel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Tower
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.AdLat.Tower
theorem _root_.solution {M : Submodule (𝓞 E) (Fin n → E)}
    (hM : ∀ v, fv F v ∈ hat F (M : Set (Fin n → E)) ↔ v ∈ M) {N : ℕ} (hN : 0 < N)
    (x : M) {u : Fin n → RA F E} (hu : u ∈ hat F (M : Set (Fin n → E)))
    (h : fv F (x : Fin n → E) = N • u) : ∃ v : M, x = N • v := by
  have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 : N • ((N : E)⁻¹ • (x : Fin n → E)) = x := by
    rw [← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hN', one_smul]
  have h2 : fv F ((N : E)⁻¹ • (x : Fin n → E)) = u := by
    apply nsmul_cancel hN
    rw [← fv_nsmul, h1, h]
  refine ⟨⟨_, (hM _).1 (h2 ▸ hu)⟩, Subtype.ext ?_⟩
  exact h1.symm
end GlobalTheory.AdLat.Tower
