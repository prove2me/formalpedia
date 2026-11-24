-- Prove2me | solution 1 for GlobalTheory.AdelicMatLat.span_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:04:29.904637+00:00
-- url     : https://prove2.me/submissions/f556433b-ea6d-4f06-9a88-3fcfee2ab31a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsLatticeAdelicMatrixIntegralTranslate
import Theorems.Thm_GlobalTheory_AdelicMatLat_exists_nat_mul_mem_family
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
open scoped Matrix
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.AdelicMatLat
variable (E : Type) [Field E] [NumberField E]
variable {E} {n : ℕ}
namespace GlobalTheory.AdelicMatLat
theorem _root_.solution (β : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    Submodule.span E (lat β : Set (Fin n → E)) = ⊤ := by
  classical
  obtain ⟨d, hd, h⟩ := exists_nat_mul_mem_family E (fun p : Fin n × Fin n => β p.1 p.2)
  rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have hm : (Pi.single i (d : E) : Fin n → E) ∈ lat β := by
    intro j
    rw [Finset.sum_eq_single i (by intro k _ hk; simp [Pi.single_eq_of_ne hk]) (by simp)]
    simpa using h (i, j)
  have hd' : (d : E) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have he : Pi.basisFun E (Fin n) i = (d : E)⁻¹ • (Pi.single i (d : E) : Fin n → E) := by
    rw [Pi.basisFun_apply, ← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hd']
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)
end GlobalTheory.AdelicMatLat
