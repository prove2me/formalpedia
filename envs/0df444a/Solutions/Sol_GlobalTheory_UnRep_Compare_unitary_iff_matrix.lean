-- Prove2me | solution 1 for GlobalTheory.UnRep.Compare.unitary_iff_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:22:09.322124+00:00
-- url     : https://prove2.me/submissions/85d2e0d0-a1f2-4370-931e-176b03d4d984

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSplitPlaceOfSplitPl
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
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ} (s : R →+* R) (G g : Matrix (Fin n) (Fin n) R) :
    (∀ x y : Fin n → R, ∑ a, ∑ b, (g *ᵥ x) a * G a b * s ((g *ᵥ y) b) = ∑ a, ∑ b, x a * G a b * s (y b)) ↔
      gᵀ * G * g.map s = G := by
  have key : ∀ (M : Matrix (Fin n) (Fin n) R) (x y : Fin n → R),
      ∑ a, ∑ b, x a * M a b * s (y b) = x ⬝ᵥ (M *ᵥ fun b => s (y b)) := fun M x y => by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have e : ∀ x y : Fin n → R, ∑ a, ∑ b, (g *ᵥ x) a * G a b * s ((g *ᵥ y) b) =
      ∑ a, ∑ b, x a * (gᵀ * G * g.map s) a b * s (y b) := fun x y => by
    have e : (fun b => s ((g *ᵥ y) b)) = g.map s *ᵥ fun b => s (y b) := by
      funext b
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
    rw [key, key, e, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec,
      ← Matrix.dotProduct_mulVec, mul_assoc]
  constructor
  · intro h
    ext a b
    have := (e (Pi.single a 1) (Pi.single b 1)).symm.trans (h _ _)
    simpa [Pi.single_apply, apply_ite s] using this
  · intro h x y
    rw [e, h]
end GlobalTheory.UnRep.Compare
