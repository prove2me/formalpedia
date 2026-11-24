-- Prove2me | solution 1 for GlobalTheory.QuantumMinorAdjacentSwap.two_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:47:45.316514+00:00
-- url     : https://prove2.me/submissions/d9874308-85dc-4782-a322-597e1c9a0048

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_QminorSwapAdjacent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.QuantumMinorAdjacentSwap
variable {A : Type} [Ring A] [Algebra ℂ A]
open Formalism.REAL
namespace GlobalTheory.QuantumMinorAdjacentSwap
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (y : ℂ) (a b c d : Fin n) :
    Tm E (y + 1) a d * Tm E y c b + Tm E (y + 1) a b * Tm E y c d =
      Tm E (y + 1) c d * Tm E y a b + Tm E (y + 1) c b * Tm E y a d := by
  have h1 := hE a b c d
  have h2 := hE a d c b
  have key : ∀ (x : ℂ) (p q : Fin n), Tm E x p q = (if p = q then x else 0) • (1 : A) + E p q := by
    intro x p q
    unfold Tm
    split_ifs <;> simp [Algebra.algebraMap_eq_smul_one]
  have h1' : E a b * E c d = E c d * E a b + (if c = b then (1 : ℂ) else 0) • E a d
      - (if a = d then (1 : ℂ) else 0) • E c b := by
    rw [sub_eq_iff_eq_add'] at h1
    rw [h1, add_sub_assoc]
    congr 2
    · by_cases h : b = c
      · simp [h]
      · simp [h, Ne.symm h]
    · by_cases h : d = a
      · simp [h]
      · simp [h, Ne.symm h]
  have h2' : E a d * E c b = E c b * E a d + (if c = d then (1 : ℂ) else 0) • E a b
      - (if a = b then (1 : ℂ) else 0) • E c d := by
    rw [sub_eq_iff_eq_add'] at h2
    rw [h2, add_sub_assoc]
    congr 2
    · by_cases h : d = c
      · simp [h]
      · simp [h, Ne.symm h]
    · by_cases h : b = a
      · simp [h]
      · simp [h, Ne.symm h]
  have k2 : ∀ (x : ℂ) (p q : Fin n), (if p = q then x else 0) = x * (if p = q then 1 else 0) := by
    intro x p q
    split_ifs <;> simp
  simp only [key]
  rw [k2 (y + 1) a d, k2 (y + 1) a b, k2 (y + 1) c d, k2 (y + 1) c b, k2 y a d, k2 y a b,
    k2 y c d, k2 y c b]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, h1', h2']
  module
end GlobalTheory.QuantumMinorAdjacentSwap
