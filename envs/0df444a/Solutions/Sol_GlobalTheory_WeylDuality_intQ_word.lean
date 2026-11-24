-- Prove2me | solution 1 for GlobalTheory.WeylDuality.intQ_word
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:28.414194+00:00
-- url     : https://prove2.me/submissions/8c2f6eb5-c4c1-4744-bcea-59c5c0bf521c

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ApplyWordMemDualWeyl
import Theorems.Thm_GlobalTheory_WeylDuality_intQ_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


section
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
namespace GlobalTheory.WeylDuality
private theorem rowGen_map_intCast {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) :
    Polynomial.map (MvPolynomial.map φ) (rowGen R a b f) = rowGen S a b (map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [rowGen]
  | add p q hp hq => rw [map_add, map_add, Polynomial.map_add, hp, hq, map_add]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.map_mul, hp, map_mul, map_mul, map_X]
    congr 1
    simp only [rowGen, aeval_X]
    split_ifs <;> simp
private theorem rowDiv_map_intCast {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (rowDiv R a b k f) = rowDiv S a b k (map φ f) := by
  unfold rowDiv
  rw [← rowGen_map_intCast, Polynomial.coeff_map]
private theorem map_intCast_applyWord {r n : ℕ} (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) ℤ) :
    map (Int.castRingHom ℚ) (applyWord ℤ w f) = applyWord ℚ w (map (Int.castRingHom ℚ) f) := by
  induction w with
  | nil => simp [applyWord]
  | cons x w ih =>
    simp only [applyWord, List.foldr_cons] at ih ⊢
    rw [rowDiv_map_intCast, ih]
private theorem map_intCast_hw {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    map (Int.castRingHom ℚ) (hw ℤ hn ν) = hw ℚ hn ν := by
  unfold hw lpMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, RingHom.map_det]
  congr 2
  ext p q
  simp
end GlobalTheory.WeylDuality
end
end

set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.WeylDuality
namespace GlobalTheory.WeylDuality
theorem _root_.solution {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (w : List (Fin r × Fin r × ℕ)) :
    intQ r n (applyWord ℤ w (hw ℤ hn ν)) = applyWord ℚ w (hw ℚ hn ν) := by
  rw [intQ_apply, map_intCast_applyWord, map_intCast_hw]
end GlobalTheory.WeylDuality
