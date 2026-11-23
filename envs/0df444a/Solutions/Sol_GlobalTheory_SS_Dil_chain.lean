-- Prove2me | solution 1 for GlobalTheory.SS.Dil.chain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:45.082802+00:00
-- url     : https://prove2.me/submissions/087d981a-4d8a-4267-bb46-46552c2c25b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Dil
namespace GlobalTheory.SS.Dil
theorem _root_.solution {R S W : Type} {n : ℕ} [CommRing R] [CommRing S] [AddCommGroup W] [Module S W]
    (σ : MvPolynomial (Fin n) R →+* S) (D : MvPolynomial (Fin n) R → W) (ha : ∀ x y, D (x + y) = D x + D y)
    (hm : ∀ x y, D (x * y) = σ x • D y + σ y • D x) (hr : ∀ r, D (C r) = 0) (p : MvPolynomial (Fin n) R) :
    D p = ∑ i, σ (pderiv i p) • D (X i) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [hr]
  | add p q hp hq => simp [ha, hp, hq, add_smul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    rw [hm, hp]
    have : ∀ i, σ (pderiv i (p * X j)) • D (X i) =
        (if i = j then σ p • D (X j) else 0) + σ (X j) • σ (pderiv i p) • D (X i) := by
      intro i
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, add_smul, mul_smul, mul_smul]
      by_cases h : i = j
      · subst h; simp
      · rw [pderiv_X_of_ne (Ne.symm h)]; simp [h]
    simp only [this, Finset.sum_add_distrib, Finset.smul_sum]
    simp
end GlobalTheory.SS.Dil
