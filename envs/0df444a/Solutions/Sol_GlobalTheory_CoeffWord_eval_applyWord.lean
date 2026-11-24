-- Prove2me | solution 1 for GlobalTheory.CoeffWord.eval_applyWord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:49:49.743847+00:00
-- url     : https://prove2.me/submissions/138461d1-359c-4247-a748-77b23644fff8

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UnitriMonomialOfLowerTri
import Theorems.Thm_GlobalTheory_CoeffWord_coeff_single
import Theorems.Thm_GlobalTheory_CoeffWord_map_rowGen
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.CoeffWord
variable {R : Type} [CommRing R] {r n : ℕ}
namespace GlobalTheory.CoeffWord
theorem _root_.solution (e : Fin r × Fin n →₀ ℕ) (L : List (Fin r × Fin n))
    (h1 : ∀ q ∈ L, q.2.val < q.1.val) (h2 : L.Pairwise fun q p => q ≠ p ∧ p.2.val ≤ q.2.val)
    (F : MvPolynomial (Fin r × Fin n) R) :
    eval (idFrame R r n) (applyWord R (L.map (letter e)) F) =
      coeff (e.filter (· ∈ L)) (unitri R L F) := by
  induction L using List.reverseRecOn generalizing F with
  | nil =>
    have h : (eval (idFrame R r n)) = constantCoeff.comp (unitri R ([] : List (Fin r × Fin n))).toRingHom := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun v => ?_)
      · simp [unitri]
      · simp only [unitri, idFrame, eval_X, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
        split_ifs <;> simp_all
    have h' : e.filter (· ∈ ([] : List (Fin r × Fin n))) = 0 := by
      ext v; simp
    rw [h', h]
    rfl
  | append_singleton L p ih =>
    rw [List.pairwise_append] at h2
    obtain ⟨h2, -, h3⟩ := h2
    have hp := h1 p (by simp)
    have hpr : p.2.val < r := lt_trans hp p.1.2
    have hL1 : ∀ q ∈ L, q.2.val < q.1.val := fun q hq => h1 q (by simp [hq])
    have hpL : p ∉ L := fun h => (h3 p h p (by simp)).1 rfl
    have hw : applyWord R ((L ++ [p]).map (letter e)) F =
        applyWord R (L.map (letter e)) (rowDiv R ⟨p.2.val, hpr⟩ p.1 (e p) F) := by
      simp [applyWord, letter, hpr]
    rw [hw, ih hL1 h2]
    have hm := map_rowGen (R := R) L p ⟨p.2.val, hpr⟩ rfl hp hpL
      (fun q hq => ⟨hL1 q hq, (h3 q hq p (by simp)).2⟩) F
    have hc := congrArg (fun P => Polynomial.coeff P (e p)) hm
    simp only [Polynomial.coeff_map] at hc
    have hc' : unitri R L (rowDiv R ⟨p.2.val, hpr⟩ p.1 (e p) F) =
        (single R p (unitri R (L ++ [p]) F)).coeff (e p) := hc
    rw [hc', coeff_single _ _ (by simp [Finsupp.filter_apply, hpL])]
    congr 1
    ext v
    by_cases hv : v = p
    · subst hv; simp [Finsupp.filter_apply, hpL]
    · simp [Finsupp.filter_apply, hv, Finsupp.single_apply, Ne.symm hv]
end GlobalTheory.CoeffWord
