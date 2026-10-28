-- Prove2me | solution 1 for OAI.CriticalStrip.HoneycombBranch.physical_stepped_flux
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T02:33:57.87125+00:00
-- url     : https://prove2.me/submissions/1084f246-790b-4024-b336-2b87a647ea5e

import Mathlib
import Definitions.Def_CriticalStripMass
import Definitions.Def_OAIQ042S015
import Theorems.Thm_OAI_CriticalStrip_Diagram_deformationAngles_scalar_ne_zero
import Theorems.Thm_OAI_CriticalStrip_Diagram_physical_augmented_stationary
import Theorems.Thm_OAI_CriticalStrip_Diagram_reversed_augmented_stationary
import Theorems.Thm_OAI_CriticalStrip_HoneycombBranch_finite_split
import Theorems.Thm_OAI_CriticalStrip_HoneycombBranch_step_turn

section
-- module Solutions.OAIQ042_SS.StripMass_TopPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open Finset


theorem physicalWeights_zero : physicalWeights 0 = identityWeights := by
  have hs₂ := ne_of_gt inlinePrivate0_sin_two_lambda_pos
  have hs₃ := ne_of_gt inlinePrivate0_sin_three_lambda_pos
  have hd := inlinePrivate0_sin_two_lambda
  unfold physicalWeights identityWeights L
  simp only [add_zero, sub_zero, Real.sin_zero, mul_zero, zero_mul, zero_div]
  congr 1
  · rw [← hd]; exact div_self (mul_ne_zero hs₂ hs₃)
  · rw [mul_comm]; exact div_self (mul_ne_zero hs₂ hs₃)

 
theorem physicalWeights_three_lambda : physicalWeights (3*lambda) = deletionWeights := by
  have hs₂ := ne_of_gt inlinePrivate0_sin_two_lambda_pos
  have hs₃ := ne_of_gt inlinePrivate0_sin_three_lambda_pos
  have h₅ : Real.sin (2*lambda+3*lambda) = Real.sin (3*lambda) := by
    have harg : 2*lambda+3*lambda = Real.pi-3*lambda := by unfold lambda; ring
    rw [harg, Real.sin_pi_sub]
  have h₆ : Real.sin (3*lambda+3*lambda) = Real.sin (2*lambda) := by
    have harg : 3*lambda+3*lambda = Real.pi-2*lambda := by unfold lambda; ring
    rw [harg, Real.sin_pi_sub]
  unfold physicalWeights deletionWeights L
  simp only [sub_self, Real.sin_zero, mul_zero, zero_mul, zero_div, h₅, h₆]
  congr 1
  · rw [← inlinePrivate0_sin_two_lambda, mul_comm]; exact div_self (mul_ne_zero hs₃ hs₂)
  · have harg : 3*lambda-lambda = 2*lambda := by ring
    rw [harg, mul_comm]; exact div_self (mul_ne_zero hs₃ hs₂)



end

end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NodalExchange
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section






open Finset
open scoped Classical



theorem rationalResidualPolynomial_degree {n : ℕ} (p : Pairing (n+1)) (k : ℕ)
    (hk : n < k) : (rationalResidualPolynomial n p).coeff k = 0 := by
  have hP := rationalNodalPolynomial_degree n
  have hT := lastTransform_degree (fun i => (spectralWeights n i).tile)
    (constF n d) (constF n c) (constF n C) (rationalNodalPolynomial n) hP
  obtain ⟨j, rfl⟩ : ∃ j, k = j+1 := ⟨k-1, by omega⟩
  by_cases hp : p.Occupied (Fin.last n)
  · rw [rationalResidualPolynomial, Polynomial.coeff_sub,
      hT p (j+1) (by simp only [hp, ite_true]; omega)]
    have h₀ := hP p j (by simp only [hp, ite_true]; omega)
    have h₁ := hP p (j+1) (by simp only [hp, ite_true]; omega)
    simp [add_mul, h₀, h₁]
  · have h₁ := hP p (j+1) (by simp only [hp, ite_false]; omega)
    by_cases he : j = n
    · subst j
      let q := p.restrict Fin.castSuccOrderEmb
      have hpad : q.padTop = p := Pairing.padTop_restrict p hp
      rw [← hpad, rationalResidualPolynomial, Polynomial.coeff_sub, lastTransform_leading _ _ _ _ _ hP q]
      have hlead : (fun p : Pairing n => (rationalNodalPolynomial n p.padTop).coeff n) =
          rationalVacuum n := funext rationalNodalPolynomial_leading
      rw [hlead, ← column_eq_raw, rationalVacuum_stationary]
      have hz : (rationalNodalPolynomial n q.padTop).coeff (n+1) = 0 := by simpa [hpad] using h₁
      simp [add_mul, rationalNodalPolynomial_leading, hz]
    · have h₀ := hP p j (by simp only [hp, ite_false]; omega)
      rw [rationalResidualPolynomial, Polynomial.coeff_sub,
        hT p (j+1) (by simp only [hp, ite_false]; omega)]
      simp [add_mul, h₀, h₁]



theorem rationalResidualPolynomial_factor {n : ℕ} (p : Pairing (n+1)) :
    rationalResidualPolynomial n p =
      Polynomial.C (rationalResidualCoefficient n p) * Lagrange.nodal univ deletionBeta := by
  apply Polynomial.eq_of_degree_sub_lt_of_eval_index_eq univ (deletionBeta_injective n).injOn
  · simp only [card_univ, Fintype.card_fin]
    apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
    intro k hk
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    by_cases he : k = n
    · subst k
      have hnod : (Lagrange.nodal univ (@deletionBeta n)).coeff n = 1 := by
        simpa only [Lagrange.natDegree_nodal, card_univ, Fintype.card_fin] using
          (Lagrange.nodal_monic (s := (univ : Finset (Fin n))) (v := @deletionBeta n)).coeff_natDegree
      simp [hnod, rationalResidualCoefficient]
    · rw [rationalResidualPolynomial_degree p k (by omega)]
      have hnod : (Lagrange.nodal univ (@deletionBeta n)).coeff k = 0 := by
        apply Polynomial.coeff_eq_zero_of_degree_lt
        simp only [Lagrange.degree_nodal, card_univ, Fintype.card_fin]
        exact_mod_cast (show n < k by omega)
      simp [hnod]
  · intro i _
    rw [rationalResidualPolynomial_at_node, Polynomial.eval_mul, Polynomial.eval_C,
      Lagrange.eval_nodal_at_node (mem_univ _), mul_zero]

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SpecializationPolynomial
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open Finset
open scoped Classical



theorem rationalInterpolationResidual_factor {n : ℕ} (p : Pairing (n+1)) :
    rationalInterpolationResidual n p =
      ((∏ i : Fin n, evalLaurent (rowDenominator i.castSucc)) / 2) *
      (if p.Occupied (Fin.last n) then torusSin (variableF (Fin.last n)) else 1) *
      liftSpectral n (rationalResidualCoefficient n p) *
      (Lagrange.nodal univ (@deletionBeta n)).eval₂ (liftSpectral n) (spectralA (Fin.last n)) := by
  rw [rationalInterpolationResidual_transfer]
  simp only [lastValue, rationalResidualPolynomial_factor, Polynomial.eval₂_mul,
    Polynomial.eval₂_C]
  split_ifs <;> ring

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NodalEmpty
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical



theorem vacuum_interpolation_stationary : ∀n p,rationalInterpolationResidual n p=0 := by
  intro n p
  have h: rationalInterpolant n=rationalVacuum (n+1) := funext (vacuumData n).interpolant
  simp only [rationalInterpolationResidual,h,rationalVacuum_stationary,sub_self,mul_zero]

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_VacuumDegree
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma polynomialVacuumVector_eval (n:ℕ) (p:Pairing n) :
    evalLaurent (polynomialVacuumVector n p)=rationalVacuum n p := by
  cases n with
  | zero =>rw [rationalVacuum_zero]; exact map_one _
  | succ n =>exact (vacuumData n).eval_P p

end




noncomputable section
open scoped BigOperators Classical



lemma horizontal_column_blocks {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Weights K) :
    (restrictedColumn (Fin.snoc w horizontalWeights)).submatrix (sourceTopSplit n) (sourceTopSplit n) =
      Matrix.fromBlocks (restrictedColumn w) 0 0 (sourceTransfer (fun i => (w i).tile)) := by
  ext q p
  have hw : (fun i => ((Fin.snoc w horizontalWeights : Fin (n+1) → Weights K) i).tile) =
      Fin.snoc (fun i => (w i).tile) (horizontalWeights : Weights K).tile := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i <;> simp
  change rawColumn _ _ _ = _
  rw [hw, rawColumn_last_factor]
  cases q with
  | inl q =>
    cases p with
    | inl p => simp [lastCoefficient_padTop, lastTile, Weights.tile,
        restrictedColumn, sourceTopSplit_inl, Pairing.nonemptyPadTop]; rfl
    | inr p => simp [Matrix.fromBlocks, lastTile, p.property, horizontalWeights, Weights.tile,
        Pairing.nonemptyPadTop]
  | inr q =>
    cases p with
    | inl p => simp [Matrix.fromBlocks, lastTile, q.property, horizontalWeights, Weights.tile,
        Pairing.nonemptyPadTop]
    | inr p => simp [Matrix.fromBlocks, lastTile, q.property, p.property, horizontalWeights,
        Weights.tile, sourceTransfer]

lemma det_horizontal_column {K : Type*} [CommRing K] {n : ℕ} (w : Fin n → Weights K) :
    (1 - restrictedColumn (Fin.snoc w horizontalWeights)).det =
      (1 - restrictedColumn w).det * (1 - sourceTransfer (fun i => (w i).tile)).det := by
  rw [← Matrix.det_submatrix_equiv_self (sourceTopSplit n)]
  simp only [Matrix.submatrix_sub, Pi.sub_apply, Matrix.submatrix_one_equiv, horizontal_column_blocks]
  have h : 1 - Matrix.fromBlocks (restrictedColumn w) 0 0 (sourceTransfer (fun i => (w i).tile)) =
      Matrix.fromBlocks (1 - restrictedColumn w) 0 0
        (1 - sourceTransfer (fun i => (w i).tile)) := by
    ext q p
    cases q <;> cases p <;> simp [Matrix.fromBlocks, Matrix.one_apply]
  rw [h, Matrix.det_fromBlocks_zero₂₁]

lemma sourceTransfer_regular_of_horizontal {K : Type*} [Field K] {n : ℕ}
    (w : Fin n → Weights K) (h : VacuumRegular (Fin.snoc w horizontalWeights)) :
    (1 - sourceTransfer (fun i => (w i).tile)).det ≠ 0 := by
  unfold VacuumRegular at h
  rw [det_horizontal_column] at h
  exact (mul_ne_zero_iff.mp h).2

lemma horizontal_spectral_regular (n : ℕ) :
    VacuumRegular (Fin.snoc (spectralWeights n) horizontalWeights) := by
  apply regular_of_cleared_specialization
    (algebraMap (SpectralRing n) (SpectralField n)) (IsFractionRing.injective _ _)
    (flatEval n).toRingHom (Fin.snoc rowDenominator 1)
    (Fin.snoc rowNumerator (horizontalWeights : Weights (SpectralRing n)).tile)
    (Fin.snoc (spectralWeights n) horizontalWeights)
    (Fin.snoc (fun _ => deletionWeights) horizontalWeights)
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp
    · simpa using flatEval_rowDenominator_ne_zero i
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro t; cases t <;> simp [horizontalWeights, Weights.tile]
    · intro t; simpa using rowNumerator_map i t
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro t; cases t <;> simp [horizontalWeights, Weights.tile]
    · intro t; simpa using rowNumerator_flatEval i t
  · unfold VacuumRegular
    rw [det_one_nonflat]
    · exact one_ne_zero
    · intro i j hi hj
      have hh : ∀ k : Fin (n+1),
          ¬((Fin.snoc (fun _ : Fin n => (deletionWeights : Weights ℂ)) horizontalWeights : Fin (n+1) → Weights ℂ) k).IsFlat →
          k = Fin.last n := by
        intro k
        refine Fin.lastCases ?_ (fun k => ?_) k
        · intro _; rfl
        · intro hk; exact (hk (Or.inr (by simp))).elim
      exact (hh i hi).trans (hh j hj).symm

 

lemma spectral_source_regular (n : ℕ) :
    (1 - sourceTransfer (fun i => (spectralWeights n i).tile)).det ≠ 0 :=
  sourceTransfer_regular_of_horizontal _ (horizontal_spectral_regular n)

lemma rationalResidualCoefficient_zero (n : ℕ) (p : Pairing (n+1)) :
    rationalResidualCoefficient n p = 0 := by
  have h := rationalInterpolationResidual_factor p
  rw [vacuum_interpolation_stationary] at h
  have hden : (∏ i : Fin n, evalLaurent (rowDenominator i.castSucc)) / 2 ≠ 0 :=
    div_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => rowDenominator_map_ne_zero i.castSucc))
      (by norm_num)
  have hs : (if p.Occupied (Fin.last n) then torusSin (variableF (Fin.last n)) else 1) ≠ 0 := by
    split_ifs
    · exact torusSin_monomial_ne_zero _ (by
        intro hh
        have hh' := congrFun hh (Fin.last n)
        simp [variableExponent] at hh') 1 one_ne_zero
    · exact one_ne_zero
  have hnod : (Lagrange.nodal Finset.univ (@deletionBeta n)).eval₂
      (liftSpectral n) (spectralA (Fin.last n)) ≠ 0 := by
    simp only [Lagrange.nodal, Polynomial.eval₂_finsetProd, Polynomial.eval₂_sub,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    have hi : liftSpectral n (deletionBeta i) = deletionBeta i.castSucc := by
      simp [deletionBeta, deletionNode, map_div₀]
    rw [hi]
    exact sub_ne_zero.mpr (spectralA_ne_beta i.castSucc (Fin.last n))
  have hh : liftSpectral n (rationalResidualCoefficient n p) = 0 := by
    rcases mul_eq_zero.mp h.symm with h | h
    · exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hden hs)
    · exact (hnod h).elim
  exact (liftSpectral n).injective (by simpa using hh)

 

lemma rationalResidualPolynomial_zero (n : ℕ) (p : Pairing (n+1)) :
    rationalResidualPolynomial n p = 0 := by
  rw [rationalResidualPolynomial_factor, rationalResidualCoefficient_zero]
  simp



lemma lastTransform_source_leading {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (d c C : K) (P : Pairing (n+1) → Polynomial K)
    (hP : LastDegree n P) (hn : 1 ≤ n) (q : SourcePairing n) :
    (lastTransform w d c C P q.val).coeff n =
      (sourceTransfer w).mulVec (fun p => (P p.val).coeff (n-1)) q +
        (2*d) * (northSource w).mulVec (fun p => (P p.padTop).coeff n) q := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [lastTransform_coeff_succ, ← (pairingTopSplit (k+1)).sum_comp]
  simp only [Fintype.sum_sum_type, pairingTopSplit_inl, pairingTopSplit_inr,
    q.property, Pairing.padTop_not_occupied_last, ite_true, ite_false]
  have hzero (p : SourcePairing (k+1)) : (P p.val).coeff (k+1) = 0 :=
    hP p.val (k+1) (by simp [p.property])
  simp only [hzero, mul_zero, sub_zero, sourceTransfer,
    northSource, Matrix.mulVec, dotProduct, Finset.mul_sum]
  simp only [SourcePairing.occupied, ite_true, Nat.succ_sub_one]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  ring


lemma northNumerator_equation (n : ℕ) :
    (1 - sourceTransfer (fun i => (spectralWeights n i).tile)).mulVec (northNumerator n) =
      (2*constF n d) • (northSource (fun i => (spectralWeights n i).tile)).mulVec (rationalVacuum n) := by
  classical
  by_cases hn : 1 ≤ n
  · have hs (q : SourcePairing n) := congrArg (fun p : Polynomial (SpectralField n) => p.coeff n)
      (sub_eq_zero.mp (rationalResidualPolynomial_zero n q.val))
    funext q
    have hz (k : ℕ) (hk : n ≤ k) : (rationalNodalPolynomial n q.val).coeff k = 0 :=
      rationalNodalPolynomial_degree n q.val k (by simpa [q.property] using hk)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hh := hs q
    change (lastTransform _ _ _ _ _ q.val).coeff (k+1) =
      ((Polynomial.X + Polynomial.C _) * rationalNodalPolynomial (k+1) q.val).coeff (k+1) at hh
    rw [lastTransform_source_leading _ _ _ _ _ (rationalNodalPolynomial_degree _) (by omega)] at hh
    simp only [rationalNodalPolynomial_leading, add_mul, Polynomial.coeff_add,
      Polynomial.coeff_X_mul, Polynomial.coeff_C_mul, hz (k+1) (by omega), mul_zero, add_zero] at hh
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      northNumerator]
    change (rationalNodalPolynomial (k+1) q.val).coeff k -
      (sourceTransfer (fun i => (spectralWeights (k+1) i).tile)).mulVec
        (fun p => (rationalNodalPolynomial (k+1) p.val).coeff k) q = _
    simp only [Nat.add_sub_cancel] at hh
    linear_combination -hh
  · have hn : n = 0 := by omega
    subst n
    funext p
    exact (p.ne_empty (p.val.eq_empty_of_le_one (by omega))).elim



lemma northNumerator_eq_integrated (n : ℕ) :
    northNumerator n = (2*constF n d * spectralNormalization n) • integratedNorthSource n := by
  have h := congrArg (fun v =>
    (1 - sourceTransfer (fun i => (spectralWeights n i).tile))⁻¹.mulVec v)
      (northNumerator_equation n)
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (spectral_source_regular n)),
    Matrix.one_mulVec, Matrix.mulVec_smul] at h
  change _ = (2*constF n d) •
    (1 - sourceTransfer (fun i => (spectralWeights n i).tile))⁻¹.mulVec
      ((northSource (fun i => (spectralWeights n i).tile)).mulVec
        (spectralNormalization n • normalizedVacuum (spectralWeights n))) at h
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, smul_smul] at h
  exact h



lemma polynomialNorthSource_eval (n : ℕ) (p : SourcePairing n) :
    evalLaurent (polynomialNorthSource n p) =
      spectralNormalization n * integratedNorthSource n p := by
  have hd : constF n d ≠ 0 :=
    (map_ne_zero (algebraMap ℂ (SpectralField n))).mpr (by exact_mod_cast d_ne_zero)
  have ht := congrFun (northNumerator_eq_integrated n) p
  simp only [Pi.smul_apply, smul_eq_mul] at ht
  unfold polynomialNorthSource
  rw [show evalLaurent ((constantL n (1/(2*(d:ℂ)))) * ((vacuumData n).P p.val).coeff (n-1)) =
      evalLaurent (constantL n (1/(2*(d:ℂ)))) * evalLaurent (((vacuumData n).P p.val).coeff (n-1)) from
        (algebraMap (SpectralRing n) (SpectralField n)).map_mul _ _, show evalLaurent (constantL n (1/(2*(d:ℂ)))) = 1/(2*constF n d) by
    rw [evalLaurent, map_constantL]
    change (algebraMap ℂ (SpectralField n)) (1/(2*(d:ℂ))) = _
    rw [map_div₀, map_one, map_mul, map_ofNat]
    rfl]
  have hc : evalLaurent (((vacuumData n).P p.val).coeff (n-1)) = northNumerator n p := by
    rw [evalLaurent, ←Polynomial.coeff_map, (vacuumData n).map_P]
    rfl
  rw [hc, ht]
  field_simp



end




end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_VacuumClosure
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators

namespace Pairing

lemma GluesAt.symm {n : ℕ} {root : Fin n} {p q : Pairing n}
    (h : GluesAt root p q) : GluesAt root q p := by
  refine ⟨(h.2.1 root).mp h.1,fun i => (h.2.1 i).symm,?_⟩
  intro i j hij
  exact Relation.ReflTransGen.mono (r := p.join q) (p := q.join p) (fun _ _ hh => hh.symm) _ _ (h.2.2 i j hij.symm)

end Pairing

namespace Pairing


lemma gluesAt_comm {n : ℕ} (root : Fin n) (p q : Pairing n) :
    GluesAt root p q ↔ GluesAt root q p := ⟨GluesAt.symm,GluesAt.symm⟩

end Pairing



lemma glueMatrix_transpose {K : Type*} [Zero K] [One K] {n : ℕ} (root : Fin n) :
    (glueMatrix root : Matrix _ _ K).transpose = glueMatrix root := by
  ext p q
  simp only [Matrix.transpose_apply,glueMatrix,Pairing.gluesAt_comm root q p]



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NorthMerging
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators

lemma sourceBlock_transpose {K : Type*} {n m : ℕ}
    (M : Matrix (Pairing (m+1)) (Pairing (n+1)) K) :
    sourceBlock M.transpose = (sourceBlock M).transpose := rfl

lemma sourceGlue_symmetric {K : Type*} [CommRing K] (n : ℕ)
    (v w : SourcePairing n → K) : sourceGlue n v w = sourceGlue n w v := by
  unfold sourceGlue
  rw [Matrix.dotProduct_mulVec, ←glueMatrix_transpose (Fin.last n),
    sourceBlock_transpose,Matrix.vecMul_transpose, dotProduct_comm]
  rw [← sourceBlock_transpose, glueMatrix_transpose]

lemma sourceGlue_eq_sum {K : Type*} [CommRing K] (n : ℕ)
    (v w : SourcePairing n → K) :
    sourceGlue n v w = ∑ p, ∑ q,
      v p * ((if Pairing.GluesAt (Fin.last n) p.val q.val then (1:K) else 0) * w q) := by
  simp only [sourceGlue, dotProduct, Matrix.mulVec, Finset.mul_sum, sourceBlock, glueMatrix]

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ArchRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram




noncomputable section
open scoped Classical BigOperators



lemma map_scalarValue {K L : Type*} [CommRing K] [CommRing L]
    (g : K →+* L) (f : ℂ →+* K) {n : ℕ} (a : Fin n → K) :
    g (scalarValue f a) = scalarValue (g.comp f) (g ∘ a) := by
  exact MvPolynomial.map_eval₂Hom _ _ _ _

lemma rowCosineL_map {n : ℕ} (i : Fin n) : evalLaurent (rowCosineL i)=spectralA i := by
  rw [rowCosineL,cosineL_map _ _ (inv_ne_zero (pow_ne_zero _ phase_ne_zero)),map_monomialL_two_variable]
  simp only [constF,map_inv₀,map_pow]
  congr 1
  simp [constF,div_eq_mul_inv,mul_comm]

lemma rowCosineL_algebraMap {n : ℕ} (i : Fin n) :
    algebraMap (SpectralRing n) (SpectralField n) (rowCosineL i)=spectralA i := rowCosineL_map i

lemma evalLaurent_constant_comp (n : ℕ) :
    (algebraMap (SpectralRing n) (SpectralField n)).comp (constantL n) =
      algebraMap ℂ (SpectralField n) := by
  ext z
  exact map_constantL n z

lemma scalarValue_rowCosine (n : ℕ) :
    scalarValue (constantL n) rowCosineL = polynomialVacuumVector n (empty n) := by
  apply IsFractionRing.injective (SpectralRing n) (SpectralField n)
  rw [show algebraMap (SpectralRing n) (SpectralField n) _ = _ from
    map_scalarValue _ (constantL n) rowCosineL]
  simp only [evalLaurent_constant_comp,Function.comp_def,rowCosineL_algebraMap]
  change scalarValue _ spectralA = evalLaurent (polynomialVacuumVector n (empty n))
  rw [polynomialVacuumVector_eval,rationalVacuum_empty]
  exact scalarPolynomial_eval_spectral n

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ColumnSew
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.Pairing.join_symm _root_.OAI.CriticalStrip.Diagram.TriplePosition.mirrorWiring_symm _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical BigOperators

 

namespace ColumnChain
variable {n : ℕ}

lemma runs_unique {p q r : Pairing n} {ts : List (Configuration n)}
    (hq : Runs p ts q) (hr : Runs p ts r) : q=r :=
  (runs_sound p ts q hq).2.1.unique (runs_sound p ts r hr).2.1

end ColumnChain
end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PfaffianConfluentLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory


theorem archWeight_nonneg (N : ℕ) (k : ℤ) (p : List Triangle) :
    0 ≤ archWeight N k p := by
  classical
  unfold archWeight
  split_ifs
  · exact pow_nonneg rho_pos.le _
  · exact le_rfl

theorem bridgeWeight_nonneg (N : ℕ) (k : ℤ) (p : List Triangle) :
    0 ≤ bridgeWeight N k p := by
  classical
  unfold bridgeWeight
  split_ifs
  · exact pow_nonneg rho_pos.le _
  · exact le_rfl

theorem K_nonneg (N : ℕ) (k : ℤ) : 0 ≤ K N k :=
  tsum_nonneg (archWeight_nonneg N k)


end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_HeightOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators


theorem rho_sq_lt_one : rho ^ 2 < 1 := by
  have hs : (1 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
    exact (Real.sqrt_one ▸ Real.sqrt_lt_sqrt (by norm_num) (by nlinarith [Real.sqrt_nonneg 2]))
  have hp : 0 < Real.sqrt (2 + Real.sqrt 2) := lt_trans zero_lt_one hs
  have hr : rho < 1 := (div_lt_one hp).2 hs
  nlinarith [rho_pos]

theorem mirrorTriangle_involutive : Function.Involutive mirrorTriangle := mirrorTriangle_mirrorTriangle

theorem mirrorTriangles_involutive : Function.Involutive (List.map mirrorTriangle) := by
  intro l
  simp [List.map_map, Function.comp_def]

 
theorem adjacent_mirror_iff (v w : Triangle) :
    adjacent (mirrorTriangle v) (mirrorTriangle w) ↔ adjacent v w := by
  rcases v with ⟨a, j, b⟩
  rcases w with ⟨a', j', b'⟩
  cases b <;> cases b' <;> simp [adjacent, upDownAdjacent, mirrorTriangle]
  all_goals omega

theorem IsPath.mirror {N : ℕ} {finish : Triangle} {p : List Triangle}
    (hp : IsPath N finish p) :
    IsPath N (mirrorTriangle finish) (p.map mirrorTriangle) := by
  refine ⟨?_, ?_, hp.2.2.1.map mirrorTriangle_involutive.injective, ?_, ?_⟩
  · rw [List.head?_map, hp.1]
    simp
  · rw [List.getLast?_map, hp.2.1]
    rfl
  · apply (List.isChain_map _).mpr
    apply hp.2.2.2.1.imp
    intro v w h
    exact (adjacent_mirror_iff v w).mpr h
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    exact hp.2.2.2.2 w hw

@[simp] theorem isPath_mirror_iff {N : ℕ} {finish : Triangle} {p : List Triangle} :
    IsPath N (mirrorTriangle finish) (p.map mirrorTriangle) ↔ IsPath N finish p := by
  refine ⟨fun h => ?_, IsPath.mirror⟩
  simpa [List.map_map, Function.comp_def] using h.mirror

theorem archWeight_mirror (N : ℕ) (k : ℤ) (p : List Triangle) :
    archWeight N (-k) (p.map mirrorTriangle) = archWeight N k p := by
  classical
  have he : up (-k) 0 = mirrorTriangle (up k 0) := by simp
  simp only [archWeight, neg_ne_zero, he, isPath_mirror_iff, List.length_map]



theorem K_reflection (N : ℕ) (k : ℤ) : K N (-k) = K N k := by
  let e := mirrorTriangles_involutive.toPerm _
  calc
    K N (-k) = ∑' p : List Triangle, archWeight N (-k) (p.map mirrorTriangle) :=
      (e.tsum_eq (archWeight N (-k))).symm
    _ = K N k := tsum_congr (archWeight_mirror N k)



theorem summable_K_of_moment {N : ℕ}
    (hM : Summable (fun n : ℕ => (n + 1 : ℝ) * K N (n + 1))) :
    Summable (K N) := by
  have hp : Summable (fun n : ℕ => K N ((n : ℤ) + 1)) := by
    apply Summable.of_nonneg_of_le (fun n => K_nonneg _ _) (fun n => ?_) hM
    have hn : (1 : ℝ) ≤ n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    exact (one_mul _).symm.le.trans (mul_le_mul_of_nonneg_right hn (K_nonneg _ _))
  have hm : HasSum (fun n : ℕ => K N (-((n : ℤ) + 1))) (∑' n : ℕ, K N ((n : ℤ) + 1)) := by
    simpa only [K_reflection] using hp.hasSum
  have hp0 : HasSum (fun n : ℕ => K N (n : ℤ)) (∑' n : ℕ, K N ((n : ℤ) + 1)) := by
    have h := (hasSum_nat_add_iff (f := fun n : ℕ => K N (n : ℤ)) 1).mp (by simpa using hp.hasSum)
    simpa using h
  exact (hp0.of_nat_of_neg_add_one hm).summable

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ScalarBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/




namespace CriticalStrip
noncomputable section
open scoped BigOperators Classical


lemma PathBetween.reverse {N : ℕ} {a b : Triangle} {p : List Triangle}
    (hp : PathBetween N a b p) : PathBetween N b a p.reverse := by
  refine ⟨by simpa using hp.2.1,by simpa using hp.1,(by simpa only [List.nodup_reverse] using hp.2.2.1),?_,?_⟩
  · exact List.isChain_reverse.mpr (hp.2.2.2.1.imp (fun _ _ h => adjacent_symmetric.symm _ _ h))
  · intro v hv
    exact hp.2.2.2.2 v (List.mem_reverse.mp hv)


lemma translateTriangle_injective (i : ℤ) : Function.Injective (translateTriangle i) := by
  intro v w h
  have := congrArg (translateTriangle (-i)) h
  simpa using this

lemma adjacent_translate_iff (i : ℤ) (v w : Triangle) :
    adjacent (translateTriangle i v) (translateTriangle i w) ↔ adjacent v w := by
  simp only [adjacent,upDownAdjacent,translateTriangle,add_assoc,add_left_cancel_iff]

lemma PathBetween.translate {N : ℕ} {a b : Triangle} {p : List Triangle}
    (hp : PathBetween N a b p) (i : ℤ) :
    PathBetween N (translateTriangle i a) (translateTriangle i b) (p.map (translateTriangle i)) := by
  refine ⟨?_,?_,hp.2.2.1.map (translateTriangle_injective i),?_,?_⟩
  · rw [List.head?_map,hp.1]; rfl
  · rw [List.getLast?_map,hp.2.1]; rfl
  · exact (List.isChain_map _).mpr (hp.2.2.2.1.imp (fun _ _ => (adjacent_translate_iff i _ _).mpr))
  · intro v hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
    exact hp.2.2.2.2 w hw

@[simp] lemma pathBetween_translate_iff (N : ℕ) (a b : Triangle) (p : List Triangle) (i : ℤ) :
    PathBetween N (translateTriangle i a) (translateTriangle i b) (p.map (translateTriangle i)) ↔
      PathBetween N a b p := by
  refine ⟨fun h => ?_,fun h => h.translate i⟩
  simpa [List.map_map,Function.comp_def] using h.translate (-i)

lemma betweenArchWeight_nonneg (N : ℕ) (i j : ℤ) (p : List Triangle) :
    0≤betweenArchWeight N i j p := by
  unfold betweenArchWeight
  split
  · exact (pow_pos rho_pos _).le
  · exact le_rfl

lemma betweenArchWeight_translate (N : ℕ) (i j : ℤ) (p : List Triangle) :
    betweenArchWeight N i j (p.map (translateTriangle i))=archWeight N (j-i) p := by
  have hi : up i 0=translateTriangle i (up 0 0) := by simp
  have hj : up j 0=translateTriangle i (up (j-i) 0) := by simp
  have hn : i≠j ↔ j-i≠0 := by omega
  simp only [betweenArchWeight,archWeight,hi,hj,pathBetween_translate_iff,
    pathBetween_source,hn,List.length_map]

 

theorem betweenArchKernel_eq (N : ℕ) (i j : ℤ) : betweenArchKernel N i j=K N (j-i) := by
  rw [betweenArchKernel,←(translatePaths i).tsum_eq]
  exact tsum_congr (betweenArchWeight_translate N i j)

lemma summable_betweenArchWeight_iff (N : ℕ) (i j : ℤ) :
    Summable (betweenArchWeight N i j) ↔ Summable (archWeight N (j-i)) := by
  rw [←(translatePaths i).summable_iff]
  exact summable_congr (betweenArchWeight_translate N i j)

lemma cutArchWeight_nonneg (N : ℕ) (x : (ℕ×ℕ)×List Triangle) : 0 ≤ cutArchWeight N x :=
  betweenArchWeight_nonneg _ _ _ _

lemma cutArchWeight_path_sum (N : ℕ) (x : ℕ×ℕ) :
    (∑' p,cutArchWeight N (x,p))=K N ((x.1+x.2:ℕ)+1) := by
  change betweenArchKernel N (-(x.1:ℤ)) ((x.2:ℤ)+1)=_
  rw [betweenArchKernel_eq]
  congr 1
  omega

 

lemma summable_add_diagonal_iff {f : ℕ→ℝ} (hf : ∀ n,0≤f n) :
    Summable (fun x : ℕ×ℕ => f (x.1+x.2)) ↔ Summable (fun n : ℕ => (n+1:ℝ)*f n) := by
  rw [←Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff]
  change Summable (fun x : Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n =>
    f (x.2.val.1+x.2.val.2)) ↔ _
  rw [summable_sigma_of_nonneg (fun x => hf _)]
  have hsum (n : ℕ) : (∑' x : Finset.HasAntidiagonal.antidiagonal n,
      f (x.val.1+x.val.2))=(n+1:ℝ)*f n := by
    have he (x : Finset.HasAntidiagonal.antidiagonal n) : x.val.1+x.val.2=n :=
      Finset.HasAntidiagonal.mem_antidiagonal.mp x.property
    simp only [he,tsum_const,Nat.card_eq_fintype_card,nsmul_eq_mul,Fintype.card_coe,Finset.Nat.card_antidiagonal,
      Nat.cast_add,Nat.cast_one]
  simp only [hsum]
  exact ⟨fun h => h.2,fun h => ⟨fun _ => (hasSum_fintype _).summable,h⟩⟩



theorem cutArchWeight_summable_iff (N : ℕ)
    (hK : ∀ k : ℤ,Summable (archWeight N k)) :
    Summable (cutArchWeight N) ↔ Summable (fun n : ℕ => (n+1:ℝ)*K N (n+1)) := by
  rw [summable_prod_of_nonneg (cutArchWeight_nonneg N)]
  have hi (x : ℕ×ℕ) : Summable (fun p => cutArchWeight N (x,p)) :=
    (summable_betweenArchWeight_iff N (-(x.1:ℤ)) ((x.2:ℤ)+1)).mpr (hK _)
  have he (x : ℕ×ℕ) : (∑' p, cutArchWeight N (x,p)) =
      (fun n : ℕ => K N (n+1)) (x.1+x.2) := cutArchWeight_path_sum N x
  have hh : Summable (fun x : ℕ×ℕ => ∑' p,cutArchWeight N (x,p)) ↔
      Summable (fun x : ℕ×ℕ => (fun n : ℕ => K N (n+1)) (x.1+x.2)) := summable_congr he
  exact ⟨fun h => (summable_add_diagonal_iff (fun n => K_nonneg N (n+1))).mp (hh.mp h.2),
    fun h => ⟨hi,hh.mpr ((summable_add_diagonal_iff (fun n => K_nonneg N (n+1))).mpr h)⟩⟩



end
 

 

noncomputable section
open scoped BigOperators Classical
open Filter Topology


lemma stepArchWeight_nonneg (N : ℕ) (s i j : ℤ) (p : List Triangle) :
    0 ≤ stepArchWeight N s i j p := by
  unfold stepArchWeight
  split
  · exact betweenArchWeight_nonneg _ _ _ _
  · exact le_rfl

lemma stepArchWeight_le (N : ℕ) (s i j : ℤ) (p : List Triangle) :
    stepArchWeight N s i j p ≤ betweenArchWeight (N+1) i j p := by
  unfold stepArchWeight
  split
  · exact le_rfl
  · exact betweenArchWeight_nonneg _ _ _ _

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_GraphPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/





namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators
open Diagram.PathGraph



namespace WireConfiguration
variable {N : ℕ} {finish : Triangle}


lemma support_eq (D : WireConfiguration N finish) (hf : finish ≠ up 0 0) :
    D.graph.support = {v | v ∈ D.path} := by
  ext v
  change (∃ w,D.graph.Adj v w) ↔ v ∈ D.path
  constructor
  · rintro ⟨w,hw⟩
    exact (consecutive_mem ((D.edges_iff hf v w).mp hw)).1
  · exact D.path_trace.used_of_mem D.graph.symm hf.symm

lemma support_finite (D : WireConfiguration N finish) (hf : finish ≠ up 0 0) :
    D.graph.support.Finite := by
  rw [D.support_eq hf]
  exact List.finite_toSet _

lemma support_ncard (D : WireConfiguration N finish) (hf : finish ≠ up 0 0) :
    D.graph.support.ncard = D.path.length := by
  rw [D.support_eq hf]
  have he : {v | v ∈ D.path} = (↑D.path.toFinset : Set Triangle) := by ext; simp
  rw [he,Set.ncard_coe_finset,List.toFinset_card_of_nodup D.path_trace.2.2.1]


lemma weight_eq (D : WireConfiguration N finish) (hf : finish ≠ up 0 0) :
    D.weight = rho ^ D.path.length := by rw [weight,D.support_ncard hf]

end WireConfiguration
end

 

 

noncomputable section
open scoped Classical BigOperators

namespace WireConfiguration

lemma summable_weight_iff (N : ℕ) (finish : Triangle) (hf : finish ≠ up 0 0) :
    Summable (weight (N := N) (finish := finish)) ↔
      Summable (fun p : List Triangle => if IsPath N finish p then rho ^ p.length else 0) := by
  have he := (equivPaths N finish hf).summable_iff
    (f := fun p : {p : List Triangle // IsPath N finish p} => rho ^ p.val.length)
  have hs := summable_subtype_iff_indicator
    (f := fun p : List Triangle => rho ^ p.length)
    (s := {p | IsPath N finish p})
  have hw : (fun p : {p : List Triangle // IsPath N finish p} => rho ^ p.val.length) ∘
      (equivPaths N finish hf) = weight := by
    funext D
    exact (D.weight_eq hf).symm
  rw [hw] at he
  exact he.trans hs

lemma tsum_weight (N : ℕ) (finish : Triangle) (hf : finish ≠ up 0 0) :
    ∑' D : WireConfiguration N finish, D.weight =
      ∑' p : List Triangle, if IsPath N finish p then rho ^ p.length else 0 := by
  calc
    _ = ∑' D : WireConfiguration N finish, rho ^ D.path.length :=
      tsum_congr (fun D => D.weight_eq hf)
    _ = ∑' p : {p : List Triangle // IsPath N finish p}, rho ^ p.val.length :=
      (equivPaths N finish hf).tsum_eq (fun p => rho ^ p.val.length)
    _ = _ := tsum_subtype {p | IsPath N finish p} (fun p => rho ^ p.length)

 

theorem arch_sum (N : ℕ) (k : ℤ) (hk : k ≠ 0) :
    K N k = ∑' D : WireConfiguration N (up k 0), D.weight := by
  have hf : up k 0 ≠ up 0 0 := by simpa [up] using hk
  rw [tsum_weight N (up k 0) hf]
  apply tsum_congr
  intro p
  simp [archWeight,hk]

theorem arch_summable (N : ℕ) (k : ℤ) (hk : k ≠ 0) :
    Summable (archWeight N k) ↔ Summable (weight (N := N) (finish := up k 0)) := by
  have hf : up k 0 ≠ up 0 0 := by simpa [up] using hk
  rw [show archWeight N k = (fun p => if IsPath N (up k 0) p then rho ^ p.length else 0) from
    funext (fun p => by simp [archWeight,hk])]
  exact (summable_weight_iff N (up k 0) hf).symm

end WireConfiguration
end





end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_RealEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped BigOperators Classical
open Finset

lemma anglePhase_add (u v : ℝ) : anglePhase (u+v)=anglePhase u*anglePhase v := by
  simp only [anglePhase,Complex.ofReal_add,add_mul,Complex.exp_add]
lemma anglePhase_neg (u : ℝ) : anglePhase (-u)=(anglePhase u)⁻¹ := by
  simp [anglePhase,Complex.exp_neg]
lemma anglePhase_sub (u v : ℝ) : anglePhase (u-v)=anglePhase u/anglePhase v := by
  simp only [sub_eq_add_neg,anglePhase_add,anglePhase_neg,div_eq_mul_inv]
lemma anglePhase_nat_mul (k : ℕ) (u : ℝ) : anglePhase ((k:ℝ)*u)=anglePhase u^k := by
  simp only [anglePhase,Complex.ofReal_mul,Complex.ofReal_natCast,←Complex.exp_nat_mul,mul_assoc]
lemma anglePhase_lambda : anglePhase lambda=phase := rfl
lemma anglePhase_sine (u : ℝ) : (anglePhase u-(anglePhase u)⁻¹)/(2*Complex.I)=(Real.sin u:ℂ) := by
  rw [anglePhase,Complex.ofReal_sin,Complex.sin,←Complex.exp_neg]
  field_simp
  simp [Complex.I_sq]
lemma anglePhase_cosine (u : ℝ) : (anglePhase u+(anglePhase u)⁻¹)/2=(Real.cos u:ℂ) := by
  rw [anglePhase,Complex.ofReal_cos,Complex.cos,←Complex.exp_neg]
  simp only [neg_mul]

lemma rationalAt_const_complex {n : ℕ} (φ : Laurent n →ₐ[ℂ] ℂ) (z : ℂ) :
    RationalAt φ.toRingHom (constF n z) z := by
  have hh:=RationalAt.algebraMap (φ:=φ.toRingHom) (F:=SpectralField n) (constantL n z)
  rw [map_constantL] at hh
  have he : φ (constantL n z)=z := φ.commutes z
  simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,he] using hh

lemma rationalAt_angle_variable {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    RationalAt (angleEvaluation u).toRingHom (variableF i) (anglePhase (u i)) := by
  have hh:=RationalAt.algebraMap (φ:=(angleEvaluation u).toRingHom) (F:=SpectralField n)
    (monomialL (variableExponent i) 1)
  change RationalAt (angleEvaluation u).toRingHom (variableF i)
    (angleEvaluation u (monomialL (variableExponent i) 1)) at hh
  simpa only [angleEvaluation_variable] using hh

lemma rationalAt_angle_sin {n : ℕ} (φ : Laurent n →ₐ[ℂ] ℂ) {x : SpectralField n} {u : ℝ}
    (h : RationalAt φ.toRingHom x (anglePhase u)) :
    RationalAt φ.toRingHom (torusSin x) (Real.sin u:ℂ) := by
  rw [←anglePhase_sine]
  exact (h.sub (h.inv (anglePhase_ne_zero _))).div
    ((RationalAt.natCast 2).mul (rationalAt_const_complex φ Complex.I))
    (mul_ne_zero (by norm_num) Complex.I_ne_zero)

lemma rationalAt_angle_cos {n : ℕ} (φ : Laurent n →ₐ[ℂ] ℂ) {x : SpectralField n} {u : ℝ}
    (h : RationalAt φ.toRingHom x (anglePhase u)) :
    RationalAt φ.toRingHom (torusCos x) (Real.cos u:ℂ) := by
  rw [←anglePhase_cosine]
  exact (h.add (h.inv (anglePhase_ne_zero _))).div (RationalAt.natCast 2) (by norm_num)

lemma rationalAt_angle_L {n : ℕ} (φ : Laurent n →ₐ[ℂ] ℂ) {x : SpectralField n} {u : ℝ}
    (h : RationalAt φ.toRingHom x (anglePhase u)) :
    RationalAt φ.toRingHom (torusL x) (L u:ℂ) := by
  have hq:=rationalAt_const_complex φ phase
  have hp (k : ℕ) : RationalAt φ.toRingHom (constF n phase^k*x) (anglePhase ((k:ℝ)*lambda+u)) := by
    simpa only [anglePhase_add,anglePhase_nat_mul,anglePhase_lambda] using (hq.pow k).mul h
  simpa only [torusL,L,Complex.ofReal_mul,Nat.cast_ofNat] using
    (rationalAt_angle_sin φ (hp 2)).mul (rationalAt_angle_sin φ (hp 3))

lemma rationalAt_angle_weights {n : ℕ} (φ : Laurent n →ₐ[ℂ] ℂ) {x : SpectralField n} {u : ℝ}
    (h : RationalAt φ.toRingHom x (anglePhase u)) (hL : L u≠0) (t : Tile) :
    RationalAt φ.toRingHom ((torusWeights x).tile t) ((physicalWeights u).tile t:ℂ) := by
  have hq:=rationalAt_const_complex φ phase
  have hd:=rationalAt_const_complex φ d
  have hs:=rationalAt_angle_sin φ h
  have hp (k : ℕ) : RationalAt φ.toRingHom (constF n phase^k/x) (anglePhase ((k:ℝ)*lambda-u)) := by
    simpa only [anglePhase_sub,anglePhase_nat_mul,anglePhase_lambda] using (hq.pow k).div h (anglePhase_ne_zero _)
  have ha: RationalAt φ.toRingHom (x/constF n phase) (anglePhase (u-lambda)) := by
    simpa only [anglePhase_sub,anglePhase_lambda] using h.div hq phase_ne_zero
  have ht:=rationalAt_angle_sin φ (hp 3)
  have hv:=rationalAt_angle_sin φ (hp 2)
  have hh:=rationalAt_angle_sin φ ha
  have hℓ:=rationalAt_angle_L φ h
  have hℓ₀ : (L u:ℂ)≠0 := by exact_mod_cast hL
  cases t
  · exact RationalAt.one
  · simpa [torusWeights,Weights.tile,physicalWeights,d] using (hd.mul ht).div hℓ hℓ₀
  · simpa [torusWeights,Weights.tile,physicalWeights,d] using (hd.mul ht).div hℓ hℓ₀
  · simpa [torusWeights,Weights.tile,physicalWeights,d] using (hs.mul ht).div hℓ hℓ₀
  · simpa [torusWeights,Weights.tile,physicalWeights,d] using (hs.mul ht).div hℓ hℓ₀
  · simpa [torusWeights,Weights.tile,physicalWeights,d] using (hd.mul hs).div hℓ hℓ₀
  · simpa [torusWeights,Weights.tile,physicalWeights,d] using (hd.mul hs).div hℓ hℓ₀
  · simpa [torusWeights,Weights.tile,physicalWeights,d] using (ht.mul hv).div hℓ hℓ₀
  · simpa [torusWeights,Weights.tile,physicalWeights,d] using (hh.mul hs).div hℓ hℓ₀

lemma rationalAt_angle_spectralA {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    RationalAt (angleEvaluation u).toRingHom (spectralA i) (Real.cos (2*u i-3*lambda):ℂ) := by
  apply rationalAt_angle_cos
  rw [anglePhase_sub,show anglePhase (2*u i)=anglePhase (u i)^2 from anglePhase_nat_mul 2 _,
    show anglePhase (3*lambda)=phase^3 from anglePhase_nat_mul 3 _]
  exact
    ((rationalAt_angle_variable u i).pow 2).div
      ((rationalAt_const_complex (angleEvaluation u) phase).pow 3) (pow_ne_zero _ phase_ne_zero)

lemma rationalAt_angle_spectralWeights {n : ℕ} (u : Fin n → ℝ)
    (hL : ∀i,L (3*lambda-u i)≠0) (i : Fin n) (t : Tile) :
    RationalAt (angleEvaluation u).toRingHom ((spectralWeights n i).tile t)
      ((physicalWeights (3*lambda-u i)).tile t:ℂ) := by
  apply rationalAt_angle_weights _ _ (hL i)
  rw [anglePhase_sub,show anglePhase (3*lambda)=phase^3 from anglePhase_nat_mul 3 _]
  exact ((rationalAt_const_complex (angleEvaluation u) phase).pow 3).div
      (rationalAt_angle_variable u i) (anglePhase_ne_zero _)

lemma angleEvaluation_rowCosine {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    angleEvaluation u (rowCosineL i)=(Real.cos (2*u i-3*lambda):ℂ) := by
  have hh:=RationalAt.algebraMap (φ:=(angleEvaluation u).toRingHom) (F:=SpectralField n) (rowCosineL i)
  rw [rowCosineL_algebraMap] at hh
  exact hh.unique (rationalAt_angle_spectralA u i)

lemma angleEvaluation_scalar {n : ℕ} (u : Fin n → ℝ) :
    angleEvaluation u (polynomialVacuumVector n (empty n))=
      scalarValue (RingHom.id ℂ) (fun i=>(Real.cos (2*u i-3*lambda):ℂ)) := by
  rw [←scalarValue_rowCosine]
  have hh:=map_scalarValue (angleEvaluation u).toRingHom (constantL n) rowCosineL
  have hc : (angleEvaluation u).toRingHom.comp (constantL n)=RingHom.id ℂ := by ext z; simp
  rw [hc] at hh
  have hf : (angleEvaluation u).toRingHom ∘ rowCosineL=fun i=>(Real.cos (2*u i-3*lambda):ℂ) := by
    funext i
    exact angleEvaluation_rowCosine u i
  rw [hf] at hh
  exact hh

lemma continuous_angleEvaluation {n : ℕ} (f : Laurent n) :
    Continuous (fun u : Fin n → ℝ=>angleEvaluation u f) := by
  induction f using AddMonoidAlgebra.induction_on with
  | of e =>
    change Continuous (fun u : Fin n → ℝ=>angleEvaluation u (monomialL e 1))
    simp only [angleEvaluation_monomial]
    apply continuous_const.mul
    apply continuous_finsetProd
    intro i _
    apply Continuous.zpow₀ _ _ (fun _=>Or.inl (anglePhase_ne_zero _))
    unfold anglePhase
    fun_prop
  | add f g hf hg =>
    simp only [map_add]
    exact hf.add hg
  | smul z f hf =>
    simp only [map_smul,smul_eq_mul]
    exact continuous_const.mul hf

end
end CriticalStrip.Diagram

 

 

 

namespace CriticalStrip.PositiveMatrix
noncomputable section
open Filter _root_.Matrix
open scoped BigOperators Topology Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma Nonnegative.pow {Q : Matrix ι ι ℝ} (hQ : Nonnegative Q) (k : ℕ) :
    Nonnegative (Q^k) := by
  induction k with
  | zero => intro i j; simp only [pow_zero,Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    intro i j
    rw [pow_succ]
    exact Finset.sum_nonneg fun a _ =>mul_nonneg (ih i a) (hQ a j)

omit [DecidableEq ι] in
lemma Nonnegative.mulVec {Q : Matrix ι ι ℝ} (hQ : Nonnegative Q)
    {z : ι → ℝ} (hz : ∀ i,0≤z i) : ∀ i, 0≤Q.mulVec z i :=
  fun _ =>Finset.sum_nonneg fun j _ =>mul_nonneg (hQ _ j) (hz j)

omit [DecidableEq ι] in
lemma Nonnegative.mulVec_mono {Q : Matrix ι ι ℝ} (hQ : Nonnegative Q)
    {x y : ι → ℝ} (hxy : ∀ i,x i≤y i) : ∀ i, Q.mulVec x i≤Q.mulVec y i :=
  fun _ =>Finset.sum_le_sum fun j _ =>mul_le_mul_of_nonneg_left (hxy j) (hQ _ j)

omit [DecidableEq ι] in
lemma entry_mul_le_mulVec {Q : Matrix ι ι ℝ} (hQ : Nonnegative Q)
    {z : ι → ℝ} (hz : ∀ i,0≤z i) (i j : ι) : Q i j*z j≤Q.mulVec z i :=
  Finset.single_le_sum (fun a _ =>mul_nonneg (hQ i a) (hz a)) (Finset.mem_univ j)

lemma stationary_partial_sum {Q : Matrix ι ι ℝ} {v w : ι → ℝ}
    (he : Q.mulVec w+v=w) (k : ℕ) :
    (∑ m∈Finset.range k, (Q^m).mulVec v)+(Q^k).mulVec w=w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ,pow_succ,←Matrix.mulVec_mulVec,add_assoc,
      ←Matrix.mulVec_add,add_comm v (Q.mulVec w),he]
    exact ih

 
lemma summable_injection {Q : Matrix ι ι ℝ} {v w : ι → ℝ}
    (hQ : Nonnegative Q) (hv : ∀i,0≤v i) (hw : ∀i,0≤w i)
    (he : Q.mulVec w+v=w) (i : ι) : Summable (fun k : ℕ =>(Q^k).mulVec v i) := by
  apply summable_of_sum_range_le (fun k =>(hQ.pow k).mulVec hv i) (c:=w i)
  intro k
  have hh:=congrFun (stationary_partial_sum he k) i
  simp only [Pi.add_apply,Finset.sum_apply] at hh
  linarith [(hQ.pow k).mulVec hw i]

 

theorem summablePowers_of_stationary {Q : Matrix ι ι ℝ} {v w : ι → ℝ}
    (hQ : Nonnegative Q) (hv : ∀i,0≤v i) (hw : ∀i,0≤w i)
    (he : Q.mulVec w+v=w) (ha : Accessible Q v) : SummablePowers Q := by
  intro i j
  obtain ⟨m,hm⟩:=ha j
  have hs := (summable_nat_add_iff m).mpr (summable_injection hQ hv hw he i)
  apply (hs.div_const ((Q^m).mulVec v j)).of_nonneg_of_le (fun k =>hQ.pow k i j)
  intro k
  apply (le_div_iff₀ hm).mpr
  simpa only [pow_add,Matrix.mulVec_mulVec] using
    entry_mul_le_mulVec (hQ.pow k) ((hQ.pow m).mulVec hv) i j

lemma SummablePowers.tendsto_zero {Q : Matrix ι ι ℝ} (hs : SummablePowers Q) (i j : ι) :
    Tendsto (fun k : ℕ =>(Q^k) i j) atTop (𝓝 0) := (hs i j).tendsto_atTop_zero

lemma SummablePowers.mulVec_tendsto_zero {Q : Matrix ι ι ℝ} (hs : SummablePowers Q)
    (w : ι → ℝ) (i : ι) : Tendsto (fun k : ℕ =>(Q^k).mulVec w i) atTop (𝓝 0) := by
  simpa only [Matrix.mulVec,dotProduct,zero_mul,Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun j _ =>(hs.tendsto_zero i j).mul_const (w j))

lemma SummablePowers.mulVec_summable {Q : Matrix ι ι ℝ} (hs : SummablePowers Q)
    (v : ι → ℝ) (i : ι) : Summable (fun k : ℕ =>(Q^k).mulVec v i) :=
  summable_sum fun j _ =>(hs i j).mul_right (v j)

 

lemma SummablePowers.stationary_eq_tsum {Q : Matrix ι ι ℝ} (hs : SummablePowers Q)
    {v w : ι → ℝ} (he : Q.mulVec w+v=w) (i : ι) :
    w i=∑' k : ℕ,(Q^k).mulVec v i := by
  have hlim:=((hs.mulVec_summable v i).hasSum.tendsto_sum_nat).add (hs.mulVec_tendsto_zero w i)
  simp only [add_zero] at hlim
  have hc : Tendsto (fun k : ℕ =>(∑ m∈Finset.range k, (Q^m).mulVec v i)+(Q^k).mulVec w i)
      atTop (𝓝 (w i)) := by
    have hh : (fun k : ℕ =>(∑ m∈Finset.range k, (Q^m).mulVec v i)+(Q^k).mulVec w i)=fun _=>w i := by
      funext k
      simpa only [Pi.add_apply,Finset.sum_apply] using congrFun (stationary_partial_sum he k) i
    rw [hh]; exact tendsto_const_nhds
  exact tendsto_nhds_unique hc hlim

lemma SummablePowers.stationary_nonneg {Q : Matrix ι ι ℝ} (hs : SummablePowers Q)
    (hQ : Nonnegative Q) {v w : ι → ℝ} (hv : ∀i,0≤v i) (he : Q.mulVec w+v=w) :
    ∀ i,0≤w i := by
  intro i
  rw [hs.stationary_eq_tsum he i]
  exact tsum_nonneg fun k =>(hQ.pow k).mulVec hv i


lemma pow_mulVec_le {Q : Matrix ι ι ℝ} (hQ : Nonnegative Q) {z : ι → ℝ}
    {r : ℝ} (hr : 0 ≤ r) (hz : ∀i,Q.mulVec z i ≤ r*z i) (k : ℕ) :
    ∀ i,(Q^k).mulVec z i ≤ r^k*z i := by
  induction k with
  | zero => simp
  | succ k ih =>
    intro i
    rw [pow_succ',←Matrix.mulVec_mulVec,pow_succ']
    calc
      Q.mulVec ((Q^k).mulVec z) i≤Q.mulVec (fun j=>r^k*z j) i := hQ.mulVec_mono ih i
      _ = r^k*Q.mulVec z i := by
        simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ r^k*(r*z i) := mul_le_mul_of_nonneg_left (hz i) (pow_nonneg hr k)
      _ = _ := by ring

lemma summablePowers_of_le {Q : Matrix ι ι ℝ} (hQ : Nonnegative Q) {z : ι → ℝ}
    (hz : ∀i,0<z i) {r : ℝ} (hr : 0 ≤ r) (hr₁ : r<1)
    (he : ∀i,Q.mulVec z i ≤ r*z i) : SummablePowers Q := by
  intro i j
  have hs:=((summable_geometric_of_lt_one hr hr₁).mul_left (z i)).div_const (z j)
  apply hs.of_nonneg_of_le (fun k=>hQ.pow k i j)
  intro k
  apply (le_div_iff₀ (hz j)).mpr
  exact (entry_mul_le_mulVec (hQ.pow k) (fun i=>(hz i).le) i j).trans
    (by simpa only [mul_comm] using pow_mulVec_le hQ hr he k i)

lemma HasSupervector.summablePowers {Q : Matrix ι ι ℝ} (h : HasSupervector Q)
    (hQ : Nonnegative Q) : SummablePowers Q := by
  obtain ⟨z,hz,he⟩:=h
  classical
  cases isEmpty_or_nonempty ι with
  | inl hi => intro i; exact isEmptyElim i
  | inr hi =>
    let r := Finset.univ.sup' Finset.univ_nonempty (fun i=>Q.mulVec z i/z i)
    have hr₁ : r<1 := (Finset.sup'_lt_iff Finset.univ_nonempty).mpr (fun i _ =>(div_lt_one (hz i)).mpr (he i))
    have hr₀ : 0 ≤ r := by
      obtain ⟨i⟩:=hi
      exact (div_nonneg (hQ.mulVec (fun i=>(hz i).le) i) (hz i).le).trans
        (Finset.le_sup' (fun i=>Q.mulVec z i/z i) (Finset.mem_univ i))
    apply summablePowers_of_le hQ hz hr₀ hr₁
    intro i
    exact (div_le_iff₀ (hz i)).mp (Finset.le_sup' (fun i=>Q.mulVec z i/z i) (Finset.mem_univ i))

lemma SummablePowers.hasSupervector {Q : Matrix ι ι ℝ} (hs : SummablePowers Q)
    (hQ : Nonnegative Q) : HasSupervector Q := by
  let z : ι → ℝ:=fun i=>∑' k : ℕ,(Q^k).mulVec (fun _=>1) i
  have hz : ∀i,1≤z i := by
    intro i
    have hh:=Summable.le_tsum (hs.mulVec_summable (fun _=>1) i) 0
      (fun k _ =>(hQ.pow k).mulVec (fun _=>by norm_num) i)
    simpa only [pow_zero,Matrix.one_mulVec] using hh
  have he : ∀ i,Q.mulVec z i+1=z i := by
    intro i
    have hh := (hs.mulVec_summable (fun _=>1) i).tsum_eq_zero_add
    simp only [pow_zero,Matrix.one_mulVec] at hh
    suffices hQz : Q.mulVec z i=∑' k : ℕ,(Q^(k+1)).mulVec (fun _=>1) i by
      rw [hQz]; linarith
    change (∑ j, Q i j * ∑' k : ℕ,(Q^k).mulVec (fun _=>1) j) = _
    simp_rw [← tsum_mul_left]
    rw [← Summable.tsum_finsetSum (fun j _ =>(hs.mulVec_summable (fun _=>1) j).mul_left (Q i j))]
    congr 1
    funext k
    change Q.mulVec ((Q^k).mulVec (fun _=>1)) i=(Q^(k+1)).mulVec (fun _=>1) i
    rw [Matrix.mulVec_mulVec,pow_succ']
  refine ⟨z,fun i=>lt_of_lt_of_le (by norm_num) (hz i),?_⟩
  intro i
  linarith [he i]

lemma hasSupervector_iff {Q : Matrix ι ι ℝ} (hQ : Nonnegative Q) :
    HasSupervector Q ↔ SummablePowers Q := ⟨fun h=>h.summablePowers hQ,fun hs=>hs.hasSupervector hQ⟩

omit [DecidableEq ι] in
lemma isOpen_hasSupervector : IsOpen {Q : Matrix ι ι ℝ | HasSupervector Q} := by
  have he : {Q : Matrix ι ι ℝ | HasSupervector Q}=
      ⋃ z : ι → ℝ, ⋃ (_ : ∀i,0<z i), ⋂ i : ι, {Q : Matrix ι ι ℝ | Q.mulVec z i<z i} := by
    ext Q
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_iInter,HasSupervector,exists_prop]
  rw [he]
  apply isOpen_iUnion
  intro z
  apply isOpen_iUnion
  intro _
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt (by unfold Matrix.mulVec dotProduct; fun_prop) continuous_const

 

theorem summablePowers_of_connected_stationary
    {α : Type*} [TopologicalSpace α] [PreconnectedSpace α]
    (Q : α → Matrix ι ι ℝ) (v w : α → ι → ℝ) (a : α)
    (hQc : Continuous Q) (hwc : Continuous w)
    (hQ : ∀ t, Nonnegative (Q t)) (hv : ∀ t i, 0≤v t i)
    (he : ∀ t,(Q t).mulVec (w t)+v t=w t)
    (hs : SummablePowers (Q a)) (ha : ∀ t,t≠a → Accessible (Q t) (v t)) :
    ∀ t,SummablePowers (Q t) := by
  let S : Set α := {t | SummablePowers (Q t)}
  have hS : S={t | ∀ i,0≤w t i} := by
    ext t
    constructor
    · intro ht
      exact ht.stationary_nonneg (hQ t) (hv t) (he t)
    · intro ht
      by_cases ht' : t=a
      · simpa only [S,Set.mem_ofPred_eq,ht'] using hs
      · exact summablePowers_of_stationary (hQ t) (hv t) ht (he t) (ha t ht')
  have hc : IsClosed S := by
    rw [hS,show {t | ∀ i,0≤w t i}=⋂ i, {t | 0≤w t i} by ext; simp]
    exact isClosed_iInter fun i =>isClosed_le continuous_const ((continuous_apply i).comp hwc)
  have ho : IsOpen S := by
    have hh : S=Q ⁻¹' {M | HasSupervector M} := by
      ext t
      exact (hasSupervector_iff (hQ t)).symm
    rw [hh]
    exact isOpen_hasSupervector.preimage hQc
  have hu : S=Set.univ := (show IsClopen S from ⟨hc,ho⟩).eq_univ ⟨a,hs⟩
  intro t
  show t∈S
  rw [hu]
  trivial

 
theorem summablePowers_on_Icc
    (Q : ℝ → Matrix ι ι ℝ) (v w : ℝ → ι → ℝ) {a b : ℝ} (hab : a≤b)
    (hQc : ContinuousOn Q (Set.Icc a b)) (hwc : ContinuousOn w (Set.Icc a b))
    (hQ : ∀t∈Set.Icc a b,Nonnegative (Q t))
    (hv : ∀t∈Set.Icc a b,∀i,0≤v t i)
    (he : ∀t∈Set.Icc a b,(Q t).mulVec (w t)+v t=w t)
    (hs : SummablePowers (Q a))
    (ha : ∀t∈Set.Ioc a b,Accessible (Q t) (v t)) :
    ∀t∈Set.Icc a b,SummablePowers (Q t) := by
  let : PreconnectedSpace (Set.Icc a b) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hh:=summablePowers_of_connected_stationary
    (fun t : Set.Icc a b=>Q t.val) (fun t : Set.Icc a b=>v t.val)
    (fun t : Set.Icc a b=>w t.val) ⟨a,le_rfl,hab⟩
    hQc.domRestrict hwc.domRestrict (fun t=>hQ _ t.property) (fun t=>hv _ t.property)
    (fun t=>he _ t.property) hs (fun t ht=>ha _ ⟨lt_of_le_of_ne t.property.1
      (by intro hr; exact ht (Subtype.ext hr.symm)),t.property.2⟩)
  exact fun t ht=>hh ⟨t,ht⟩



end
end CriticalStrip.PositiveMatrix

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PhysicalStationarity
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped BigOperators Classical
open Finset _root_.Matrix


lemma rationalAt_angle_vacuum {n : ℕ} (u : Fin n → ℝ) (p : Pairing n) :
    RationalAt (angleEvaluation u).toRingHom (rationalVacuum n p)
      (angleEvaluation u (polynomialVacuumVector n p)) := by
  have h:=RationalAt.algebraMap (φ:=(angleEvaluation u).toRingHom) (F:=SpectralField n)
    (polynomialVacuumVector n p)
  rw [show algebraMap (Laurent n) (SpectralField n) (polynomialVacuumVector n p)=rationalVacuum n p from
    polynomialVacuumVector_eval n p] at h
  exact h

lemma rationalAt_angle_column {n : ℕ} (u : Fin n → ℝ)
    (hL : ∀i,L (3*lambda-u i)≠0) (p q : Pairing n) :
    RationalAt (angleEvaluation u).toRingHom (column (spectralWeights n) p q)
      (transfer u p q:ℂ) := by
  have hc:=rationalAt_column (spectralWeights n)
    (fun i=>(physicalWeights (3*lambda-u i)).map Complex.ofRealHom)
    (fun i t=>by simpa using rationalAt_angle_spectralWeights u hL i t) p q
  rw [←column_map] at hc
  exact hc

lemma angle_rawVacuum_stationary {n : ℕ} (u : Fin n → ℝ)
    (hL : ∀i,L (3*lambda-u i)≠0) :
    ((transfer u).map Complex.ofRealHom).mulVec (fun p=>angleEvaluation u (polynomialVacuumVector n p))=
      fun p=>angleEvaluation u (polynomialVacuumVector n p) := by
  funext p
  have hm:=RationalAt.mulVec (φ:=(angleEvaluation u).toRingHom)
    (column (spectralWeights n)) ((transfer u).map Complex.ofRealHom)
    (rationalVacuum n) (fun p=>angleEvaluation u (polynomialVacuumVector n p))
    (rationalAt_angle_column u hL) (rationalAt_angle_vacuum u) p
  rw [rationalVacuum_stationary] at hm
  exact hm.unique (rationalAt_angle_vacuum u p)

lemma angleVacuum_empty {n : ℕ} (u : Fin n → ℝ) (h : angleScalar u≠0) :
    angleVacuum u (empty n)=1 := by
  change (angleScalar u / angleScalar u).re = 1
  rw [div_self h, Complex.one_re]

lemma angleVacuum_stationary {n : ℕ} (u : Fin n → ℝ)
    (hL : ∀i,L (3*lambda-u i)≠0) :
    (transfer u).mulVec (angleVacuum u)=angleVacuum u := by
  funext p
  have hh:=congrArg (fun z : ℂ=>(z/angleScalar u).re) (congrFun (angle_rawVacuum_stationary u hL) p)
  simp only [Matrix.mulVec,dotProduct,Matrix.map_apply,Complex.ofRealHom_eq_coe,Finset.sum_div] at hh
  simpa only [Matrix.mulVec,dotProduct,angleVacuum,mul_div_assoc,Complex.re_sum,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hh

lemma continuous_angleScalar {n : ℕ} : Continuous (@angleScalar n) :=
  continuous_angleEvaluation _

lemma continuousOn_angleVacuum {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : ∀u∈S,angleScalar u≠0) : ContinuousOn (fun u=>angleVacuum u) S := by
  apply continuousOn_pi.mpr
  intro p
  exact Complex.continuous_re.continuousOn.comp
    ((continuous_angleEvaluation _).continuousOn.div continuous_angleScalar.continuousOn h)
    (Set.mapsTo_univ _ _)

lemma continuousOn_angleNorthSource {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : ∀u∈S,angleScalar u≠0) : ContinuousOn (fun u=>angleNorthSource u) S := by
  apply continuousOn_pi.mpr
  intro p
  exact Complex.continuous_re.continuousOn.comp
    ((continuous_angleEvaluation _).continuousOn.div continuous_angleScalar.continuousOn h)
    (Set.mapsTo_univ _ _)

section
variable {R F K : Type*} [CommRing R] [Field F] [Field K]
  [Algebra R F] {φ : R →+* K}

lemma rationalAt_lastCoefficient [IsDomain R] [IsFractionRing R F]
    {n : ℕ} (w : Fin n → Tile → F) (v : Fin n → Tile → K)
    (h : ∀i t,RationalAt φ (w i t) (v i t)) (p q : Pairing (n+1)) :
    RationalAt φ (lastCoefficient w p q) (lastCoefficient v p q) := by
  unfold lastCoefficient
  apply RationalAt.sum
  intro t _
  split_ifs
  · exact RationalAt.prod _ _ _ (fun i _=>h i (t i))
  · exact RationalAt.zero
end

lemma rationalAt_angle_sourceTransfer {n : ℕ} (u : Fin n → ℝ)
    (hL : ∀i,L (3*lambda-u i)≠0) (p q : SourcePairing n) :
    RationalAt (angleEvaluation u).toRingHom
      (sourceTransfer (fun i=>(spectralWeights n i).tile) p q)
      ((sourceTransfer (fun i=>(physicalWeights (3*lambda-u i)).tile) p q : ℝ):ℂ) := by
  have hh:=rationalAt_lastCoefficient (fun i=>(spectralWeights n i).tile)
    (fun i t=>Complex.ofRealHom ((physicalWeights (3*lambda-u i)).tile t))
    (rationalAt_angle_spectralWeights u hL) p.val q.val
  rw [lastCoefficient_map Complex.ofRealHom] at hh
  exact hh

lemma rationalAt_angle_northSource {n : ℕ} (u : Fin n → ℝ)
    (hL : ∀i,L (3*lambda-u i)≠0) (p : SourcePairing n) (q : Pairing n) :
    RationalAt (angleEvaluation u).toRingHom
      (northSource (fun i=>(spectralWeights n i).tile) p q)
      ((northSource (fun i=>(physicalWeights (3*lambda-u i)).tile) p q : ℝ):ℂ) := by
  have hh:=rationalAt_lastCoefficient (fun i=>(spectralWeights n i).tile)
    (fun i t=>Complex.ofRealHom ((physicalWeights (3*lambda-u i)).tile t))
    (rationalAt_angle_spectralWeights u hL) p.val q.padTop
  rw [lastCoefficient_map Complex.ofRealHom] at hh
  exact hh

lemma polynomialNorthSource_rational_equation (n : ℕ) :
    (sourceTransfer (fun i=>(spectralWeights n i).tile)).mulVec
        (fun p=>evalLaurent (polynomialNorthSource n p))+
      (northSource (fun i=>(spectralWeights n i).tile)).mulVec (rationalVacuum n)=
      fun p=>evalLaurent (polynomialNorthSource n p) := by
  have hs: (1-sourceTransfer (fun i=>(spectralWeights n i).tile)).mulVec (integratedNorthSource n)=
      (northSource (fun i=>(spectralWeights n i).tile)).mulVec (normalizedVacuum (spectralWeights n)) := by
    rw [integratedNorthSource,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (spectral_source_regular n)),Matrix.one_mulVec]
  have ht:=congrArg (fun v=>spectralNormalization n • v) hs
  rw [Matrix.sub_mulVec,Matrix.one_mulVec] at ht
  simp only [smul_sub,←Matrix.mulVec_smul] at ht
  have he : (fun p=>evalLaurent (polynomialNorthSource n p))=
      spectralNormalization n • integratedNorthSource n := funext (polynomialNorthSource_eval n)
  rw [he]
  change _+(northSource _).mulVec (spectralNormalization n • normalizedVacuum (spectralWeights n))=_
  rw [←ht]
  abel

lemma angle_rawNorthSource_equation {n : ℕ} (u : Fin n → ℝ)
    (hL : ∀i,L (3*lambda-u i)≠0) :
    ((sourceTransfer (fun i=>(physicalWeights (3*lambda-u i)).tile)).map Complex.ofRealHom).mulVec
        (fun p=>angleEvaluation u (polynomialNorthSource n p))+
      ((northSource (fun i=>(physicalWeights (3*lambda-u i)).tile)).map Complex.ofRealHom).mulVec
        (fun p=>angleEvaluation u (polynomialVacuumVector n p))=
      fun p=>angleEvaluation u (polynomialNorthSource n p) := by
  funext p
  have hm:=RationalAt.mulVec (φ:=(angleEvaluation u).toRingHom)
    (sourceTransfer (fun i=>(spectralWeights n i).tile))
    ((sourceTransfer (fun i=>(physicalWeights (3*lambda-u i)).tile)).map Complex.ofRealHom)
    (fun q=>evalLaurent (polynomialNorthSource n q))
    (fun q=>angleEvaluation u (polynomialNorthSource n q))
    (rationalAt_angle_sourceTransfer u hL) (fun q=>RationalAt.algebraMap _) p
  have hn:=RationalAt.mulVec (φ:=(angleEvaluation u).toRingHom)
    (northSource (fun i=>(spectralWeights n i).tile))
    ((northSource (fun i=>(physicalWeights (3*lambda-u i)).tile)).map Complex.ofRealHom)
    (rationalVacuum n) (fun q=>angleEvaluation u (polynomialVacuumVector n q))
    (rationalAt_angle_northSource u hL) (rationalAt_angle_vacuum u) p
  have hh:=hm.add hn
  have he:=congrFun (polynomialNorthSource_rational_equation n) p
  simp only [Pi.add_apply] at he
  rw [he] at hh
  exact hh.unique (RationalAt.algebraMap _)

lemma angleNorthSource_stationary {n : ℕ} (u : Fin n → ℝ)
    (hL : ∀i,L (3*lambda-u i)≠0) :
    (sourceTransfer (fun i=>(physicalWeights (3*lambda-u i)).tile)).mulVec (angleNorthSource u)+
      (northSource (fun i=>(physicalWeights (3*lambda-u i)).tile)).mulVec (angleVacuum u)=
      angleNorthSource u := by
  funext p
  have hh:=congrArg (fun z : ℂ=>(z/angleScalar u).re) (congrFun (angle_rawNorthSource_equation u hL) p)
  simpa only [Pi.add_apply,Matrix.mulVec,dotProduct,Matrix.map_apply,Complex.ofRealHom_eq_coe,
    add_div,Finset.sum_div,mul_div_assoc,Complex.add_re,Complex.re_sum,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,angleNorthSource,angleVacuum] using hh


 

 

 


namespace Pairing

lemma ArcAddition.occupied {n : ℕ} {p q : Pairing n} {a b : Fin n}
    (h : ArcAddition p q a b) (i : Fin n) :
    q.Occupied i ↔ i=a ∨ i=b ∨ p.Occupied i := by
  simp only [Occupied,h.adj]
  aesop

lemma ArcAddition.old {n : ℕ} {p q : Pairing n} {a b i j : Fin n}
    (h : ArcAddition p q a b) (hp : p.Adj i j) : q.Adj i j :=
  (h.adj i j).mpr (Or.inr (Or.inr hp))

lemma ArcAddition.arc {n : ℕ} {p q : Pairing n} {a b : Fin n}
    (h : ArcAddition p q a b) : q.Adj a b := (h.adj a b).mpr (Or.inl ⟨rfl,rfl⟩)

end Pairing



namespace ArcColumn
variable {n : ℕ} {p q : Pairing n} {a b : Fin n} (h : Pairing.ArcAddition p q a b)

include h

omit h in
lemma at_a : arcColumn p a b a=.cup := by simp [arcColumn]
lemma at_b : arcColumn p a b b=.vertical₀ := by simp [arcColumn,ne_of_gt h.lt]
omit h in
lemma at_inside (i : Fin n) (ha : a < i) (hb : i < b) : arcColumn p a b i=.diagonal₀ := by
  simp [arcColumn,ne_of_gt ha,ne_of_lt hb,ha,hb]
lemma at_old (i : Fin n) (hi : p.Occupied i) : arcColumn p a b i=.diagonal₁ := by
  have hn : ¬(a ≤ i ∧ i ≤ b) := fun hh=>h.vacant i hh.1 hh.2 hi
  have hab:=h.lt
  simp only [arcColumn]
  split_ifs <;> first | rfl | omega

lemma west (i : Fin n) : (arcColumn p a b i).Occupied 1 ↔ p.Occupied i := by
  have ha:=h.lt
  have hv:=h.vacant i
  unfold arcColumn
  split_ifs <;> simp_all [Tile.Occupied,Tile.Adj,Tile.edges]
  all_goals apply hv <;> omega

lemma east (i : Fin n) : (arcColumn p a b i).Occupied 2 ↔ q.Occupied i := by
  rw [h.occupied]
  have ha:=h.lt
  have hv:=h.vacant i
  unfold arcColumn
  split_ifs <;> simp_all [Tile.Occupied,Tile.Adj,Tile.edges]
  all_goals apply hv <;> omega

lemma south (i : Fin n) : (arcColumn p a b i).Occupied 0 ↔ a < i ∧ i ≤ b := by
  have ha:=h.lt
  unfold arcColumn
  split_ifs <;> simp_all [Tile.Occupied,Tile.Adj,Tile.edges] <;> omega

lemma north (i : Fin n) : (arcColumn p a b i).Occupied 3 ↔ a ≤ i ∧ i < b := by
  have ha:=h.lt
  unfold arcColumn
  split_ifs <;> simp_all [Tile.Occupied,Tile.Adj,Tile.edges] <;> omega

omit h in
lemma tile_edge {i : Fin n} {r s : Fin 4} (ht : (arcColumn p a b i).Adj r s) :
    Wiring p (arcColumn p a b) (i,r) (i,s) := Or.inl ⟨rfl,ht⟩

lemma reach_north (i : Fin n) (hai : a ≤ i) (hib : i < b) :
    Reach p (arcColumn p a b) (a,2) (i,3) := by
  induction k : i.val using Nat.strong_induction_on generalizing i with
  | h k ih =>
    by_cases he : i=a
    · subst i
      exact .single (tile_edge (by simp [at_a,Tile.Adj,Tile.edges]))
    · have hip : 0 < i.val := by omega
      let j : Fin n:=⟨i.val-1,by omega⟩
      have hji : j.val+1=i.val := by dsimp [j]; omega
      have hj : a ≤ j ∧ j < b := by dsimp [j]; constructor <;> omega
      have hr:=ih j.val (by dsimp [j]; omega) j hj.1 hj.2 rfl
      have hg : Wiring p (arcColumn p a b) (j,3) (i,0) :=
        Or.inr (Or.inr (Or.inl ⟨rfl,rfl,hji,(north h j).mpr hj⟩))
      have hi : arcColumn p a b i=.diagonal₀ := at_inside i (by omega) hib
      exact (hr.tail hg).tail (tile_edge (by simp [hi,Tile.Adj,Tile.edges]))

lemma reach_south (i : Fin n) (hai : a < i) (hib : i ≤ b) :
    Reach p (arcColumn p a b) (a,2) (i,0) := by
  have hip : 0 < i.val := by omega
  let j : Fin n:=⟨i.val-1,by omega⟩
  have hji : j.val+1=i.val := by dsimp [j]; omega
  have hj : a ≤ j ∧ j < b := by dsimp [j]; constructor <;> omega
  exact (reach_north h j hj.1 hj.2).tail
    (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,hji,(north h j).mpr hj⟩)))

lemma reach_arc : Reach p (arcColumn p a b) (a,2) (b,2) :=
  (reach_south h b h.lt le_rfl).tail (tile_edge (by simp [at_b h,Tile.Adj,Tile.edges]))

lemma reach_old (i : Fin n) (hi : p.Occupied i) :
    Reach p (arcColumn p a b) (i,1) (i,2) :=
  .single (tile_edge (by simp [at_old h i hi,Tile.Adj,Tile.edges]))

lemma edge_label {v w : Vertex n} (hw : Wiring p (arcColumn p a b) v w) :
    label a v=label a w ∨ q.Adj (label a v) (label a w) := by
  rcases v with ⟨i,r⟩; rcases w with ⟨j,s⟩
  rcases hw with ⟨rfl,ht⟩ | ⟨rfl,rfl,hp⟩ | ⟨rfl,rfl,_,_⟩ | ⟨rfl,rfl,_,_⟩
  · by_cases hi : i=a
    · subst i
      simp only [at_a,Tile.Adj,Tile.edges,mem_singleton,Prod.mk.injEq] at ht
      rcases ht with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [label]
    · by_cases hj : i=b
      · subst i
        rw [at_b h] at ht
        simp only [Tile.Adj,Tile.edges,mem_singleton,Prod.mk.injEq] at ht
        rcases ht with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inr h.arc
        · exact Or.inr (Pairing.adj_symm h.arc)
      · by_cases hm : a < i ∧ i < b
        · rw [at_inside i hm.1 hm.2] at ht
          simp only [Tile.Adj,Tile.edges,mem_singleton,Prod.mk.injEq] at ht
          rcases ht with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [label]
        · by_cases hp : p.Occupied i
          · rw [at_old h i hp] at ht
            simp only [Tile.Adj,Tile.edges,mem_singleton,Prod.mk.injEq] at ht
            rcases ht with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [label]
          · simp [arcColumn,hi,hj,hm,hp] at ht
  · exact Or.inr (h.old hp)
  · exact Or.inl rfl
  · exact Or.inl rfl

lemma reach_label {v w : Vertex n} (hr : Reach p (arcColumn p a b) v w) :
    label a v=label a w ∨ q.Adj (label a v) (label a w) := by
  induction hr with
  | refl => exact Or.inl rfl
  | @tail w z _ hw ih =>
    obtain he | he := edge_label h hw
    · simpa only [←he] using ih
    obtain hi | hi := ih
    · exact Or.inr (hi ▸ he)
    · exact Or.inl (Pairing.adj_unique (Pairing.adj_symm hi) he)

lemma no_loop (v w : Vertex n) (hw : Wiring p (arcColumn p a b) v w) :
    ∃ j, q.Occupied j ∧ Reach p (arcColumn p a b) v (j,2) := by
  have ha : q.Occupied a:=⟨b,h.arc⟩
  have hb : q.Occupied b:=⟨a,Pairing.adj_symm h.arc⟩
  rcases v with ⟨i,r⟩; rcases w with ⟨j,s⟩
  rcases hw with ⟨rfl,ht⟩ | ⟨rfl,rfl,hp⟩ | ⟨rfl,rfl,_,hn⟩ | ⟨rfl,rfl,hji,hn⟩
  · by_cases hi : i=a
    · subst i
      simp only [at_a,Tile.Adj,Tile.edges,mem_singleton,Prod.mk.injEq] at ht
      rcases ht with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨a,ha,.refl⟩
      · exact ⟨a,ha,reach_symm (reach_north h a le_rfl h.lt)⟩
    · by_cases hj : i=b
      · subst i
        rw [at_b h] at ht
        simp only [Tile.Adj,Tile.edges,mem_singleton,Prod.mk.injEq] at ht
        rcases ht with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact ⟨b,hb,.single (tile_edge (by simp [at_b h,Tile.Adj,Tile.edges]))⟩
        · exact ⟨b,hb,.refl⟩
      · by_cases hm : a < i ∧ i < b
        · rw [at_inside i hm.1 hm.2] at ht
          simp only [Tile.Adj,Tile.edges,mem_singleton,Prod.mk.injEq] at ht
          rcases ht with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · exact ⟨a,ha,reach_symm (reach_south h i hm.1 hm.2.le)⟩
          · exact ⟨a,ha,reach_symm (reach_north h i hm.1.le hm.2)⟩
        · by_cases hp : p.Occupied i
          · rw [at_old h i hp] at ht
            simp only [Tile.Adj,Tile.edges,mem_singleton,Prod.mk.injEq] at ht
            rcases ht with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
            · exact ⟨i,(h.occupied i).mpr (Or.inr (Or.inr hp)),reach_old h i hp⟩
            · exact ⟨i,(h.occupied i).mpr (Or.inr (Or.inr hp)),.refl⟩
          · simp [arcColumn,hi,hj,hm,hp] at ht
  · exact ⟨i,⟨j,h.old hp⟩,reach_old h i ⟨j,hp⟩⟩
  · obtain ⟨hi,hb'⟩:=(north h i).mp hn
    exact ⟨a,ha,reach_symm (reach_north h i hi hb')⟩
  · obtain ⟨hj,hb'⟩:=(north h j).mp hn
    change j.val+1=i.val at hji
    exact ⟨a,ha,reach_symm (reach_south h i (by omega) (by omega))⟩

lemma realizes : Realizes p q (arcColumn p a b) := by
  refine ⟨west h,east h,?_,?_,?_,no_loop h,?_⟩
  · intro i hi ht
    have hh:=(south h i).mp ht
    omega
  · intro i hi ht
    have hh:=(north h i).mp ht
    have:=b.isLt
    omega
  · intro i j hij
    rw [north h i,south h j]
    omega
  · intro i j hij
    constructor
    · intro ht
      rcases (h.adj i j).mp ht with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | hp
      · exact reach_arc h
      · exact reach_symm (reach_arc h)
      · exact ((reach_symm (reach_old h i ⟨j,hp⟩)).tail
          (Or.inr (Or.inl ⟨rfl,rfl,hp⟩))).trans (reach_old h j ⟨i,Pairing.adj_symm hp⟩)
    · intro hr
      have hh:=reach_label h hr
      simpa [label,hij] using hh

end ArcColumn

namespace Pairing

 

lemma exists_arcAddition {n : ℕ} (q : Pairing n) (hq : q ≠ empty n) :
    ∃ (p : Pairing n) (a b : Fin n), p.val.card < q.val.card ∧ ArcAddition p q a b := by
  have hne : q.val.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    exact hq (Subtype.ext he)
  obtain ⟨⟨a,b⟩,hab,hmin⟩:=Finset.exists_min_image q.val
    (fun e : Fin n × Fin n=>e.2.val-e.1.val) hne
  have hlt : a < b:=q.property.1 _ hab
  have hqab : q.Adj a b:=Or.inl hab
  refine ⟨q.omitTwo a b,a,b,?_,hlt,?_,?_⟩
  · apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _,?_⟩
    intro he
    have hh : (a,b) ∈ (q.omitTwo a b).val:=he ▸ hab
    simp [omitTwo] at hh
  · intro i hai hib ⟨j,hij⟩
    obtain ⟨hij,hia,hib',hja,hjb⟩:=(omitTwo_adj q a b i j).mp hij
    have hai' : a < i:=lt_of_le_of_ne hai (Ne.symm hia)
    have hib'' : i < b:=lt_of_le_of_ne hib hib'
    rcases hij with hf | hf
    · have hf_lt := q.property.1 _ hf
      have hc := q.property.2.2 _ hab _ hf
      have hm := hmin _ hf
      dsimp only at hf_lt hc hm
      omega
    · have hf_lt := q.property.1 _ hf
      have hc := q.property.2.2 _ hf _ hab
      have hm := hmin _ hf
      dsimp only at hf_lt hc hm
      omega
  · intro i j
    rw [omitTwo_adj]
    constructor
    · intro hij
      by_cases hia : i=a
      · subst i
        exact Or.inl ⟨rfl,adj_unique hij hqab⟩
      by_cases hib : i=b
      · subst i
        exact Or.inr (Or.inl ⟨rfl,adj_unique hij (adj_symm hqab)⟩)
      have hja : j ≠ a:= by
        rintro rfl
        exact hib (adj_unique (adj_symm hij) hqab)
      have hjb : j ≠ b:= by
        rintro rfl
        exact hia (adj_unique (adj_symm hij) (adj_symm hqab))
      exact Or.inr (Or.inr ⟨hij,hia,hib,hja,hjb⟩)
    · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨hh,_⟩)
      · exact hqab
      · exact adj_symm hqab
      · exact hh

end Pairing



lemma ColumnNonnegative.column {n : ℕ} {w : Fin n → Weights ℝ}
    (hw : ColumnNonnegative w) : PositiveMatrix.Nonnegative (column w) := by
  intro q p
  apply Finset.sum_nonneg
  intro t _
  split_ifs with ht
  · exact hw p q t ht
  · exact le_rfl

lemma ColumnNonnegative.restricted {n : ℕ} {w : Fin n → Weights ℝ}
    (hw : ColumnNonnegative w) : PositiveMatrix.Nonnegative (restrictedColumn w) :=
  fun p q=>hw.column p.val q.val

lemma ColumnNonnegative.injection {n : ℕ} {w : Fin n → Weights ℝ}
    (hw : ColumnNonnegative w) : ∀ p, 0 ≤ injectionColumn w p :=
  fun p=>hw.column p.val (empty n)

lemma arcColumn_weight_pos {n : ℕ} (w : Fin n → Weights ℝ)
    (hA : ∀ i,0 < (w i).A) (hB : ∀ i,0 < (w i).B)
    (hU : ∀ i,i.val+1 < n → 0 < (w i).U)
    {p q : Pairing n} {a b : Fin n} (h : Pairing.ArcAddition p q a b) :
    0 < ∏ i, (w i).tile (arcColumn p a b i) := by
  apply Finset.prod_pos
  intro i _
  have hab:=h.lt
  have hb:=b.isLt
  unfold arcColumn
  split_ifs <;> simp only [Weights.tile]
  · exact hU i (by subst i; omega)
  · exact hA i
  · exact hB i
  · exact hB i
  · exact zero_lt_one

lemma column_arc_pos {n : ℕ} (w : Fin n → Weights ℝ) (hw : ColumnNonnegative w)
    (hA : ∀ i,0 < (w i).A) (hB : ∀ i,0 < (w i).B)
    (hU : ∀ i,i.val+1 < n → 0 < (w i).U)
    {p q : Pairing n} {a b : Fin n} (h : Pairing.ArcAddition p q a b) :
    0 < column w q p := by
  have hl : (∏ i,(w i).tile (arcColumn p a b i)) ≤ column w q p := by
    have := Finset.single_le_sum (s:=Finset.univ)
      (f:=fun t : Configuration n=>if Realizes p q t then ∏ i,(w i).tile (t i) else 0)
      (fun t _=>by split_ifs with ht; exact hw p q t ht; exact le_rfl)
      (Finset.mem_univ (arcColumn p a b))
    simpa only [ite_eq_left (ArcColumn.realizes h),column] using this
  exact (arcColumn_weight_pos w hA hB hU h).trans_le hl

 

theorem column_accessible {n : ℕ} (w : Fin n → Weights ℝ) (hw : ColumnNonnegative w)
    (hA : ∀ i,0 < (w i).A) (hB : ∀ i,0 < (w i).B)
    (hU : ∀ i,i.val+1 < n → 0 < (w i).U) :
    PositiveMatrix.Accessible (restrictedColumn w) (injectionColumn w) := by
  intro q
  induction k : q.val.val.card using Nat.strong_induction_on generalizing q with
  | h k ih =>
    obtain ⟨p,a,b,hcard,hadd⟩:=Pairing.exists_arcAddition q.val q.property
    have hpq:=column_arc_pos w hw hA hB hU hadd
    by_cases hp : p=empty n
    · subst p
      refine ⟨0,?_⟩
      simpa only [pow_zero,Matrix.one_mulVec,injectionColumn] using hpq
    · let p' : NonemptyPairing n:=⟨p,hp⟩
      obtain ⟨m,hm⟩:=ih p.val.card (by omega) p' rfl
      refine ⟨m+1,?_⟩
      rw [pow_succ',←Matrix.mulVec_mulVec]
      exact (mul_pos hpq hm).trans_le
        (PositiveMatrix.entry_mul_le_mulVec hw.restricted
          ((hw.restricted.pow m).mulVec hw.injection) q p')

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_AugmentedColumn
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped BigOperators Classical
open Finset _root_.Matrix



lemma column_last_factor {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Weights K) (z : Weights K) (q p : Pairing (n+1)) :
    column (Fin.snoc w z) q p = lastCoefficient (fun i=>(w i).tile) q p * z.tile (lastTile p q) := by
  have hw : (fun i=>((Fin.snoc w z : Fin (n+1) → Weights K) i).tile)=
      Fin.snoc (fun i=>(w i).tile) z.tile := by
    funext i
    refine Fin.lastCases ?_ (fun i=>?_) i <;> simp
  change rawColumn _ q p=_
  rw [hw,rawColumn_last_factor]

lemma northInjection_column_blocks {K : Type*} [CommRing K] {n : ℕ} (w : Fin n → Weights K) :
    (column (Fin.snoc w northInjectionWeights)).submatrix (sourceFullSplit n) (sourceFullSplit n)=
      Matrix.fromBlocks (column w) 0 (northSource (fun i=>(w i).tile))
        (sourceTransfer (fun i=>(w i).tile)) := by
  ext q p
  change column _ _ _=_
  rw [column_last_factor]
  cases q with
  | inl q =>
    cases p with
    | inl p => simp [lastCoefficient_padTop,lastTile,Weights.tile]; rfl
    | inr p => simp [lastTile,p.property,northInjectionWeights,Weights.tile]
  | inr q =>
    cases p with
    | inl p => simp [lastTile,q.property,northInjectionWeights,Weights.tile,northSource]
    | inr p => simp [lastTile,q.property,p.property,northInjectionWeights,Weights.tile,sourceTransfer]

lemma augmentVector_stationary {K : Type*} [CommRing K] {n : ℕ} (w : Fin n → Weights K)
    (v : Pairing n → K) (z : SourcePairing n → K)
    (hv : (column w).mulVec v=v)
    (hz : (sourceTransfer (fun i=>(w i).tile)).mulVec z+
      (northSource (fun i=>(w i).tile)).mulVec v=z) :
    (column (Fin.snoc w northInjectionWeights)).mulVec (augmentVector v z)=augmentVector v z := by
  funext q
  obtain ⟨q,rfl⟩:=(sourceFullSplit n).surjective q
  have he : (column (Fin.snoc w northInjectionWeights)).mulVec (augmentVector v z) (sourceFullSplit n q)=
      (Matrix.fromBlocks (column w) 0 (northSource (fun i=>(w i).tile))
        (sourceTransfer (fun i=>(w i).tile))).mulVec (Sum.elim v z) q := by
    rw [Matrix.mulVec,dotProduct,←(sourceFullSplit n).sum_comp]
    simp_rw [augmentVector_split]
    change (∑ p,((column (Fin.snoc w northInjectionWeights)).submatrix
      (sourceFullSplit n) (sourceFullSplit n)) q p * Sum.elim v z p)=_
    rw [northInjection_column_blocks]
    rfl
  rw [he,augmentVector_split]
  cases q with
  | inl q => simpa [Matrix.mulVec,dotProduct,Fintype.sum_sum_type] using congrFun hv q
  | inr q =>
    have hh:=congrFun hz q
    simp only [Pi.add_apply,Matrix.mulVec,dotProduct] at hh
    simpa only [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂,Sum.elim_inl,Sum.elim_inr,add_comm] using hh


lemma angleAugmented_restricted_stationary {n : ℕ} (u : Fin n → ℝ)
    (hL : ∀i,L (3*lambda-u i)≠0) (h : angleScalar u≠0) :
    (restrictedColumn (Fin.snoc (fun i=>physicalWeights (3*lambda-u i)) northInjectionWeights)).mulVec
        (fun p=>angleAugmented u p.val)+
      injectionColumn (Fin.snoc (fun i=>physicalWeights (3*lambda-u i)) northInjectionWeights)=
      fun p=>angleAugmented u p.val := by
  have hh:=augmentVector_stationary (fun i=>physicalWeights (3*lambda-u i))
    (angleVacuum u) (angleNorthSource u) (angleVacuum_stationary u hL) (angleNorthSource_stationary u hL)
  funext p
  have hp:=congrFun hh p.val
  rw [column_mulVec_nonempty,augmentVector_empty,angleVacuum_empty u h,mul_one] at hp
  simpa only [Pi.add_apply,add_comm,angleAugmented] using hp

lemma continuousOn_angleAugmented {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : ∀u∈S,angleScalar u≠0) : ContinuousOn (fun u=>angleAugmented u) S := by
  apply continuousOn_pi.mpr
  intro p
  obtain ⟨q,rfl⟩:=(sourceFullSplit n).surjective p
  have he : (fun u=>angleAugmented u (sourceFullSplit n q))=
      fun u=>Sum.elim (angleVacuum u) (angleNorthSource u) q := by
    funext u
    exact augmentVector_split _ _ _
  rw [he]
  cases q with
  | inl q => exact (continuousOn_pi.mp (continuousOn_angleVacuum h)) q
  | inr q => exact (continuousOn_pi.mp (continuousOn_angleNorthSource h)) q

end

 

 

noncomputable section
open scoped BigOperators Classical
namespace ColumnChain
section RingCoefficients
variable {K : Type*} [CommRing K] {n : ℕ}

lemma weighted_runs_cons (w : Fin n → Weights K) (p q : Pairing n)
    (t : Configuration n) (ts : List (Configuration n)) :
    (if Runs p (t::ts) q then weight w (t::ts) else 0)=
      ∑ r : Pairing n, (if Realizes r q t then ∏i,(w i).tile (t i) else 0)*
        (if Runs p ts r then weight w ts else 0) := by
  by_cases hh : ∃r,Runs p ts r
  · obtain ⟨r,hr⟩:=hh
    rw [Finset.sum_eq_single r]
    · have he : Runs p (t::ts) q ↔ Realizes r q t := by
        constructor
        · rintro ⟨r',hr',ht⟩
          exact runs_unique hr' hr ▸ ht
        · exact fun ht=>⟨r,hr,ht⟩
      simp only [he,hr,ite_true,weight]
      split_ifs <;> simp
    · intro s _ hsr
      have hs : ¬Runs p ts s := fun hs=>hsr (runs_unique hs hr)
      simp [hs]
    · simp
  · have hs : ∀r,¬Runs p ts r := fun r hr=>hh ⟨r,hr⟩
    have hq : ¬Runs p (t::ts) q := fun ⟨r,hr,_⟩=>hs r hr
    simp [hq,hs]

lemma mass_zero (w : Fin n → Weights K) (q p : Pairing n) :
    mass w 0 q p=if q=p then 1 else 0 := by
  simp [mass,Runs,weight,eq_comm]

lemma mass_succ (w : Fin n → Weights K) (m : ℕ) (q p : Pairing n) :
    mass w (m+1) q p=∑r,column w q r*mass w m r p := by
  unfold mass
  rw [←(Fin.consEquiv (fun _ : Fin (m+1)=>Configuration n)).sum_comp]
  simp only [Fintype.sum_prod_type]
  simp only [Fin.consEquiv,Equiv.coe_fn_mk,List.ofFn_cons]
  simp_rw [weighted_runs_cons]
  conv_lhs =>
    arg 2
    ext t
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [column,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]

 

lemma mass_eq_pow (w : Fin n → Weights K) (m : ℕ) (q p : Pairing n) :
    mass w m q p=(column w ^ m) q p := by
  induction m generalizing q p with
  | zero => simp [mass_zero,Matrix.one_apply]
  | succ m ih =>
    rw [mass_succ,pow_succ']
    simp only [Matrix.mul_apply,ih]

end RingCoefficients






end ColumnChain
end





end CriticalStrip.Diagram

 

 

namespace CriticalStrip.PositiveMatrix
noncomputable section
open _root_.Matrix
open scoped BigOperators Classical

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma submatrix_pow_equiv (Q : Matrix ι ι ℝ) (e : κ ≃ ι) (k : ℕ) :
    (Q.submatrix e e)^k=(Q^k).submatrix e e := by
  induction k with
  | zero => simp only [pow_zero,Matrix.submatrix_one_equiv]
  | succ k ih => rw [pow_succ,pow_succ,ih,Matrix.submatrix_mul_equiv]

lemma SummablePowers.reindex {Q : Matrix ι ι ℝ} (hs : SummablePowers Q) (e : κ ≃ ι) :
    SummablePowers (Q.submatrix e e) := by
  intro i j
  simpa only [submatrix_pow_equiv,Matrix.submatrix_apply] using hs (e i) (e j)

lemma summablePowers_reindex_iff (Q : Matrix ι ι ℝ) (e : κ ≃ ι) :
    SummablePowers (Q.submatrix e e) ↔ SummablePowers Q := by
  refine ⟨fun h=>?_,fun h=>h.reindex e⟩
  have hh:=h.reindex e.symm
  have he : (Q.submatrix e e).submatrix e.symm e.symm=Q := by
    ext i j; simp only [Matrix.submatrix_apply,Equiv.apply_symm_apply]
  rw [he] at hh
  exact hh

 

lemma SummablePowers.fromBlocks_zero_right {Q : Matrix ι ι ℝ} (hs : SummablePowers Q)
    (hQ : Nonnegative Q) (B : Matrix κ ι ℝ) (hB : ∀i j,0≤B i j) :
    SummablePowers (Matrix.fromBlocks Q 0 B 0) := by
  obtain ⟨z,hz,he⟩:=hs.hasSupervector hQ
  have hBz : ∀i,0≤B.mulVec z i := fun i=>Finset.sum_nonneg fun j _=>mul_nonneg (hB i j) (hz j).le
  apply HasSupervector.summablePowers
  · refine ⟨Sum.elim z (fun i=>B.mulVec z i+1),?_,?_⟩
    · intro i
      cases i with
      | inl i => exact hz i
      | inr i => exact lt_of_le_of_lt (hBz i) (lt_add_one _)
    · intro i
      cases i with
      | inl i => simpa only [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
          Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Sum.elim_inl,Sum.elim_inr,
          Matrix.zero_apply,zero_mul,Finset.sum_const_zero,add_zero] using he i
      | inr i =>
        simp only [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
          Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Sum.elim_inl,Sum.elim_inr,
          Matrix.zero_apply,zero_mul,Finset.sum_const_zero,add_zero]
        exact lt_add_one _
  · intro i j
    cases i <;> cases j <;> simp only [Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.zero_apply]
    · exact hQ _ _
    · exact le_rfl
    · exact hB _ _
    · exact le_rfl

 

lemma summablePowers_of_zero_cols (M : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (hM : Nonnegative M) (hs : SummablePowers M.toBlocks₁₁)
    (hz : ∀i j,M i (.inr j)=0) : SummablePowers M := by
  have hblock : M=Matrix.fromBlocks M.toBlocks₁₁ 0 M.toBlocks₂₁ 0 := by
    ext i j
    cases i <;> cases j <;> simp only [Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.zero_apply,Matrix.toBlocks₁₁,Matrix.toBlocks₂₁,Matrix.of_apply,hz]
  rw [hblock]
  exact hs.fromBlocks_zero_right (fun i j=>hM (.inl i) (.inl j)) M.toBlocks₂₁
    (fun i j=>hM (.inr i) (.inl j))

end
end CriticalStrip.PositiveMatrix

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_BoundaryTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.FiniteBranchTree
noncomputable section
open scoped BigOperators Classical

variable {V S : Type*} [DecidableEq V]



lemma nil_mem_iff (vertex : S → V) (next : S → Bool → S) (free : Finset V) (s : S) :
    [] ∈ leaves vertex next free s ↔ vertex s ∉ free := by
  rw [leaves]
  split_ifs <;> simp_all

lemma cons_mem_iff (vertex : S → V) (next : S → Bool → S) (free : Finset V)
    (s : S) (b : Bool) (l : List Bool) :
    b::l ∈ leaves vertex next free s ↔
      vertex s ∈ free ∧ l ∈ leaves vertex next (free.erase (vertex s)) (next s b) := by
  rw [leaves]
  split_ifs with hs
  · cases b <;> simp [hs]
  · simp [hs]


lemma visited_mem_domain (vertex : S → V) (next : S → Bool → S) {free : Finset V}
    {s : S} {l : List Bool} (hl : l ∈ leaves vertex next free s) :
    ∀ v ∈ visited vertex next s l, v ∈ free := by
  induction l generalizing free s with
  | nil => simp [visited]
  | cons b l ih =>
    obtain ⟨hs,hl⟩ := (cons_mem_iff vertex next free s b l).mp hl
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hs
    · exact Finset.mem_of_mem_erase (ih hl v hv)

lemma visited_nodup (vertex : S → V) (next : S → Bool → S) {free : Finset V}
    {s : S} {l : List Bool} (hl : l ∈ leaves vertex next free s) :
    (visited vertex next s l).Nodup := by
  induction l generalizing free s with
  | nil => simp [visited]
  | cons b l ih =>
    obtain ⟨_,hl⟩ := (cons_mem_iff vertex next free s b l).mp hl
    apply List.nodup_cons.mpr
    refine ⟨?_,ih hl⟩
    intro hv
    exact Finset.notMem_erase _ _ (visited_mem_domain vertex next hl _ hv)



lemma mem_leaves_iff (vertex : S → V) (next : S → Bool → S) (D : Finset V)
    (s : S) (l : List Bool) :
    l ∈ leaves vertex next D s ↔
      (visited vertex next s l).Nodup ∧
      (∀ v ∈ visited vertex next s l, v ∈ D) ∧
      (vertex (terminal next s l) ∉ D ∨
        vertex (terminal next s l) ∈ visited vertex next s l) := by
  induction l generalizing D s with
  | nil => simp [nil_mem_iff,visited,terminal]
  | cons b l ih =>
    rw [cons_mem_iff,ih]
    simp only [visited,List.nodup_cons,List.mem_cons,forall_eq_or_imp,terminal]
    constructor
    · rintro ⟨hs,hn,hm,ht⟩
      have hnot : vertex s ∉ visited vertex next (next s b) l := by
        intro hv
        exact Finset.notMem_erase _ _ (hm _ hv)
      refine ⟨⟨hnot,hn⟩,⟨hs,fun v hv => Finset.mem_of_mem_erase (hm v hv)⟩,?_⟩
      rcases ht with ht | ht
      · by_cases he : vertex (terminal next (next s b) l)=vertex s
        · exact Or.inr (Or.inl he)
        · exact Or.inl (fun hd => ht (Finset.mem_erase.mpr ⟨he,hd⟩))
      · exact Or.inr (Or.inr ht)
    · rintro ⟨⟨hnot,hn⟩,⟨hs,hm⟩,ht⟩
      refine ⟨hs,hn,fun v hv =>Finset.mem_erase.mpr ⟨?_,hm v hv⟩,?_⟩
      · exact fun he =>hnot (he ▸ hv)
      · rcases ht with ht | he | ht
        · exact Or.inl (fun hd =>ht (Finset.mem_of_mem_erase hd))
        · exact Or.inl (fun hd =>(Finset.mem_erase.mp hd).1 he)
        · exact Or.inr ht



end
end CriticalStrip.FiniteBranchTree

 

 

 

namespace CriticalStrip.HoneycombBranch
noncomputable section
open scoped BigOperators Classical
open FiniteBranchTree

lemma wordWeight_eq (l : List Bool) :
    wordWeight factor l = (rho : ℂ)^l.length * Diagram.phase ^ turn l := by
  induction l with
  | nil => simp [wordWeight,turn]
  | cons b l ih =>
    simp only [wordWeight_cons,ih,List.length_cons,turn,factor,pow_succ,
      zpow_add₀ Diagram.phase_ne_zero]
    ring

lemma phase_norm : ‖Diagram.phase‖ = 1 := by
  simp [Diagram.phase,Complex.norm_exp]

lemma wordWeight_norm (l : List Bool) : ‖wordWeight factor l‖ = rho^l.length := by
  rw [wordWeight_eq,norm_mul,norm_pow,norm_zpow,phase_norm,one_zpow,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos rho_pos]


end
end CriticalStrip.HoneycombBranch

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_HoneycombTiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped BigOperators


namespace Tile



lemma physical_weight (r : ℝ) (t : Tile) (h : t ≠ .verticalPair) :
    (Weights.mk (r^2) (r^2) r 0 (r^2)).tile t =
      r ^ ((if t.upperUsed then 1 else 0) + (if t.lowerUsed then 1 else 0) : ℕ) := by
  cases t <;> simp_all [Weights.tile,upperUsed,lowerUsed]

end Tile
end
end CriticalStrip.Diagram





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_HoneycombDictionary
attribute [-instance] _root_.OAI.CriticalStrip.HoneycombAssignment.portWiring_symm_instance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators
open Diagram Diagram.PathGraph

namespace HoneycombAssignment
variable {N : ℕ}

lemma tileSupport_eq_image (D : HoneycombAssignment N) :
    D.tileSupport = (fun v : Triangle => (v.1,v.2.1)) '' D.graph.support := by
  ext ⟨i,j⟩
  change D.tile (i,j) ≠ .vacant ↔ ∃ v ∈ D.graph.support, (v.1,v.2.1)=(i,j)
  rw [Tile.nonvacant_iff_used]
  constructor
  · rintro (hu | hd)
    · exact ⟨up i j,(D.up_support_iff i j).mpr hu,rfl⟩
    · exact ⟨down i j,(D.down_support_iff i j).mpr hd,rfl⟩
  · rintro ⟨⟨a,k,b⟩,hv,he⟩
    have hi : a=i := congrArg Prod.fst he
    have hj : k=j := congrArg Prod.snd he
    subst a k
    cases b
    · exact Or.inr ((D.down_support_iff i j).mp hv)
    · exact Or.inl ((D.up_support_iff i j).mp hv)

 

lemma support_ncard_eq (D : HoneycombAssignment N) (F : Finset Cell)
    (hF : ∀ q, D.tile q ≠ .vacant ↔ q∈F) :
    D.graph.support.ncard =
      ∑ q∈F, ((if (D.tile q).upperUsed then 1 else 0) +
        (if (D.tile q).lowerUsed then 1 else 0) : ℕ) := by
  let U := F.filter (fun q => (D.tile q).upperUsed)
  let L := F.filter (fun q => (D.tile q).lowerUsed)
  let fu : Cell → Triangle := fun q => up q.1 q.2
  let fl : Cell → Triangle := fun q => down q.1 q.2
  have hu : Function.Injective fu := by
    intro q r h
    have hh := congrArg (fun v : Triangle => (v.1,v.2.1)) h
    exact hh
  have hl : Function.Injective fl := by
    intro q r h
    have hh := congrArg (fun v : Triangle => (v.1,v.2.1)) h
    exact hh
  have hd : Disjoint (U.image fu) (L.image fl) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hw
    have hh := congrArg (fun v : Triangle => v.2.2) hr
    exact Bool.false_ne_true hh
  have hs : D.graph.support = ↑(U.image fu ∪ L.image fl) := by
    ext ⟨i,j,b⟩
    cases b
    · change down i j ∈ D.graph.support ↔ _
      rw [D.down_support_iff]
      simp only [Finset.mem_coe,Finset.mem_union,Finset.mem_image,U,L,
        Finset.mem_filter,fu,fl,up,down,Prod.mk.injEq,Bool.true_eq_false,and_false,exists_false,
        false_or,and_true]
      constructor
      · intro h
        exact ⟨(i,j),⟨(hF (i,j)).mp ((Tile.nonvacant_iff_used _).mpr (Or.inr h)),h⟩,rfl,rfl⟩
      · rintro ⟨⟨a,k⟩,⟨_,h⟩,hi,hj⟩
        dsimp only at hi hj
        subst a k; exact h
    · change up i j ∈ D.graph.support ↔ _
      rw [D.up_support_iff]
      simp only [Finset.mem_coe,Finset.mem_union,Finset.mem_image,U,L,
        Finset.mem_filter,fu,fl,up,down,Prod.mk.injEq,Bool.false_eq_true,and_false,exists_false,
        or_false,and_true]
      constructor
      · intro h
        exact ⟨(i,j),⟨(hF (i,j)).mp ((Tile.nonvacant_iff_used _).mpr (Or.inl h)),h⟩,rfl,rfl⟩
      · rintro ⟨⟨a,k⟩,⟨_,h⟩,hi,hj⟩
        dsimp only at hi hj
        subst a k; exact h
  rw [hs,Set.ncard_coe_finset,Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ hu,Finset.card_image_of_injective _ hl,Finset.sum_add_distrib]
  simp [U,L]

end HoneycombAssignment

namespace HoneycombConfiguration
variable {N : ℕ} {b : BoundaryPort}

lemma tileSupport_finite (D : HoneycombConfiguration N b) (hN : 1≤N) (hb : b ≠ .bottom 0) :
    D.toHoneycombAssignment.tileSupport.Finite := by
  rw [HoneycombAssignment.tileSupport_eq_image]
  exact ((D.toWire hN).support_finite (b.vertex_ne_source hb)).image _



theorem weight_eq_wire (D : HoneycombConfiguration N b) (hN : 1≤N) (hb : b ≠ .bottom 0) :
    D.weight=(D.toWire hN).weight := by
  let F := (D.tileSupport_finite hN hb).toFinset
  have hF : ∀ q, D.tile q≠.vacant ↔ q∈F := by
    intro q
    exact ((D.tileSupport_finite hN hb).mem_toFinset).symm
  have he := finprod_eq_prod_of_mulSupport_subset
    (fun q : Cell => (physicalWeights (2*Diagram.lambda)).tile (D.tile q)) (s := F)
  have hw : D.weight = ∏ q∈F, (physicalWeights (2*Diagram.lambda)).tile (D.tile q) := by
    apply he
    intro q hq
    apply (hF q).mp
    intro ht; exact hq (by simp only [ht,Weights.tile])
  rw [hw,physicalWeights_two_lambda]
  change (∏ q∈F, (⟨rho^2,rho^2,rho,0,rho^2⟩ : Weights ℝ).tile (D.tile q)) = _
  have hw' (q : Cell) :
      (⟨rho^2,rho^2,rho,0,rho^2⟩ : Weights ℝ).tile (D.tile q) =
        rho ^ ((if (D.tile q).upperUsed then 1 else 0) +
          (if (D.tile q).lowerUsed then 1 else 0) : ℕ) :=
    Tile.physical_weight rho (D.tile q) (D.physical q)
  simp_rw [hw']
  rw [Finset.prod_pow_eq_pow_sum]
  change rho ^ _ = rho ^ D.toHoneycombAssignment.graph.support.ncard
  rw [D.toHoneycombAssignment.support_ncard_eq F hF]

lemma weight_eq_path (D : HoneycombConfiguration N b) (hN : 1≤N) (hb : b ≠ .bottom 0) :
    D.weight = rho ^ (D.toWire hN).path.length := by
  rw [D.weight_eq_wire hN hb,(D.toWire hN).weight_eq (b.vertex_ne_source hb)]


theorem summable_weight_iff (N : ℕ) (b : BoundaryPort) (hN : 1≤N) (hb : b ≠ .bottom 0) :
    Summable (weight (N := N) (b := b)) ↔
      Summable (WireConfiguration.weight (N := N) (finish := b.vertex N)) := by
  have h := (equivWires N b hN hb).summable_iff (f := WireConfiguration.weight)
  have he : WireConfiguration.weight ∘ (equivWires N b hN hb) = weight := by
    funext D
    exact (D.weight_eq_wire hN hb).symm
  rwa [he] at h

lemma tsum_weight (N : ℕ) (b : BoundaryPort) (hN : 1≤N) (hb : b ≠ .bottom 0) :
    ∑' D : HoneycombConfiguration N b, D.weight =
      ∑' D : WireConfiguration N (b.vertex N), D.weight := by
  rw [show (fun D : HoneycombConfiguration N b => D.weight) =
    (fun D => (D.toWire hN).weight) from funext (fun D => D.weight_eq_wire hN hb)]
  exact (equivWires N b hN hb).tsum_eq WireConfiguration.weight

theorem arch_sum (N : ℕ) (hN : 1≤N) (k : ℤ) (hk : k≠0) :
    K N k = ∑' D : HoneycombConfiguration N (.bottom k), D.weight := by
  rw [tsum_weight N (.bottom k) hN (by simpa using hk)]
  exact WireConfiguration.arch_sum N k hk

theorem arch_summable (N : ℕ) (hN : 1≤N) (k : ℤ) (hk : k≠0) :
    Summable (archWeight N k) ↔ Summable (weight (N := N) (b := .bottom k)) := by
  rw [summable_weight_iff N (.bottom k) hN (by simpa using hk)]
  exact WireConfiguration.arch_summable N k hk

end HoneycombConfiguration
end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_DeformationWeights
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open _root_.Matrix Set
open scoped BigOperators Classical

lemma lambda_pos : 0<lambda := by unfold lambda; positivity

lemma L_deformation_pos {t : ℝ} (ht : t∈Icc 0 lambda) : 0<L (3*lambda-t) := by
  unfold L
  apply mul_pos <;> apply Real.sin_pos_of_pos_of_lt_pi <;>
    unfold lambda at * <;> linarith [ht.1,ht.2,Real.pi_pos]

lemma physicalWeights_deformation_pos {t : ℝ} (ht : t∈Ioc 0 lambda) :
    0<(physicalWeights (3*lambda-t)).A ∧ 0<(physicalWeights (3*lambda-t)).B ∧
      0<(physicalWeights (3*lambda-t)).U := by
  have hL:=L_deformation_pos ⟨ht.1.le,ht.2⟩
  have hd : 0<Real.cos (2*lambda) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> unfold lambda <;> linarith [Real.pi_pos]
  have ht₀ : 0<Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (ht.2.trans_lt (by unfold lambda; linarith [Real.pi_pos]))
  have hs : 0<Real.sin (3*lambda-t) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> unfold lambda at * <;> linarith [ht.1,ht.2,Real.pi_pos]
  unfold physicalWeights
  dsimp only
  rw [show 3*lambda-(3*lambda-t)=t by ring]
  exact ⟨div_pos (mul_pos hd ht₀) hL,div_pos (mul_pos hs ht₀) hL,div_pos (mul_pos hd hs) hL⟩

lemma physicalWeights_deformation_tile_nonneg {t : ℝ} (ht : t∈Icc 0 lambda)
    (s : Tile) (hs : ¬s.Occupied 0) : 0<(physicalWeights (3*lambda-t)).U ∧
      0≤(physicalWeights (3*lambda-t)).tile s := by
  rcases eq_or_lt_of_le ht.1 with rfl | ht₀
  · rw [sub_zero,physicalWeights_three_lambda]
    constructor
    · norm_num [deletionWeights]
    · cases s <;> norm_num [deletionWeights,Weights.tile]
  · obtain ⟨hA,hB,hU⟩:=physicalWeights_deformation_pos ⟨ht₀,ht.2⟩
    refine ⟨hU,?_⟩
    cases s <;> simp_all [Tile.Occupied,Tile.Adj,Tile.edges,Weights.tile]
    any_goals positivity

lemma physicalWeights_two_lambda_nonneg (s : Tile) : 0≤(physicalWeights (2*lambda)).tile s := by
  rw [physicalWeights_two_lambda]
  have hrho : 0 < rho := by unfold rho; positivity
  cases s <;> simp only [Weights.tile] <;> positivity

lemma physicalWeights_two_lambda_pos :
    0<(physicalWeights (2*lambda)).A ∧ 0<(physicalWeights (2*lambda)).B ∧
      0<(physicalWeights (2*lambda)).U := by
  have hh:=physicalWeights_deformation_pos (t:=lambda) ⟨lambda_pos,le_rfl⟩
  simpa only [show 3*lambda-lambda=2*lambda by ring] using hh

lemma northInjection_nonneg (s : Tile) : 0≤(northInjectionWeights : Weights ℝ).tile s := by
  cases s <;> norm_num [northInjectionWeights,Weights.tile]


lemma deformationWeights_eq (n : ℕ) (t : ℝ) :
    deformationWeights n t=Fin.snoc
      (fun i=>physicalWeights (3*lambda-deformationAngles n t i)) northInjectionWeights := by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · change physicalWeights (3*lambda-t)=
      (Fin.snoc (fun i : Fin (n+1)=>physicalWeights (3*lambda-deformationAngles n t i))
        northInjectionWeights : Fin (n+1+1) → Weights ℝ) ((0 : Fin (n+1)).castSucc)
    rw [Fin.snoc_castSucc]
    rfl
  · rw [deformationWeights,Fin.cons_succ]
    refine Fin.lastCases ?_ (fun j=>?_) j
    · rw [augmentedPhysicalWeights,Fin.snoc_last,Fin.succ_last,Fin.snoc_last]
    · rw [augmentedPhysicalWeights,Fin.snoc_castSucc,Fin.succ_castSucc,Fin.snoc_castSucc]
      simp only [deformationAngles,Fin.cons_succ,show 3*lambda-lambda=2*lambda by ring]

lemma deformationWeights_physical (n : ℕ) : deformationWeights n lambda=augmentedPhysicalWeights (n+1) := by
  rw [deformationWeights_eq]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j=>?_) i <;>
    simp only [deformationAngles,Fin.cons_zero,Fin.cons_succ,show 3*lambda-lambda=2*lambda by ring]

lemma deformationWeights_flat (n : ℕ) : deformationWeights n 0 0=deletionWeights := by
  simp [deformationWeights,physicalWeights_three_lambda]

lemma augmentedPhysical_tile_nonneg (n : ℕ) (i : Fin (n+1)) (s : Tile) :
    0≤(augmentedPhysicalWeights n i).tile s := by
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simpa only [augmentedPhysicalWeights,Fin.snoc_last] using northInjection_nonneg s
  · simpa only [augmentedPhysicalWeights,Fin.snoc_castSucc] using physicalWeights_two_lambda_nonneg s

lemma deformationWeights_nonnegative (n : ℕ) {t : ℝ} (ht : t∈Icc 0 lambda) :
    ColumnNonnegative (deformationWeights n t) := by
  intro p q s hs
  apply Finset.prod_nonneg
  intro i _
  refine Fin.cases ?_ (fun j=>?_) i
  · exact (physicalWeights_deformation_tile_nonneg ht (s 0) (hs.south 0 rfl)).2
  · exact augmentedPhysical_tile_nonneg n j (s j.succ)

lemma deformationWeights_accessible (n : ℕ) {t : ℝ} (ht : t∈Ioc 0 lambda) :
    PositiveMatrix.Accessible (restrictedColumn (deformationWeights n t))
      (injectionColumn (deformationWeights n t)) := by
  apply column_accessible _ (deformationWeights_nonnegative n ⟨ht.1.le,ht.2⟩)
  · intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact (physicalWeights_deformation_pos ht).1
    · refine Fin.lastCases ?_ (fun j=>?_) j
      · norm_num [deformationWeights,augmentedPhysicalWeights,northInjectionWeights]
      · simpa only [deformationWeights,Fin.cons_succ,augmentedPhysicalWeights,Fin.snoc_castSucc]
          using physicalWeights_two_lambda_pos.1
  · intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact (physicalWeights_deformation_pos ht).2.1
    · refine Fin.lastCases ?_ (fun j=>?_) j
      · norm_num [deformationWeights,augmentedPhysicalWeights,northInjectionWeights]
      · simpa only [deformationWeights,Fin.cons_succ,augmentedPhysicalWeights,Fin.snoc_castSucc]
          using physicalWeights_two_lambda_pos.2.1
  · intro i hi
    revert hi
    refine Fin.cases ?_ (fun j=>?_) i
    · intro _; exact (physicalWeights_deformation_pos ht).2.2
    · revert j
      apply Fin.lastCases
      · intro hh
        simp only [Fin.val_succ,Fin.val_last] at hh
        omega
      · intro j _
        simpa only [deformationWeights,Fin.cons_succ,augmentedPhysicalWeights,Fin.snoc_castSucc]
          using physicalWeights_two_lambda_pos.2.2

lemma deformationAngles_L_ne_zero (n : ℕ) {t : ℝ} (ht : t∈Icc 0 lambda)
    (i : Fin (n+1)) : L (3*lambda-deformationAngles n t i)≠0 := by
  refine Fin.cases ?_ (fun j=>?_) i
  · exact (L_deformation_pos ht).ne'
  · exact (L_deformation_pos (t:=lambda) ⟨lambda_pos.le,le_rfl⟩).ne'

lemma deformationWeights_stationary (n : ℕ) {t : ℝ} (ht : t∈Icc 0 lambda) :
    (restrictedColumn (deformationWeights n t)).mulVec (fun p=>angleAugmented (deformationAngles n t) p.val)+
      injectionColumn (deformationWeights n t)=fun p=>angleAugmented (deformationAngles n t) p.val := by
  rw [deformationWeights_eq]
  exact angleAugmented_restricted_stationary _ (deformationAngles_L_ne_zero n ht)
    (deformationAngles_scalar_ne_zero n ht)


 

 


lemma continuousOn_column {α : Type*} [TopologicalSpace α] {S : Set α} {n : ℕ}
    (w : α → Fin n → Weights ℝ) (hw : ∀i s,ContinuousOn (fun t=>(w t i).tile s) S) :
    ContinuousOn (fun t=>column (w t)) S := by
  apply continuousOn_pi.mpr
  intro p
  apply continuousOn_pi.mpr
  intro q
  unfold column
  apply continuousOn_finsetSum
  intro s _
  by_cases hs : Realizes q p s
  · simp only [ite_eq_left hs]
    exact continuousOn_finsetProd _ (fun i _=>hw i (s i))
  · simp only [ite_eq_right hs]
    exact continuousOn_const

lemma continuousOn_deformationWeights_tile (n : ℕ) (i : Fin (n+1+1)) (s : Tile) :
    ContinuousOn (fun t=>(deformationWeights n t i).tile s) (Icc 0 lambda) := by
  refine Fin.cases ?_ (fun j=>?_) i
  · change ContinuousOn (fun t=>(physicalWeights (3*lambda-t)).tile s) (Icc 0 lambda)
    cases s <;> simp only [physicalWeights,Weights.tile]
    · exact continuousOn_const
    all_goals
      apply ContinuousOn.div
      · fun_prop
      · unfold L; fun_prop
      · exact fun t ht=>(L_deformation_pos ht).ne'
  · change ContinuousOn (fun _ : ℝ=>(augmentedPhysicalWeights n j).tile s) (Icc 0 lambda)
    exact continuousOn_const

lemma continuousOn_deformationColumn (n : ℕ) :
    ContinuousOn (fun t=>restrictedColumn (deformationWeights n t)) (Icc 0 lambda) := by
  have hh:=continuousOn_column (deformationWeights n) (continuousOn_deformationWeights_tile n)
  apply continuousOn_pi.mpr
  intro p
  apply continuousOn_pi.mpr
  intro q
  exact continuousOn_pi.mp (continuousOn_pi.mp hh p.val) q.val

lemma continuous_deformationAngles (n : ℕ) : Continuous (deformationAngles n) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · exact continuous_id
  · exact continuous_const

lemma continuousOn_deformationVector (n : ℕ) :
    ContinuousOn (fun t=>fun p : NonemptyPairing (n+1+1)=>angleAugmented (deformationAngles n t) p.val)
      (Icc 0 lambda) := by
  have hc:=continuousOn_angleAugmented (S:=deformationAngles n '' Icc 0 lambda) (by
    rintro u ⟨t,ht,rfl⟩
    exact deformationAngles_scalar_ne_zero n ht)
  have hh:=hc.comp (continuous_deformationAngles n).continuousOn (fun t ht=>⟨t,ht,rfl⟩)
  apply continuousOn_pi.mpr
  intro p
  exact continuousOn_pi.mp hh p.val

lemma summablePowers_flat_bottom {n : ℕ} (w : Fin (n+1) → Weights ℝ)
    (hzero : w 0=deletionWeights) (hw : ColumnNonnegative w)
    (hs : PositiveMatrix.SummablePowers (restrictedColumn (fun i=>w i.succ))) :
    PositiveMatrix.SummablePowers (restrictedColumn w) := by
  let e:=Pairing.nonemptyBottomSplit n
  apply (PositiveMatrix.summablePowers_reindex_iff _ e).mp
  apply PositiveMatrix.summablePowers_of_zero_cols
  · exact fun i j=>hw.restricted (e i) (e j)
  · have he : ((restrictedColumn w).submatrix e e).toBlocks₁₁=
        restrictedColumn (fun i=>w i.succ) := by
      ext q p
      exact column_padBottom w p.val q.val
    rw [he]
    exact hs
  · intro i p
    exact column_deletion_bottom_col w hzero p.val.val (e i).val (not_not.mp p.property)

 

theorem augmentedPhysical_summablePowers (n : ℕ) :
    PositiveMatrix.SummablePowers (restrictedColumn (augmentedPhysicalWeights n)) := by
  induction n with
  | zero =>
    intro p
    exact (p.property (Pairing.eq_empty_of_le_one (by omega) p.val)).elim
  | succ n ih =>
    rw [←deformationWeights_physical]
    apply PositiveMatrix.summablePowers_on_Icc
      (fun t=>restrictedColumn (deformationWeights n t))
      (fun t=>injectionColumn (deformationWeights n t))
      (fun t=>fun p=>angleAugmented (deformationAngles n t) p.val)
      lambda_pos.le (continuousOn_deformationColumn n) (continuousOn_deformationVector n)
      (fun t ht=>(deformationWeights_nonnegative n ht).restricted)
      (fun t ht=>(deformationWeights_nonnegative n ht).injection)
      (fun t ht=>deformationWeights_stationary n ht)
      ?_ (fun t ht=>deformationWeights_accessible n ht)
      lambda ⟨lambda_pos.le,le_rfl⟩
    apply summablePowers_flat_bottom _ (deformationWeights_flat n)
      (deformationWeights_nonnegative n ⟨le_rfl,lambda_pos.le⟩)
    simpa only [deformationWeights,Fin.cons_succ] using ih

end
end CriticalStrip.Diagram

 

 

namespace CriticalStrip.PositiveMatrix
noncomputable section
open _root_.Matrix
open scoped BigOperators Classical

variable {ι κ : Type*}

variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma SummablePowers.transpose {Q : Matrix ι ι ℝ} (hs : SummablePowers Q) :
    SummablePowers Q.transpose := by
  intro i j
  simpa only [←Matrix.transpose_pow,Matrix.transpose_apply] using hs j i

lemma summablePowers_of_zero_rows (M : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (hM : Nonnegative M) (hs : SummablePowers M.toBlocks₁₁)
    (hz : ∀i j,M (.inr i) j=0) : SummablePowers M := by
  have ht : SummablePowers M.transpose := by
    apply summablePowers_of_zero_cols
    · exact fun i j=>hM j i
    · exact hs.transpose
    · intros; apply hz
  simpa only [Matrix.transpose_transpose] using ht.transpose

end
end CriticalStrip.PositiveMatrix





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ReversedConvergence
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open _root_.Matrix Set
open scoped BigOperators Classical

lemma physicalWeights_lambda_nonneg (s : Tile) : 0≤(physicalWeights lambda).tile s := by
  rw [physicalWeights_lambda]
  have hrho : 0 < rho := by unfold rho; positivity
  cases s <;> simp only [Weights.tile] <;> positivity

lemma physicalWeights_reverse_pos {t : ℝ} (ht : t∈Ioc 0 lambda) :
    0<(physicalWeights t).A ∧ 0<(physicalWeights t).B ∧ 0<(physicalWeights t).U := by
  have hh:=physicalWeights_deformation_pos ht
  rw [physicalWeights_reflection] at hh
  exact ⟨hh.2.2,hh.2.1,hh.1⟩

lemma physicalWeights_reverse_tile_nonneg {t : ℝ} (ht : t∈Icc 0 lambda)
    (s : Tile) (hs : ¬s.Occupied 0) : 0≤(physicalWeights t).tile s := by
  rcases eq_or_lt_of_le ht.1 with rfl | ht₀
  · rw [physicalWeights_zero]
    cases s <;> norm_num [identityWeights,Weights.tile]
  · obtain ⟨hA,hB,hU⟩:=physicalWeights_reverse_pos ⟨ht₀,ht.2⟩
    cases s <;> simp_all [Tile.Occupied,Tile.Adj,Tile.edges,Weights.tile]
    any_goals positivity

lemma reverseDeformationWeights_eq (n : ℕ) (t : ℝ) :
    reverseDeformationWeights n t=Fin.snoc
      (fun i=>physicalWeights (3*lambda-reverseDeformationAngles n t i)) northInjectionWeights := by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · change physicalWeights t=
      (Fin.snoc (fun i : Fin (n+1)=>physicalWeights (3*lambda-reverseDeformationAngles n t i))
        northInjectionWeights : Fin (n+1+1) → Weights ℝ) ((0 : Fin (n+1)).castSucc)
    rw [Fin.snoc_castSucc]
    simp only [reverseDeformationAngles,Fin.cons_zero,show 3*lambda-(3*lambda-t)=t by ring]
  · rw [reverseDeformationWeights,Fin.cons_succ]
    refine Fin.lastCases ?_ (fun j=>?_) j
    · rw [augmentedReversedWeights,Fin.snoc_last,Fin.succ_last,Fin.snoc_last]
    · rw [augmentedReversedWeights,Fin.snoc_castSucc,Fin.succ_castSucc,Fin.snoc_castSucc]
      simp only [reverseDeformationAngles,Fin.cons_succ,show 3*lambda-2*lambda=lambda by ring]

lemma reverseDeformationWeights_physical (n : ℕ) :
    reverseDeformationWeights n lambda=augmentedReversedWeights (n+1) := by
  rw [reverseDeformationWeights_eq]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j=>?_) i <;>
    simp only [reverseDeformationAngles,Fin.cons_zero,Fin.cons_succ,
      show 3*lambda-(3*lambda-lambda)=lambda by ring,show 3*lambda-2*lambda=lambda by ring]

lemma reverseDeformationWeights_flat (n : ℕ) : reverseDeformationWeights n 0 0=identityWeights := by
  simp [reverseDeformationWeights,physicalWeights_zero]

lemma augmentedReversed_tile_nonneg (n : ℕ) (i : Fin (n+1)) (s : Tile) :
    0≤(augmentedReversedWeights n i).tile s := by
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simpa only [augmentedReversedWeights,Fin.snoc_last] using northInjection_nonneg s
  · simpa only [augmentedReversedWeights,Fin.snoc_castSucc] using physicalWeights_lambda_nonneg s

lemma reverseDeformationWeights_nonnegative (n : ℕ) {t : ℝ} (ht : t∈Icc 0 lambda) :
    ColumnNonnegative (reverseDeformationWeights n t) := by
  intro p q s hs
  apply Finset.prod_nonneg
  intro i _
  refine Fin.cases ?_ (fun j=>?_) i
  · exact physicalWeights_reverse_tile_nonneg ht (s 0) (hs.south 0 rfl)
  · exact augmentedReversed_tile_nonneg n j (s j.succ)

lemma physicalWeights_lambda_pos :
    0<(physicalWeights lambda).A ∧ 0<(physicalWeights lambda).B ∧ 0<(physicalWeights lambda).U :=
  physicalWeights_reverse_pos ⟨lambda_pos,le_rfl⟩

lemma reverseDeformationWeights_accessible (n : ℕ) {t : ℝ} (ht : t∈Ioc 0 lambda) :
    PositiveMatrix.Accessible (restrictedColumn (reverseDeformationWeights n t))
      (injectionColumn (reverseDeformationWeights n t)) := by
  apply column_accessible _ (reverseDeformationWeights_nonnegative n ⟨ht.1.le,ht.2⟩)
  · intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact (physicalWeights_reverse_pos ht).1
    · refine Fin.lastCases ?_ (fun j=>?_) j
      · norm_num [reverseDeformationWeights,augmentedReversedWeights,northInjectionWeights]
      · simpa only [reverseDeformationWeights,Fin.cons_succ,augmentedReversedWeights,Fin.snoc_castSucc]
          using physicalWeights_lambda_pos.1
  · intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact (physicalWeights_reverse_pos ht).2.1
    · refine Fin.lastCases ?_ (fun j=>?_) j
      · norm_num [reverseDeformationWeights,augmentedReversedWeights,northInjectionWeights]
      · simpa only [reverseDeformationWeights,Fin.cons_succ,augmentedReversedWeights,Fin.snoc_castSucc]
          using physicalWeights_lambda_pos.2.1
  · intro i hi
    revert hi
    refine Fin.cases ?_ (fun j=>?_) i
    · intro _; exact (physicalWeights_reverse_pos ht).2.2
    · revert j
      apply Fin.lastCases
      · intro hh
        simp only [Fin.val_succ,Fin.val_last] at hh
        omega
      · intro j _
        simpa only [reverseDeformationWeights,Fin.cons_succ,augmentedReversedWeights,Fin.snoc_castSucc]
          using physicalWeights_lambda_pos.2.2

lemma reverseDeformationAngles_scalar_ne_zero (n : ℕ) {t : ℝ} (ht : t∈Icc 0 lambda) :
    angleScalar (reverseDeformationAngles n t)≠0 := by
  have hh:=deformationAngles_scalar_ne_zero n ht
  rw [angleScalar,angleEvaluation_scalar] at hh ⊢
  have he : (fun i=>(Real.cos (2*reverseDeformationAngles n t i-3*lambda):ℂ))=
      (fun i=>(Real.cos (2*deformationAngles n t i-3*lambda):ℂ)) := by
    funext i
    refine Fin.cases ?_ (fun j=>?_) i
    · simp only [reverseDeformationAngles,deformationAngles,Fin.cons_zero,
        show 2*(3*lambda-t)-3*lambda= -(2*t-3*lambda) by ring,Real.cos_neg]
    · simp only [reverseDeformationAngles,deformationAngles,Fin.cons_succ,
        show 2*(2*lambda)-3*lambda=lambda by ring,show 2*lambda-3*lambda= -lambda by ring,Real.cos_neg]
  rw [he]
  exact hh

lemma reverseDeformationAngles_L_ne_zero (n : ℕ) {t : ℝ} (ht : t∈Icc 0 lambda)
    (i : Fin (n+1)) : L (3*lambda-reverseDeformationAngles n t i)≠0 := by
  refine Fin.cases ?_ (fun j=>?_) i
  · simp only [reverseDeformationAngles,Fin.cons_zero,show 3*lambda-(3*lambda-t)=t by ring]
    rw [←L_reflection t]
    exact (L_deformation_pos ht).ne'
  · simp only [reverseDeformationAngles,Fin.cons_succ]
    rw [L_reflection]
    simpa only [show 3*lambda-lambda=2*lambda by ring] using
      (L_deformation_pos (t:=lambda) ⟨lambda_pos.le,le_rfl⟩).ne'

lemma reverseDeformationWeights_stationary (n : ℕ) {t : ℝ} (ht : t∈Icc 0 lambda) :
    (restrictedColumn (reverseDeformationWeights n t)).mulVec
        (fun p=>angleAugmented (reverseDeformationAngles n t) p.val)+
      injectionColumn (reverseDeformationWeights n t)=fun p=>angleAugmented (reverseDeformationAngles n t) p.val := by
  rw [reverseDeformationWeights_eq]
  exact angleAugmented_restricted_stationary _ (reverseDeformationAngles_L_ne_zero n ht)
    (reverseDeformationAngles_scalar_ne_zero n ht)

lemma continuousOn_reverseDeformationWeights_tile (n : ℕ) (i : Fin (n+1+1)) (s : Tile) :
    ContinuousOn (fun t=>(reverseDeformationWeights n t i).tile s) (Icc 0 lambda) := by
  refine Fin.cases ?_ (fun j=>?_) i
  · change ContinuousOn (fun t=>(physicalWeights t).tile s) (Icc 0 lambda)
    cases s <;> simp only [physicalWeights,Weights.tile]
    · exact continuousOn_const
    all_goals
      apply ContinuousOn.div
      · fun_prop
      · unfold L; fun_prop
      · intro t ht
        rw [←L_reflection t]
        exact (L_deformation_pos ht).ne'
  · change ContinuousOn (fun _ : ℝ=>(augmentedReversedWeights n j).tile s) (Icc 0 lambda)
    exact continuousOn_const

lemma continuousOn_reverseDeformationColumn (n : ℕ) :
    ContinuousOn (fun t=>restrictedColumn (reverseDeformationWeights n t)) (Icc 0 lambda) := by
  have hh:=continuousOn_column (reverseDeformationWeights n) (continuousOn_reverseDeformationWeights_tile n)
  apply continuousOn_pi.mpr
  intro p
  apply continuousOn_pi.mpr
  intro q
  exact continuousOn_pi.mp (continuousOn_pi.mp hh p.val) q.val

lemma continuous_reverseDeformationAngles (n : ℕ) : Continuous (reverseDeformationAngles n) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · exact continuous_const.sub continuous_id
  · exact continuous_const

lemma continuousOn_reverseDeformationVector (n : ℕ) :
    ContinuousOn (fun t=>fun p : NonemptyPairing (n+1+1)=>angleAugmented (reverseDeformationAngles n t) p.val)
      (Icc 0 lambda) := by
  have hc:=continuousOn_angleAugmented (S:=reverseDeformationAngles n '' Icc 0 lambda) (by
    rintro u ⟨t,ht,rfl⟩
    exact reverseDeformationAngles_scalar_ne_zero n ht)
  have hh:=hc.comp (continuous_reverseDeformationAngles n).continuousOn (fun t ht=>⟨t,ht,rfl⟩)
  apply continuousOn_pi.mpr
  intro p
  exact continuousOn_pi.mp hh p.val

lemma summablePowers_identity_bottom {n : ℕ} (w : Fin (n+1) → Weights ℝ)
    (hzero : w 0=identityWeights) (hw : ColumnNonnegative w)
    (hs : PositiveMatrix.SummablePowers (restrictedColumn (fun i=>w i.succ))) :
    PositiveMatrix.SummablePowers (restrictedColumn w) := by
  let e:=Pairing.nonemptyBottomSplit n
  apply (PositiveMatrix.summablePowers_reindex_iff _ e).mp
  apply PositiveMatrix.summablePowers_of_zero_rows
  · exact fun i j=>hw.restricted (e i) (e j)
  · have he : ((restrictedColumn w).submatrix e e).toBlocks₁₁=
        restrictedColumn (fun i=>w i.succ) := by
      ext q p
      exact column_padBottom w p.val q.val
    rw [he]
    exact hs
  · intro q i
    exact column_identity_bottom_row w hzero (e i).val q.val.val (not_not.mp q.property)

 

theorem augmentedReversed_summablePowers (n : ℕ) :
    PositiveMatrix.SummablePowers (restrictedColumn (augmentedReversedWeights n)) := by
  induction n with
  | zero =>
    intro p
    exact (p.property (Pairing.eq_empty_of_le_one (by omega) p.val)).elim
  | succ n ih =>
    rw [←reverseDeformationWeights_physical]
    apply PositiveMatrix.summablePowers_on_Icc
      (fun t=>restrictedColumn (reverseDeformationWeights n t))
      (fun t=>injectionColumn (reverseDeformationWeights n t))
      (fun t=>fun p=>angleAugmented (reverseDeformationAngles n t) p.val)
      lambda_pos.le (continuousOn_reverseDeformationColumn n) (continuousOn_reverseDeformationVector n)
      (fun t ht=>(reverseDeformationWeights_nonnegative n ht).restricted)
      (fun t ht=>(reverseDeformationWeights_nonnegative n ht).injection)
      (fun t ht=>reverseDeformationWeights_stationary n ht)
      ?_ (fun t ht=>reverseDeformationWeights_accessible n ht)
      lambda ⟨lambda_pos.le,le_rfl⟩
    apply summablePowers_identity_bottom _ (reverseDeformationWeights_flat n)
      (reverseDeformationWeights_nonnegative n ⟨le_rfl,lambda_pos.le⟩)
    simpa only [reverseDeformationWeights,Fin.cons_succ] using ih

end





end CriticalStrip.Diagram





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_HoneycombClip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators
open Diagram


namespace HoneycombAssignment
variable {N : ℕ}

lemma turn_tile_all (D : HoneycombAssignment N) (b : ℤ) (q : Cell) :
    (D.turn b).tile q=(D.tile (turnCell N b q)).turn := by
  rcases q with ⟨i,j⟩
  by_cases hj : j<N
  · exact D.turn_tile b i j hj |>.trans (by simp only [turnCell,turnRow,hj,ite_true,Equiv.coe_fn_mk])
  · simp only [turn,turnCell,Equiv.coe_fn_mk,turnRow,hj,ite_false,D.outside (b-i) j (by omega),Tile.turn_vacant]

lemma turn_weight (D : HoneycombAssignment N) (b : ℤ) : (D.turn b).weight=D.weight := by
  unfold weight
  simp_rw [D.turn_tile_all b,Tile.turn_weight]
  exact finprod_comp_equiv (turnCell N b) (f:=fun q : Cell=>(physicalWeights (2*Diagram.lambda)).tile (D.tile q))

lemma turn_tileSupport (D : HoneycombAssignment N) (b : ℤ) :
    (D.turn b).tileSupport=turnCell N b ⁻¹' D.tileSupport := by
  ext q
  change ((D.turn b).tile q≠.vacant) ↔ D.tile (turnCell N b q)≠.vacant
  rw [D.turn_tile_all b,Tile.turn_nonvacant]


lemma Fits.mono {D : HoneycombAssignment N} {m l : ℕ} (h : D.Fits m) (hm : m≤l) :
    D.Fits l := by
  intro q hq
  obtain ⟨h₁,h₂⟩:=h q hq
  constructor <;> omega

lemma exists_fits (D : HoneycombAssignment N) (h : D.tileSupport.Finite) : ∃m,D.Fits m := by
  let F:=h.toFinset
  refine ⟨F.sup (fun q=>q.1.natAbs+1),?_⟩
  intro q hq
  have hm : q∈F := h.mem_toFinset.mpr hq
  have hs : q.1.natAbs+1≤F.sup (fun q=>q.1.natAbs+1) := Finset.le_sup (f:=fun q : Cell=>q.1.natAbs+1) hm
  have hi : q.1≤(q.1.natAbs:ℤ) := Int.le_natAbs
  have hi' : -q.1≤(q.1.natAbs:ℤ) := by have ht : -q.1≤((-q.1).natAbs:ℤ) := Int.le_natAbs; simpa only [Int.natAbs_neg] using ht
  constructor <;> omega

end HoneycombAssignment

namespace TopArchConfiguration
variable {N : ℕ} {a b : ℤ}

lemma tileSupport_finite (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a≠b) :
    D.toHoneycombAssignment.tileSupport.Finite := by
  have hb : BoundaryPort.bottom (b-a)≠.bottom 0 := by intro hh; have hh:=BoundaryPort.bottom.inj hh; omega
  have hs:=(D.toArch hN).tileSupport_finite hN hb
  change (D.toHoneycombAssignment.turn b).tileSupport.Finite at hs
  rw [←D.toHoneycombAssignment.turn_turn b,HoneycombAssignment.turn_tileSupport]
  exact hs.preimage (turnCell N b).injective.injOn

lemma weight_toArch (D : TopArchConfiguration N a b) (hN : 1≤N) :
    (D.toArch hN).weight=D.toHoneycombAssignment.weight :=
  D.toHoneycombAssignment.turn_weight b

end TopArchConfiguration
end





noncomputable section
open scoped Classical BigOperators
open Diagram

lemma windowCell_injective (N m : ℕ) : Function.Injective (windowCell N m) := by
  rintro ⟨k,j⟩ ⟨l,i⟩ h
  cases k <;> cases l
  all_goals simp only [windowCell,Prod.mk.injEq] at h
  · exact Prod.ext (congrArg Sum.inl (Fin.ext (by omega))) (Fin.ext h.2)
  · omega
  · omega
  · exact Prod.ext (congrArg Sum.inr (Fin.ext (by omega))) (Fin.ext h.2)

lemma windowCell_range (N m : ℕ) (q : Cell) :
    (∃ x,windowCell N m x=q) ↔ -(m:ℤ)≤q.1 ∧ q.1<(m:ℤ) ∧ q.2<N := by
  constructor
  · rintro ⟨⟨k,j⟩,rfl⟩
    cases k <;> dsimp [windowCell] <;> omega
  · rintro ⟨hl,hr,hj⟩
    by_cases hq : q.1<0
    · refine ⟨(.inl ⟨(-1-q.1).toNat,by omega⟩,⟨q.2,hj⟩),?_⟩
      apply Prod.ext <;> dsimp [windowCell]
      omega
    · refine ⟨(.inr ⟨q.1.toNat,by omega⟩,⟨q.2,hj⟩),?_⟩
      apply Prod.ext <;> dsimp [windowCell]
      omega

namespace HoneycombAssignment
variable {N : ℕ}

lemma weight_window (D : HoneycombAssignment N) (m : ℕ) (h : D.Fits m) :
    D.weight=(∏ k : Fin m,∏ j : Fin N,
      (physicalWeights (2*Diagram.lambda)).tile (D.tile (-1-(k.val:ℤ),j.val))) *
      (∏ k : Fin m,∏ j : Fin N,
      (physicalWeights (2*Diagram.lambda)).tile (D.tile ((k.val:ℤ),j.val))) := by
  let F:=Finset.univ.image (windowCell N m)
  have hs : Function.mulSupport (fun q=>(physicalWeights (2*Diagram.lambda)).tile (D.tile q)) ⊆ (F:Set Cell) := by
    intro q hq
    have ht : D.tile q≠.vacant := by
      intro he
      exact hq (by change (physicalWeights (2*Diagram.lambda)).tile (D.tile q)=1; rw [he]; rfl)
    have hj : q.2<N := by
      by_contra hn
      exact ht (D.outside _ _ (by omega))
    obtain ⟨x,hx⟩ := (windowCell_range N m q).mpr ⟨(h _ ht).1,(h _ ht).2,hj⟩
    exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,hx⟩
  rw [weight,finprod_eq_prod_of_mulSupport_subset _ hs]
  rw [Finset.prod_image (by intro x _ y _ he; exact windowCell_injective N m he)]
  rw [Fintype.prod_prod_type,Fintype.prod_sum_type]
  rfl

end HoneycombAssignment

namespace TopArchConfiguration
variable {N : ℕ} {a b : ℤ}



lemma clips_weight (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a<b)
    (ha : a<0) (hb : 0≤b) (m : ℕ) (hf : D.toHoneycombAssignment.Fits m) :
    ColumnChain.weight (SewnRectangle.leftWeights N) (List.ofFn ((D.extend hN hab).leftClip m)) *
    ColumnChain.weight (SewnRectangle.rightWeights N) (List.ofFn ((D.extend hN hab).rightClip m))=
      D.toHoneycombAssignment.weight := by
  rw [D.leftClip_weight hN hab hb,D.rightClip_weight hN hab ha]
  exact (D.toHoneycombAssignment.weight_window m hf).symm

end TopArchConfiguration
end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NorthBijection
attribute [-instance] _root_.OAI.CriticalStrip.NorthHistory.boundedFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators
open Diagram

namespace CrossTopArch
variable {N : ℕ}

lemma exists_fits (D : CrossTopArch N) (hN : 1≤N) : ∃m,D.Fits m :=
  D.arch.toHoneycombAssignment.exists_fits (D.arch.tileSupport_finite hN (by omega))


end CrossTopArch



namespace NorthHistory
variable {N m : ℕ}

lemma ofCross_weight (D : CrossTopArch.Bounded N m) (hN : 1≤N) :
    (ofCross D hN).weight=D.val.weight :=
  D.val.arch.clips_weight hN (by omega) (by omega) (by omega) m D.property

lemma toCross_weight (h : NorthHistory N m) (hN : 1≤N) :
    h.weight=(h.toCross hN).weight := by
  have hh := ofCross_weight ⟨h.toCross hN,h.toCross_fits hN⟩ hN
  rwa [ofCross_toCross h hN] at hh

end NorthHistory
end
end CriticalStrip





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NorthMass
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators
open Diagram

lemma sum_subtype_indicator {α : Type*} [Fintype α] (P : α→Prop) (f : α→ℝ) :
    (∑ x : {a // P a},f x.val)=∑ x,if P x then f x else 0 := by
  rw [←Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter P) (by simp) f).symm

namespace NorthHistory
variable {N m : ℕ}

lemma weighted_valid (l r : Fin m → Configuration (N+1)) :
    (if Valid l r then ColumnChain.weight (SewnRectangle.leftWeights N) (List.ofFn l)*
        ColumnChain.weight (SewnRectangle.rightWeights N) (List.ofFn r) else 0)=
      ∑p : Pairing (N+1),∑q : Pairing (N+1),
        (if ColumnChain.Runs (empty (N+1)) (List.ofFn l) p then
          ColumnChain.weight (SewnRectangle.leftWeights N) (List.ofFn l) else 0)*
        (if p.GluesAt (Fin.last N) q then (1:ℝ) else 0)*
        (if ColumnChain.Runs (empty (N+1)) (List.ofFn r) q then
          ColumnChain.weight (SewnRectangle.rightWeights N) (List.ofFn r) else 0) := by
  by_cases hl : ∃p,ColumnChain.Runs (empty (N+1)) (List.ofFn l) p
  · obtain ⟨p,hp⟩:=hl
    have hpl (x : Pairing (N+1)) :
        ColumnChain.Runs (empty (N+1)) (List.ofFn l) x ↔ x=p :=
      ⟨fun h=>ColumnChain.runs_unique h hp,fun h=>h ▸ hp⟩
    by_cases hr : ∃q,ColumnChain.Runs (empty (N+1)) (List.ofFn r) q
    · obtain ⟨q,hq⟩:=hr
      have hqr (x : Pairing (N+1)) :
          ColumnChain.Runs (empty (N+1)) (List.ofFn r) x ↔ x=q :=
        ⟨fun h=>ColumnChain.runs_unique h hq,fun h=>h ▸ hq⟩
      rw [Finset.sum_eq_single p]
      · rw [Finset.sum_eq_single q]
        · by_cases hwl : ColumnChain.weight (SewnRectangle.leftWeights N) (List.ofFn l)=0
          · simp [Valid,hpl,hqr,hwl]
          · by_cases hwr : ColumnChain.weight (SewnRectangle.rightWeights N) (List.ofFn r)=0
            · simp [Valid,hpl,hqr,hwr]
            · simp only [Valid,hpl,hqr,hwl,hwr,ne_eq,not_false_eq_true,true_and,
                ite_true]
              have he : (∃ p₁ q₁ : Pairing (N+1), p₁=p ∧ q₁=q ∧ p₁.GluesAt (Fin.last N) q₁) ↔
                  p.GluesAt (Fin.last N) q :=
                ⟨by rintro ⟨_,_,rfl,rfl,h⟩; exact h, fun h=>⟨p,q,rfl,rfl,h⟩⟩
              simp only [he]
              split_ifs <;> simp
        · intro q' _ hq'
          simp only [hqr,hq',ite_false,mul_zero]
        · simp
      · intro p' _ hp'
        simp only [hpl,hp',ite_false,zero_mul,Finset.sum_const_zero]
      · simp
    · have he (q : Pairing (N+1)) : ¬ColumnChain.Runs (empty (N+1)) (List.ofFn r) q :=
        fun h=>hr ⟨q,h⟩
      simp only [Valid,he,false_and,and_false,exists_false,ite_false,mul_zero,Finset.sum_const_zero]
  · have he (p : Pairing (N+1)) : ¬ColumnChain.Runs (empty (N+1)) (List.ofFn l) p :=
      fun h=>hl ⟨p,h⟩
    simp only [Valid,he,false_and,exists_false,and_false,ite_false,zero_mul,Finset.sum_const_zero]

lemma sum_weight_pairings (N m : ℕ) :
    (∑ h : NorthHistory N m,h.weight)=
      ∑p : Pairing (N+1),∑q : Pairing (N+1),
        (column (SewnRectangle.leftWeights N)^m) p (empty (N+1))*
        (if p.GluesAt (Fin.last N) q then (1:ℝ) else 0)*
        (column (SewnRectangle.rightWeights N)^m) q (empty (N+1)) := by
  rw [show (∑h : NorthHistory N m,h.weight)=
      ∑ h : {lr : (Fin m → Configuration (N+1)) × (Fin m → Configuration (N+1)) // Valid lr.1 lr.2},
        ColumnChain.weight (SewnRectangle.leftWeights N) (List.ofFn h.val.1)*
        ColumnChain.weight (SewnRectangle.rightWeights N) (List.ofFn h.val.2) from
    Fintype.sum_equiv pairEquiv _ _ (fun _=>rfl)]
  rw [sum_subtype_indicator (fun lr : (Fin m → Configuration (N+1)) × (Fin m → Configuration (N+1))=>Valid lr.1 lr.2)
    (fun lr=>ColumnChain.weight (SewnRectangle.leftWeights N) (List.ofFn lr.1)*
      ColumnChain.weight (SewnRectangle.rightWeights N) (List.ofFn lr.2)),Fintype.sum_prod_type]
  simp_rw [weighted_valid]
  simp_rw [←ColumnChain.mass_eq_pow,ColumnChain.mass,Finset.sum_mul,Finset.mul_sum]
  conv_lhs => arg 2; intro l; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  conv_lhs => arg 2; intro l; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

lemma sum_weight_source (N m : ℕ) :
    (∑ h : NorthHistory N m,h.weight)=
      sourceGlue N (fun p=>(column (SewnRectangle.leftWeights N)^m) p.val (empty (N+1)))
        (fun q=>(column (SewnRectangle.rightWeights N)^m) q.val (empty (N+1))) := by
  rw [sum_weight_pairings,←(sourceFullSplit N).sum_comp,sourceGlue_eq_sum]
  simp_rw [←(sourceFullSplit N).sum_comp]
  have hl (p : Pairing N) (q : Pairing (N+1)) : ¬p.padTop.GluesAt (Fin.last N) q :=
    fun h=>Pairing.padTop_not_occupied_last p h.1
  have hr (p : Pairing (N+1)) (q : Pairing N) : ¬p.GluesAt (Fin.last N) q.padTop :=
    fun h=>Pairing.padTop_not_occupied_last q ((h.2.1 _).mp h.1)
  simp only [Fintype.sum_sum_type,sourceFullSplit_inl,sourceFullSplit_inr,hl,hr,ite_false,mul_zero,
    zero_mul,Finset.sum_const_zero,zero_add,mul_assoc]
  rfl

lemma sum_weight_cross (N m : ℕ) (hN : 1≤N) [Fintype (CrossTopArch.Bounded N m)] :
    (∑ h : NorthHistory N m,h.weight)=∑D : CrossTopArch.Bounded N m,D.val.weight :=
  Fintype.sum_equiv (equivCross hN) _ _ (fun h=>toCross_weight h hN)

end NorthHistory
end
end CriticalStrip

 

 

namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators
open _root_.Matrix Filter Topology

lemma column_pow_empty_empty {n : ℕ} (w : Fin n → Weights ℝ) (m : ℕ) :
    (column w^m) (empty n) (empty n)=1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ']
    change (column w).mulVec (fun p=>(column w^m) p (empty n)) (empty n)=1
    rw [column_mulVec_empty,ih]

 

lemma column_pow_empty_nonempty {n : ℕ} (w : Fin n → Weights ℝ)
    (v : NonemptyPairing n → ℝ)
    (hv : (restrictedColumn w).mulVec v+injectionColumn w=v) (m : ℕ) :
    ∀ p : NonemptyPairing n, (column w^m) p.val (empty n)=
      v p-(restrictedColumn w^m).mulVec v p := by
  induction m with
  | zero =>
    intro p
    simp only [pow_zero,Matrix.one_apply,p.property,ite_false,Matrix.one_mulVec,sub_self]
  | succ m ih =>
    intro p
    rw [pow_succ']
    change (column w).mulVec (fun q=>(column w^m) q (empty n)) p.val=_
    rw [column_mulVec_nonempty,column_pow_empty_empty,mul_one]
    have he : (fun q : NonemptyPairing n=>(column w^m) q.val (empty n))=
        v-(restrictedColumn w^m).mulVec v := funext ih
    rw [he,Matrix.mulVec_sub,Matrix.mulVec_mulVec,←pow_succ']
    have hp:=congrFun hv p
    simp only [Pi.add_apply] at hp
    simp only [Pi.sub_apply]
    linarith

theorem column_pow_empty_tendsto {n : ℕ} (w : Fin n → Weights ℝ)
    (hs : PositiveMatrix.SummablePowers (restrictedColumn w))
    (v : NonemptyPairing n → ℝ)
    (hv : (restrictedColumn w).mulVec v+injectionColumn w=v) (p : NonemptyPairing n) :
    Tendsto (fun m : ℕ=>(column w^m) p.val (empty n)) atTop (𝓝 (v p)) := by
  simp_rw [column_pow_empty_nonempty w v hv]
  have hh:=(hs.mulVec_tendsto_zero v p).const_sub (v p)
  simpa only [sub_zero] using hh

lemma physical_empty_tendsto_source (N : ℕ) (p : SourcePairing N) :
    Tendsto (fun m : ℕ=>(column (SewnRectangle.leftWeights N)^m) p.val (empty (N+1))) atTop
      (𝓝 (angleNorthSource (fun _ : Fin N=>lambda) p)) := by
  have hp : p.val≠empty (N+1) := by
    intro h; exact empty_not_occupied _ (h ▸ p.property)
  have hh:=column_pow_empty_tendsto (SewnRectangle.leftWeights N)
    (augmentedPhysical_summablePowers N) _ (physical_augmented_stationary N) ⟨p.val,hp⟩
  simpa only [angleAugmented,augmentVector_source] using hh

lemma reversed_empty_tendsto_source (N : ℕ) (p : SourcePairing N) :
    Tendsto (fun m : ℕ=>(column (SewnRectangle.rightWeights N)^m) p.val (empty (N+1))) atTop
      (𝓝 (angleNorthSource (fun _ : Fin N=>2*lambda) p)) := by
  have hp : p.val≠empty (N+1) := by
    intro h; exact empty_not_occupied _ (h ▸ p.property)
  have hh:=column_pow_empty_tendsto (SewnRectangle.rightWeights N)
    (augmentedReversed_summablePowers N) _ (reversed_augmented_stationary N) ⟨p.val,hp⟩
  simpa only [angleAugmented,augmentVector_source] using hh

end
end CriticalStrip.Diagram

 

 

namespace CriticalStrip
noncomputable section
open scoped BigOperators Classical
open Diagram Filter Topology

namespace NorthHistory

lemma mass_tendsto (N : ℕ) :
    Tendsto (fun m : ℕ=>∑ h : NorthHistory N m,h.weight) atTop (𝓝 (realNorthSeparator N)) := by
  simp_rw [sum_weight_source]
  rw [realNorthSeparator,sourceGlue_symmetric]
  simp_rw [sourceGlue_eq_sum]
  apply tendsto_finsetSum
  intro p _
  apply tendsto_finsetSum
  intro q _
  exact (physical_empty_tendsto_source N p).mul
    ((reversed_empty_tendsto_source N q).const_mul _)

end NorthHistory

namespace CrossTopArch
variable {N : ℕ}

lemma weight_nonneg (D : CrossTopArch N) (hN : 1≤N) : 0≤D.weight := by
  rw [weight,←D.arch.weight_toArch hN,(D.arch.toArch hN).weight_eq_path hN (by
    intro he
    have hx:=BoundaryPort.bottom.inj he
    omega)]
  exact (pow_pos rho_pos _).le

lemma Fits.mono {D : CrossTopArch N} {m l : ℕ} (h : D.Fits m) (hm : m≤l) : D.Fits l :=
  HoneycombAssignment.Fits.mono h hm

lemma window_tendsto (N : ℕ) [hN : Fact (1≤N)] :
    Tendsto (fun m : ℕ=>window N m) atTop atTop := by
  apply tendsto_atTop.mpr
  intro F
  let b : CrossTopArch N → ℕ := fun D=>Classical.choose (D.exists_fits hN.out)
  have hb (D : CrossTopArch N) : D.Fits (b D) := Classical.choose_spec (D.exists_fits hN.out)
  apply eventually_atTop.mpr
  refine ⟨F.sup b,?_⟩
  intro m hm D hD
  rw [mem_window]
  exact (hb D).mono ((Finset.le_sup hD).trans hm)

lemma window_mass (N m : ℕ) [hN : Fact (1≤N)] :
    (∑D∈window N m,D.weight)=∑h : NorthHistory N m,h.weight := by
  rw [window,Finset.sum_map,NorthHistory.sum_weight_cross N m hN.out]
  rfl

 

theorem summable_weight (N : ℕ) (hN : 1≤N) : Summable (weight (N:=N)) := by
  let : Fact (1≤N) := ⟨hN⟩
  have hlim : Tendsto (fun m : ℕ=>∑D∈window N m,D.weight) atTop (𝓝 (realNorthSeparator N)) := by
    simpa only [window_mass] using NorthHistory.mass_tendsto N
  apply summable_of_sum_le (fun D=>D.weight_nonneg hN)
  intro F
  apply ge_of_tendsto hlim
  filter_upwards [tendsto_atTop.mp (window_tendsto N) F] with m hm
  exact Finset.sum_le_sum_of_subset_of_nonneg hm (fun D _ _=>D.weight_nonneg hN)



end CrossTopArch
end

 

 

noncomputable section
open scoped Classical BigOperators
open Diagram

namespace TopArchConfiguration
variable {N : ℕ} {a b : ℤ}

lemma weight_nonneg (D : TopArchConfiguration N a b) (hN : 1≤N) (hab : a≠b) :
    0≤D.toHoneycombAssignment.weight := by
  rw [←D.weight_toArch hN,(D.toArch hN).weight_eq_path hN (by
    intro he; have hx:=BoundaryPort.bottom.inj he; omega)]
  exact (pow_pos rho_pos _).le

lemma weight_sum (N : ℕ) (hN : 1≤N) (a b : ℤ) (hab : a≠b) :
    (∑' D : TopArchConfiguration N a b,D.toHoneycombAssignment.weight)=K N (b-a) := by
  rw [HoneycombConfiguration.arch_sum N hN (b-a) (by omega)]
  rw [show (fun D : TopArchConfiguration N a b=>D.toHoneycombAssignment.weight)=
      (fun D : TopArchConfiguration N a b=>(D.toArch hN).weight) from
    funext (fun D=>(D.weight_toArch hN).symm)]
  exact (equivArch N a b hN).tsum_eq HoneycombConfiguration.weight

lemma summable_weight_iff (N : ℕ) (hN : 1≤N) (a b : ℤ) (hab : a≠b) :
    Summable (fun D : TopArchConfiguration N a b=>D.toHoneycombAssignment.weight) ↔
      Summable (archWeight N (b-a)) := by
  rw [HoneycombConfiguration.arch_summable N hN (b-a) (by omega)]
  have hh := (equivArch N a b hN).summable_iff (f:=HoneycombConfiguration.weight)
  have he : HoneycombConfiguration.weight ∘ (equivArch N a b hN)=
      fun D : TopArchConfiguration N a b=>D.toHoneycombAssignment.weight := by
    funext D
    exact D.weight_toArch hN
  rwa [he] at hh

end TopArchConfiguration

namespace CrossTopArch

lemma summable_sigma (N : ℕ) (hN : 1≤N) :
    Summable (fun D : Sigma (fun x : ℕ×ℕ=>TopArchConfiguration N (-1-(x.1:ℤ)) (x.2:ℤ))=>
      D.2.toHoneycombAssignment.weight) :=
  (sigmaEquiv N).summable_iff.mp (summable_weight N hN)

lemma sigma_sums (N : ℕ) (hN : 1≤N) :
    (∀ x : ℕ×ℕ,Summable (fun D : TopArchConfiguration N (-1-(x.1:ℤ)) (x.2:ℤ)=>
      D.toHoneycombAssignment.weight)) ∧
    Summable (fun x : ℕ×ℕ=>K N ((x.1+x.2:ℕ)+1)) := by
  have hh := (summable_sigma_of_nonneg (fun D : Sigma (fun x : ℕ×ℕ=>TopArchConfiguration N (-1-(x.1:ℤ)) (x.2:ℤ))=>
    TopArchConfiguration.weight_nonneg D.2 hN (by omega))).mp (summable_sigma N hN)
  refine ⟨hh.1,hh.2.congr ?_⟩
  intro x
  rw [TopArchConfiguration.weight_sum N hN _ _ (by omega)]
  congr 1
  omega

end CrossTopArch

 

theorem archWeight_summable_positive {N : ℕ} (hN : 1≤N) (k : ℤ) (hk : 0<k) :
    Summable (archWeight N k) := by
  have hh := (TopArchConfiguration.summable_weight_iff N hN
    (-1-((k.toNat-1:ℕ):ℤ)) 0 (by omega)).mp ((CrossTopArch.sigma_sums N hN).1 (k.toNat-1,0))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  omega

theorem archWeight_summable {N : ℕ} (hN : 1≤N) (k : ℤ) : Summable (archWeight N k) := by
  rcases lt_trichotomy k 0 with hk|rfl|hk
  · have hp := archWeight_summable_positive hN (-k) (by omega)
    let e:=mirrorTriangles_involutive.toPerm _
    have hh := (e.summable_iff).mpr hp
    apply hh.congr
    intro p
    exact archWeight_mirror N k p
  · change Summable (fun p : List Triangle=>archWeight N 0 p)
    simp only [archWeight,ne_eq,not_true_eq_false,false_and,ite_false]
    exact summable_zero
  · exact archWeight_summable_positive hN k hk

 

theorem moment_summable {N : ℕ} (hN : 1≤N) :
    Summable (fun k : ℕ=>(k+1:ℝ)*K N (k+1)) := by
  apply (summable_add_diagonal_iff (fun n=>K_nonneg N (n+1))).mp
  exact (CrossTopArch.sigma_sums N hN).2



end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SidePaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators Classical



lemma rotateTriangle_band_lt {H : ℕ} {v : Triangle} (h : v.2.1<H) :
    (rotateTriangle H v).2.1<H := by simp only [rotateTriangle,ite_eq_left h]; omega

lemma rotateTriangle_involutive (H : ℕ) : Function.Involutive (rotateTriangle H) := by
  intro v
  by_cases h : v.2.1<H
  · have h' : H-1-v.2.1<H := by omega
    have he : H-1-(H-1-v.2.1)=v.2.1 := by omega
    simp [rotateTriangle,h,h',he]
  · simp [rotateTriangle,h]

lemma adjacent_rotate_iff {H : ℕ} {v w : Triangle} (hv : v.2.1<H) (hw : w.2.1<H) :
    adjacent (rotateTriangle H v) (rotateTriangle H w) ↔ adjacent v w := by
  rcases v with ⟨i,j,b⟩
  rcases w with ⟨i',j',b'⟩
  change j<H at hv
  change j'<H at hw
  cases b <;> cases b' <;> simp [adjacent,upDownAdjacent,rotateTriangle,hv,hw]
  all_goals omega

lemma PathBetween.rotate {H : ℕ} {a b : Triangle} {p : List Triangle}
    (hp : PathBetween H a b p) :
    PathBetween H (rotateTriangle H a) (rotateTriangle H b) (p.map (rotateTriangle H)) := by
  refine ⟨?_,?_,hp.2.2.1.map (rotateTriangle_involutive H).injective,?_,?_⟩
  · rw [List.head?_map,hp.1]; rfl
  · rw [List.getLast?_map,hp.2.1]; rfl
  · apply (List.isChain_map _).mpr
    apply hp.2.2.2.1.imp_of_mem_imp
    intro v w hv hw h
    exact (adjacent_rotate_iff (hp.2.2.2.2 v hv) (hp.2.2.2.2 w hw)).mpr h
  · intro v hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
    exact rotateTriangle_band_lt (hp.2.2.2.2 w hw)

lemma PathBetween.append_vertex {H : ℕ} {a b v : Triangle} {p : List Triangle}
    (hp : PathBetween H a b p) (hv : v.2.1<H) (hn : v∉p) (hab : adjacent b v) :
    PathBetween H a v (p++[v]) := by
  refine ⟨?_,by simp,?_,?_,?_⟩
  · rw [List.head?_append,hp.1]; rfl
  · apply List.nodup_append.mpr
    refine ⟨hp.2.2.1,by simp,?_⟩
    intro x hx y hy hxy
    have hyv := List.mem_singleton.mp hy
    exact hn ((hxy.trans hyv) ▸ hx)
  · apply List.isChain_append.mpr
    refine ⟨hp.2.2.2.1,by simp,?_⟩
    simpa [hp.2.1] using hab
  · intro w hw
    rcases List.mem_append.mp hw with hw|hw
    · exact hp.2.2.2.2 w hw
    · simpa using List.mem_singleton.mp hw ▸ hv



lemma stepSideWeight_nonneg (N : ℕ) (s i : ℤ) (p : List Triangle) :
    0 ≤ stepSideWeight N s i p := by
  unfold stepSideWeight
  split
  · exact (pow_pos rho_pos _).le
  · exact le_rfl



lemma sideToTallBridge_injective (N : ℕ) (s : ℤ) :
    Function.Injective (sideToTallBridge N s) := by
  intro p q h
  have h₁ := List.map_injective_iff.mpr (translateTriangle_injective (s-1))
  have h₂ := List.map_injective_iff.mpr (rotateTriangle_involutive (N+1)).injective
  unfold sideToTallBridge at h
  exact List.append_cancel_right ((List.reverse_inj).mp (h₂ (h₁ h)))

lemma sideToTallBridge_spec {N : ℕ} (s i : ℤ) {p : List Triangle}
    (hp : PathBetween (N+1) (up i 0) (up s N) p)
    (hD : ∀ v∈p,steppedDomain N s v) :
    IsPath (N+1) (down (s-1-i) N) (sideToTallBridge N s p) := by
  have hn : down (s-1) N ∉ p := by
    intro h
    have hh := hD _ h
    simp only [steppedDomain,down,lt_self_iff_false,false_or,true_and] at hh
    omega
  have hA : adjacent (up s N) (down (s-1) N) := by
    apply Or.inl
    exact ⟨rfl,rfl,Or.inl ⟨rfl,Or.inr (by change s-1+1=s; omega)⟩⟩
  have he := ((hp.append_vertex (Nat.lt_succ_self N) hn hA).reverse.rotate).translate (s-1)
  have h₀ : 0<N+1 := by omega
  simpa [sideToTallBridge,rotateTriangle_down,rotateTriangle_up,h₀,
    Nat.lt_succ_self,sub_eq_add_neg,add_assoc,add_comm,add_left_comm] using he

lemma sideToTallBridge_weight (N : ℕ) (s i : ℤ) (p : List Triangle) :
    rho * stepSideWeight N s i p ≤ bridgeWeight (N+1) (s-1-i) (sideToTallBridge N s p) := by
  unfold stepSideWeight
  split_ifs with hp
  · rw [bridgeWeight,ite_eq_left ⟨by omega,sideToTallBridge_spec s i hp.1 hp.2⟩]
    simp [sideToTallBridge,pow_succ,mul_comm]
  · simp only [mul_zero]
    exact bridgeWeight_nonneg _ _ _

lemma bridge_all_paths_summable {H : ℕ} (hH : StripSumsFinite H) :
    Summable (fun x : ℤ×List Triangle => bridgeWeight H x.1 x.2) := by
  apply (summable_prod_of_nonneg (fun x => bridgeWeight_nonneg _ _ _)).mpr
  exact ⟨hH.2.1,hH.2.2.2.1⟩



theorem stepSideWeight_summable {N : ℕ} (s : ℤ) (h : StripSumsFinite (N+1)) :
    Summable (fun x : ℤ×List Triangle =>stepSideWeight N s x.1 x.2) := by
  let e : (ℤ×List Triangle) → (ℤ×List Triangle) :=
    fun x => (s-1-x.1,sideToTallBridge N s x.2)
  have he : Function.Injective e := by
    intro x y h
    have hi := congrArg Prod.fst h
    have hp := (sideToTallBridge_injective N s) (congrArg Prod.snd h)
    have hxy : x.1=y.1 := by dsimp [e] at hi; omega
    exact Prod.ext hxy hp
  have hg := (bridge_all_paths_summable h).comp_injective he
  have hmul : Summable (fun x : ℤ×List Triangle =>rho * stepSideWeight N s x.1 x.2) :=
    hg.of_nonneg_of_le (fun x =>mul_nonneg rho_pos.le (stepSideWeight_nonneg _ _ _ _))
      (fun x =>sideToTallBridge_weight N s x.1 x.2)
  exact (summable_mul_left_iff rho_pos.ne').mp hmul

end




end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_BridgeUnfold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators


lemma prepareBridge_injective : Function.Injective prepareBridge := by
  intro p q h
  exact List.map_injective_iff.mpr raiseTriangle_injective ((List.cons.inj (List.cons.inj h).2).2)







lemma PathBetween.append {H : ℕ} {a b c d : Triangle} {p q : List Triangle}
    (hp : PathBetween H a b p) (hq : PathBetween H c d q)
    (hd : List.Disjoint p q) (hbc : adjacent b c) :
    PathBetween H a d (p++q) := by
  refine ⟨?_,?_,List.nodup_append.mpr ⟨hp.2.2.1,hq.2.2.1,?_⟩,?_,?_⟩
  · rw [List.head?_append,hp.1]; rfl
  · rw [List.getLast?_append,hq.2.1]; rfl
  · intro x hx y hy he
    exact List.disjoint_left.mp hd hx (he ▸ hy)
  · apply List.isChain_append.mpr
    refine ⟨hp.2.2.2.1,hq.2.2.2.1,?_⟩
    intro x hx y hy
    have he : b=x := by simpa only [hp.2.1,Option.mem_some_iff] using hx
    have he' : c=y := by simpa only [hq.1,Option.mem_some_iff] using hy
    exact he ▸ he' ▸ hbc
  · intro v hv
    rcases List.mem_append.mp hv with hv|hv
    · exact hp.2.2.2.2 v hv
    · exact hq.2.2.2.2 v hv

namespace BridgeCut
section TraceRealizations
variable {H : ℕ} {k : ℤ} {p : List Triangle}

lemma height_pos (D : BridgeCut H k p) : 0<H := by have :=D.row_lt; omega

lemma end_le (D : BridgeCut H k p) : k≤D.column :=
  D.right_le _ (List.mem_of_mem_getLast? (by rw [D.right_path.2.1]; rfl))

lemma right_ne_nil (D : BridgeCut H k p) : D.right≠[] := by
  intro he
  have hh:=D.right_path.1
  rw [he] at hh
  contradiction



lemma move_col (D : BridgeCut H k p) {v : Triangle} (hv : v.2.1<H) :
    (D.move v).1=2*D.column+2-v.1 := by simp [move,translateTriangle,rotateTriangle,hv,sub_eq_add_neg]

lemma move_injective (D : BridgeCut H k p) : Function.Injective D.move :=
  (translateTriangle_injective _).comp (rotateTriangle_involutive H).injective

lemma moved_path (D : BridgeCut H k p) :
    PathBetween H (up (D.column+2) (H-1-D.row)) (up (2*D.column+2-k) 0)
      (D.right.map D.move) := by
  change PathBetween H _ _ (D.right.map (fun v=>translateTriangle (2*D.column+2) (rotateTriangle H v)))
  have hh:=(D.right_path.rotate).translate (2*D.column+2)
  simpa only [rotateTriangle_down _ _ D.row_lt,
    rotateTriangle_down _ _ (by have :=D.height_pos; omega : H-1<H),
    Nat.sub_self,translateTriangle_up,List.map_map,Function.comp_def,
    show 2*D.column+2+-D.column=D.column+2 by ring,
    show 2*D.column+2+-k=2*D.column+2-k by ring,move] using hh

lemma moved_ge (D : BridgeCut H k p) : ∀v∈D.right.map D.move,D.column+2≤v.1 := by
  intro v hv
  obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hv
  rw [D.move_col (D.right_path.2.2.2.2 w hw)]
  have :=D.right_le w hw
  omega

lemma connector_spec (D : BridgeCut H k p) :
    PathBetween H (up (D.column+1) D.row) (down (D.column+1) (H-1-D.row)) D.connector ∧
      (∀v∈D.connector,v.1=D.column+1) ∧ D.connector.length≤2*H := D.connector_exists.choose_spec


lemma arch_path (D : BridgeCut H k p) :
    IsPath H (up (2*D.column+2-k) 0) D.arch := by
  have hc:=D.connector_spec
  have hl : PathBetween H (up 0 0) (down (D.column+1) (H-1-D.row)) (D.left++D.connector) := by
    apply D.left_path.append hc.1
    · apply List.disjoint_left.mpr
      intro v hv hv'
      have h₁:=D.left_le v hv
      have h₂:=hc.2.1 v hv'
      omega
    · simp [adjacent,upDownAdjacent,up,down]
  apply hl.append D.moved_path
  · apply List.disjoint_left.mpr
    intro v hv hv'
    have hg:=D.moved_ge v hv'
    rcases List.mem_append.mp hv with hv|hv
    · have := D.left_le v hv; omega
    · have :=hc.2.1 v hv; omega
  · simp [adjacent,upDownAdjacent,up,down]
    omega

lemma arch_length (D : BridgeCut H k p) : D.arch.length≤p.length+(2*H+1) := by
  have he:=congrArg List.length D.reconstruct
  have hc:=D.connector_spec.2.2
  have hn : 0<D.right.length := List.length_pos_iff.mpr D.right_ne_nil
  simp only [List.length_append,List.length_tail] at he
  simp only [arch,List.length_append,List.length_map]
  omega

 

lemma arch_filter_left (D : BridgeCut H k p) :
    D.arch.filter (fun v=>decide (v.1≤D.column))=D.left := by
  have hl : D.left.filter (fun v=>decide (v.1≤D.column))=D.left :=
    List.filter_eq_self.mpr (fun v hv=>by simpa using D.left_le v hv)
  have hc : D.connector.filter (fun v=>decide (v.1≤D.column))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro v hv
    have :=D.connector_spec.2.1 v hv
    simp only [decide_eq_true_eq]
    omega
  have hr : (D.right.map D.move).filter (fun v=>decide (v.1≤D.column))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro v hv
    have :=D.moved_ge v hv
    simp only [decide_eq_true_eq]
    omega
  simp only [arch,List.filter_append,hl,hc,hr,List.append_nil]

lemma arch_filter_right (D : BridgeCut H k p) :
    D.arch.filter (fun v=>decide (D.column+2≤v.1))=D.right.map D.move := by
  have hl : D.left.filter (fun v=>decide (D.column+2≤v.1))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro v hv
    have :=D.left_le v hv
    simp only [decide_eq_true_eq]
    omega
  have hc : D.connector.filter (fun v=>decide (D.column+2≤v.1))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro v hv
    have :=D.connector_spec.2.1 v hv
    simp only [decide_eq_true_eq]
    omega
  have hr : (D.right.map D.move).filter (fun v=>decide (D.column+2≤v.1))=D.right.map D.move :=
    List.filter_eq_self.mpr (fun v hv=>by simpa using D.moved_ge v hv)
  simp only [arch,List.filter_append,hl,hc,hr,List.nil_append]

end TraceRealizations

 

 


lemma recover {H : ℕ} {k l : ℤ} {p q : List Triangle}
    (D : BridgeCut H k p) (E : BridgeCut H l q)
    (hcol : D.column=E.column) (ha : D.arch=E.arch) : p=q := by
  have hl : D.left=E.left := by
    rw [←D.arch_filter_left,ha,hcol,E.arch_filter_left]
  have hr : D.right.map D.move=E.right.map E.move := by
    rw [←D.arch_filter_right,ha,hcol,E.arch_filter_right]
  have he : E.move=D.move := by funext v; simp only [move,hcol]
  rw [he] at hr
  have hr' := List.map_injective_iff.mpr D.move_injective hr
  rw [D.reconstruct,E.reconstruct,hl,hr']
end BridgeCut


namespace BridgePath
variable {N : ℕ}

lemma toCutArch_injective (hN : 1≤N) : Function.Injective (toCutArch hN) := by
  intro x y he
  have hm : (x.cut hN).column=(y.cut hN).column := by
    have hh:=congrArg (fun z : (ℕ×ℕ)×List Triangle=>z.1.1) he
    change (x.cut hN).column.toNat=(y.cut hN).column.toNat at hh
    have h₁:=(x.cut hN).column_nonneg
    have h₂:=(y.cut hN).column_nonneg
    omega
  have ha : (x.cut hN).arch=(y.cut hN).arch := by
    have hh:=congrArg Prod.snd he
    change (x.cut hN).arch.map (translateTriangle (-(x.cut hN).column))=
      (y.cut hN).arch.map (translateTriangle (-(y.cut hN).column)) at hh
    rw [hm] at hh
    exact List.map_injective_iff.mpr (translateTriangle_injective _) hh
  have hp := prepareBridge_injective ((x.cut hN).recover (y.cut hN) hm ha)
  apply Subtype.ext
  apply Prod.ext ?_ hp
  have hx:=x.property.2.1
  have hy:=y.property.2.1
  rw [hp,hy] at hx
  exact (congrArg Prod.fst (Option.some.inj hx)).symm

lemma toCutArch_path (hN : 1≤N) (x : BridgePath N) :
    PathBetween (N+1) (up (-((toCutArch hN x).1.1:ℤ)) 0)
      (up (((toCutArch hN x).1.2:ℤ)+1) 0) (toCutArch hN x).2 := by
  let D:=x.cut hN
  have hM : (D.column.toNat:ℤ)=D.column := Int.toNat_of_nonneg D.column_nonneg
  have he : ((D.column+1-x.val.1).toNat:ℤ)=D.column+1-x.val.1 :=
    Int.toNat_of_nonneg (by have :=D.end_le; omega)
  have hh:=(show PathBetween (N+1) (up 0 0) (up (2*D.column+2-x.val.1) 0) D.arch from
    D.arch_path).translate (-D.column)
  change PathBetween _ (up (-(D.column.toNat:ℤ)) 0)
    (up (((D.column+1-x.val.1).toNat:ℤ)+1) 0) (D.arch.map (translateTriangle (-D.column)))
  simpa only [translateTriangle_up,hM,he,add_zero,
    show -D.column+(2*D.column+2-x.val.1)=D.column+1-x.val.1+1 by ring] using hh

lemma rho_le_one : rho≤1 := by nlinarith [rho_pos,rho_sq_lt_one]

lemma toCutArch_weight_bound (hN : 1≤N) (x : BridgePath N) :
    rho^(2*(N+1)+3)*rho^x.val.2.length ≤ cutArchWeight (N+1) (toCutArch hN x) := by
  have hp:=toCutArch_path hN x
  rw [cutArchWeight,betweenArchWeight,ite_eq_left ⟨by omega,hp⟩,←pow_add]
  apply pow_le_pow_of_le_one rho_pos.le rho_le_one
  have hl:=(x.cut hN).arch_length
  simp only [prepareBridge_length] at hl
  change ((x.cut hN).arch.map _).length≤_
  rw [List.length_map]
  omega

 

theorem summable_weight (hN : 1≤N) : Summable (fun x : BridgePath N=>rho^x.val.2.length) := by
  have ht := (cutArchWeight_summable_iff (N+1) (archWeight_summable (by omega))).mpr
    (moment_summable (by omega))
  have hs:=ht.comp_injective (toCutArch_injective hN)
  have hb : Summable (fun x : BridgePath N=>rho^(2*(N+1)+3)*rho^x.val.2.length) :=
    Summable.of_nonneg_of_le (fun _=>by positivity [rho_pos]) (toCutArch_weight_bound hN) hs
  exact (summable_mul_left_iff (pow_ne_zero _ rho_pos.ne')).mp hb
end BridgePath

theorem summable_bridgeWeight {N : ℕ} (hN : 1≤N) :
    Summable (fun x : ℤ×List Triangle=>bridgeWeight N x.1 x.2) := by
  have hh:= (summable_subtype_iff_indicator
    (f:=fun x : ℤ×List Triangle=>rho^x.2.length)
    (s:={x : ℤ×List Triangle | IsPath N (down x.1 (N-1)) x.2})).mp
      (BridgePath.summable_weight hN)
  apply hh.congr
  intro x
  dsimp [Set.indicator]
  unfold bridgeWeight
  split_ifs <;> simp_all

 

theorem stripSumsFinite {N : ℕ} (hN : 1≤N) : StripSumsFinite N := by
  have hb:=(summable_prod_of_nonneg (fun x : ℤ×List Triangle=>bridgeWeight_nonneg N x.1 x.2)).mp
    (summable_bridgeWeight hN)
  exact ⟨archWeight_summable hN,hb.1,summable_K_of_moment (moment_summable hN),hb.2,moment_summable hN⟩

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_RibbonGlobal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators



namespace HoneycombBranch
open FiniteBranchTree

lemma terminal_eq_of_visited {s : State} {l m : List Bool} (hl : l≠[]) (hm : m≠[])
    (hv : visited Prod.fst next s l=visited Prod.fst next s m)
    (hp : (terminal next s l).2=(terminal next s m).2) :
    terminal next s l=terminal next s m := by
  have he:=congrArg List.getLast? hv
  rw [(visited_head_last s l hl).2,(visited_head_last s m hm).2] at he
  have hb : back (terminal next s l)=back (terminal next s m) := Prod.ext (Option.some.inj he) hp
  have ht:=congrArg back hb
  simpa only [back_back] using ht



namespace SideWord
variable {H : ℕ} {i k : ℤ}

lemma path_spec (x : SideWord H i k) :
    PathBetween H (up i 0) (retractVertex (back x.state).1) x.path := by
  apply visited_retract_path H _ _ (bottom i) x.val x.property.1 rfl
    (by apply (embed_retract _ _).symm; exact (x.property.2.2.1 _ (lastVisited_mem _ _ x.property.1)).1)
    x.property.2.1
  intro v hv
  exact ⟨(x.property.2.2.1 v hv).1,(x.property.2.2.1 v hv).2.1⟩

lemma path_no_column (x : SideWord H i k) : ∀v∈x.path,v.1≠k := by
  intro v hv
  obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hv
  exact (x.property.2.2.1 w hw).2.2

 lemma connector_spec (x : SideWord H i k) :
    PathBetween H (retractVertex x.state.1) (up k 0) x.connector ∧
      (∀v∈x.connector,v.1=k) ∧ x.connector.length≤2*H := x.connector_exists.choose_spec

lemma arch_spec (x : SideWord H i k) : PathBetween H (up i 0) (up k 0) x.arch := by
  apply x.path_spec.append x.connector_spec.1
  · apply List.disjoint_left.mpr
    intro v hv hv'
    exact x.path_no_column v hv (x.connector_spec.2.1 v hv')
  · apply (adjacent_iff _ _).mpr
    have hb : 0≤(back x.state).1.2.1 := (x.property.2.2.1 _ (lastVisited_mem _ _ x.property.1)).1
    rw [embed_retract _ hb,embed_retract _ x.band.1]
    exact ⟨x.state.2,neighbor_reverse _ _⟩

lemma arch_filter (x : SideWord H i k) :
    x.arch.filter (fun v=>decide (v.1≠k))=x.path := by
  have hp : x.path.filter (fun v=>decide (v.1≠k))=x.path :=
    List.filter_eq_self.mpr (fun v hv=>by simpa using x.path_no_column v hv)
  have hc : x.connector.filter (fun v=>decide (v.1≠k))=[] :=
    List.filter_eq_nil_iff.mpr (fun v hv=>by simp [x.connector_spec.2.1 v hv])
  simp only [arch,List.filter_append,hp,hc,List.append_nil]

lemma path_embed (x : SideWord H i k) :
    x.path.map embedTriangle=visited Prod.fst next (bottom i) x.val := by
  rw [path,List.map_map]
  conv_rhs => rw [←List.map_id (visited Prod.fst next (bottom i) x.val)]
  apply List.map_congr_left
  intro v hv
  exact embed_retract v (x.property.2.2.1 v hv).1

lemma arch_injective : Function.Injective (arch (H:=H) (i:=i) (k:=k)) := by
  intro x y he
  have hp : x.path=y.path := by rw [←x.arch_filter,he,y.arch_filter]
  have hv : visited Prod.fst next (bottom i) x.val=visited Prod.fst next (bottom i) y.val := by
    rw [←x.path_embed,hp,y.path_embed]
  apply Subtype.ext
  apply word_unique _ _ _ hv
  apply terminal_eq_of_visited x.property.1 y.property.1 hv
  exact x.property.2.2.2.1.trans y.property.2.2.2.1.symm

lemma arch_length (x : SideWord H i k) : x.arch.length≤x.val.length+2*H := by
  simp only [arch,List.length_append,path,List.length_map,visited_length]
  have :=x.connector_spec.2.2
  omega

lemma weighted_bound (hik : i≠k) (x : SideWord H i k) :
    rho^(2*H)*rho^x.val.length≤betweenArchWeight H i k x.arch := by
  rw [betweenArchWeight,ite_eq_left ⟨hik,x.arch_spec⟩,←pow_add]
  exact pow_le_pow_of_le_one rho_pos.le BridgePath.rho_le_one (by have:=x.arch_length; omega)

lemma sum_le (hH : 1≤H) (hik : i≠k) (F : Finset (SideWord H i k)) :
    ∑ x∈F,rho^x.val.length ≤ (rho^(2*H))⁻¹*K H (k-i) := by
  have hs := (summable_betweenArchWeight_iff H i k).mpr ((stripSumsFinite hH).1 _)
  have hi : Summable (fun x : SideWord H i k=>betweenArchWeight H i k x.arch) :=
    hs.comp_injective arch_injective
  have hh : rho^(2*H)*(∑ x∈F,rho^x.val.length)≤K H (k-i) := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ x∈F,betweenArchWeight H i k x.arch := Finset.sum_le_sum (fun x _=>weighted_bound hik x)
      _ ≤ ∑' x : SideWord H i k,betweenArchWeight H i k x.arch :=
        hi.sum_le_tsum F (fun x _=>betweenArchWeight_nonneg _ _ _ _)
      _ ≤ ∑' p,betweenArchWeight H i k p :=
        tsum_comp_le_tsum_of_inj hs (betweenArchWeight_nonneg H i k) arch_injective
      _ = K H (k-i) := betweenArchKernel_eq H i k
  have hh' : (∑ x∈F,rho^x.val.length)≤K H (k-i)/rho^(2*H) :=
    (le_div_iff₀ (pow_pos rho_pos _)).mpr (by simpa only [mul_comm] using hh)
  simpa only [div_eq_mul_inv,mul_comm] using hh'

end SideWord
end HoneycombBranch
end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_FluxWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.HoneycombBranch
noncomputable section
open scoped Classical BigOperators
open FiniteBranchTree Filter Topology


lemma source_clip {D : Vertex→Prop} {H : ℕ} (hH : 1≤H) {i : ℤ}
    (hi : D (bottom i).1) (m : ℕ) : (bottom i).1∈clip D H i m := by
  simp only [clip,Finset.mem_filter,mem_window,bottom]
  exact ⟨⟨by omega,by omega,by omega,by omega⟩,hi⟩

lemma finiteExit_nonempty {D : Vertex→Prop} {H : ℕ} (hH : 1≤H) {i : ℤ}
    (hi : D (bottom i).1) {m : ℕ} {l : List Bool} (hl : l∈finiteExits D H i m) : l≠[] := by
  intro he
  subst l
  exact (Finset.mem_filter.mp hl).2 (source_clip hH hi m)

lemma physicalExit_isExit {D : Vertex→Prop} {H : ℕ} (hH : 1≤H) {i : ℤ}
    (hi : D (bottom i).1) {m : ℕ} {l : List Bool} (hl : l∈physicalExits D H i m) : IsExit D i l := by
  obtain ⟨he,ht⟩:=Finset.mem_filter.mp hl
  refine ⟨finiteExit_nonempty hH hi he,visited_nodup Prod.fst next (Finset.mem_filter.mp he).1,?_,ht⟩
  intro v hv
  exact (Finset.mem_filter.mp (visited_mem_domain Prod.fst next (Finset.mem_filter.mp he).1 v hv)).2

lemma eventually_window {H : ℕ} {i : ℤ} {v : Vertex} (hv : 0≤v.2.1 ∧ v.2.1<(H:ℤ)) :
    ∀ᶠ m : ℕ in atTop,v∈window H i m := by
  filter_upwards [eventually_ge_atTop ((v.1-i).natAbs+1)] with m hm
  rw [mem_window]
  have ha : v.1-i≤((v.1-i).natAbs:ℤ) := Int.le_natAbs
  have hb : -(v.1-i)≤((v.1-i).natAbs:ℤ) := by simpa only [Int.natAbs_neg] using (Int.le_natAbs : -(v.1-i)≤((-(v.1-i)).natAbs:ℤ))
  exact ⟨by omega,by omega,hv⟩

lemma eventually_physicalExit {D : Vertex→Prop} {H : ℕ} {i : ℤ}
    (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) {l : List Bool} (hl : IsExit D i l) :
    ∀ᶠ m : ℕ in atTop,l∈physicalExits D H i m := by
  have he : ∀ᶠ m : ℕ in atTop,∀v∈(visited Prod.fst next (bottom i) l).toFinset,v∈window H i m := by
    apply (Finset.eventually_all _).mpr
    intro v hv
    exact eventually_window (hD v (hl.2.2.1 v (List.mem_toFinset.mp hv)))
  filter_upwards [he] with m hm
  have hout : (terminal next (bottom i) l).1∉clip D H i m := by
    intro hx; exact hl.2.2.2 (Finset.mem_filter.mp hx).2
  have hw : l∈words (clip D H i m) (bottom i) := by
    apply (mem_leaves_iff _ _ _ _ _).mpr
    exact ⟨hl.2.1,fun v hv=>Finset.mem_filter.mpr ⟨hm v (List.mem_toFinset.mpr hv),hl.2.2.1 v hv⟩,Or.inl hout⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hw,hout⟩,hl.2.2.2⟩

lemma physicalExit_limit {D : Vertex→Prop} {H : ℕ} (hH : 1≤H) {i : ℤ}
    (hi : D (bottom i).1) (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ))
    (hs : Summable (exitWeight D i)) :
    Tendsto (fun m : ℕ=>∑l∈physicalExits D H i m,wordWeight factor l)
      atTop (𝓝 (∑'l,exitWeight D i l)) := by
  have he (m : ℕ) : (∑l∈physicalExits D H i m,wordWeight factor l)=
      ∑'l,if l∈physicalExits D H i m then wordWeight factor l else 0 := by
    symm
    rw [tsum_eq_sum (s:=physicalExits D H i m) (fun l hl=>ite_eq_right hl)]
    apply Finset.sum_congr rfl
    intro l hl
    rw [ite_eq_left hl]
  simp_rw [he]
  apply tendsto_tsum_of_dominated_convergence hs.norm
  · intro l
    by_cases hl : IsExit D i l
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_physicalExit hD hl] with m hm
      simp [exitWeight,hl,hm]
    · apply tendsto_const_nhds.congr'
      apply Eventually.of_forall
      intro m
      have hn : l∉physicalExits D H i m := fun hm=>hl (physicalExit_isExit hH hi hm)
      simp [exitWeight,hl,hn]
  · apply Eventually.of_forall
    intro m l
    split_ifs with hl
    · rw [exitWeight,ite_eq_left (physicalExit_isExit hH hi hl)]
    · simpa only [norm_zero] using norm_nonneg (exitWeight D i l)

lemma crossing_column {H : ℕ} {i : ℤ} {m : ℕ} {s : State}
    (hp : (back s).1∈window H i m) (hs : 0 ≤ s.1.2.1 ∧ s.1.2.1 < (H:ℤ))
    (hn : s.1∉window H i m) : s.2=1 ∧ (s.1.1=i-(m:ℤ)-1 ∨ s.1.1=i+(m:ℤ)+1) := by
  rcases s with ⟨⟨k,r,b⟩,p⟩
  fin_cases p <;> cases b <;> simp [mem_window,back,neighbor] at hp hs hn ⊢ <;> omega

lemma sideExit_column {D : Vertex→Prop} {H : ℕ} (hH : 1≤H) {i : ℤ}
    (hi : D (bottom i).1) (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) {m : ℕ} {l : List Bool}
    (hl : l∈sideExits D H i m) :
    (terminal next (bottom i) l).2=1 ∧
    ((terminal next (bottom i) l).1.1=i-(m:ℤ)-1 ∨ (terminal next (bottom i) l).1.1=i+(m:ℤ)+1) := by
  obtain ⟨he,hd⟩:=Finset.mem_filter.mp hl
  obtain ⟨hw,hn⟩:=Finset.mem_filter.mp he
  apply crossing_column
    (Finset.mem_filter.mp (visited_mem_domain Prod.fst next hw _
      (lastVisited_mem _ _ (finiteExit_nonempty hH hi he)))).1 (hD _ hd)
  intro hm
  exact hn (Finset.mem_filter.mpr ⟨hm,hd⟩)

lemma sideExit_spec {D : Vertex→Prop} {H : ℕ} (hH : 1≤H) {i k : ℤ}
    (hi : D (bottom i).1) (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) {m : ℕ} {l : List Bool}
    (hl : l∈sideExits D H i m) (hk : (terminal next (bottom i) l).1.1=k) :
    l≠[] ∧ (visited Prod.fst next (bottom i) l).Nodup ∧
    (∀v∈visited Prod.fst next (bottom i) l,0≤v.2.1 ∧ v.2.1<(H:ℤ) ∧ v.1≠k) ∧
    (terminal next (bottom i) l).2=1 ∧ (terminal next (bottom i) l).1.1=k := by
  have he := (Finset.mem_filter.mp hl).1
  have hw := (Finset.mem_filter.mp he).1
  have hc:=sideExit_column hH hi hD hl
  refine ⟨finiteExit_nonempty hH hi he,visited_nodup Prod.fst next hw,?_,hc.1,hk⟩
  intro v hv
  have hm:=Finset.mem_filter.mp (visited_mem_domain Prod.fst next hw v hv)
  have hb:=hD _ hm.2
  have hcol:=(mem_window H i m v).mp hm.1
  exact ⟨hb.1,hb.2,by rcases hc.2 with hc|hc <;> omega⟩

lemma side_sum_bound {D : Vertex→Prop} {H : ℕ} (hH : 1≤H) {i k : ℤ}
    (hi : D (bottom i).1) (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) {m : ℕ}
    (F : Finset (List Bool)) (hF : F⊆sideExits D H i m)
    (hk : ∀l∈F,(terminal next (bottom i) l).1.1=k) (hik : i≠k) :
    ∑l∈F,rho^l.length ≤ (rho^(2*H))⁻¹*K H (k-i) := by
  let e : F→SideWord H i k:=fun l=>⟨l.val,sideExit_spec hH hi hD (hF l.property) (hk l.val l.property)⟩
  have he : Function.Injective e := by intro l n h; apply Subtype.ext; exact congrArg (fun x : SideWord H i k=>x.val) h
  have hs:=SideWord.sum_le hH hik (Finset.univ.image e)
  rw [Finset.sum_image (fun x _ y _ h=>he h)] at hs
  change (∑x : F,rho^x.val.length)≤_ at hs
  rw [←Finset.sum_coe_sort F (fun l : List Bool=>rho^l.length)]
  exact hs

lemma sideExit_bound {D : Vertex→Prop} {H : ℕ} (hH : 1≤H) {i : ℤ}
    (hi : D (bottom i).1) (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) (m : ℕ) :
    ‖∑l∈sideExits D H i m,wordWeight factor l‖ ≤
      (rho^(2*H))⁻¹*(K H (-(m:ℤ)-1)+K H ((m:ℤ)+1)) := by
  have hl:=side_sum_bound hH hi hD
    ((sideExits D H i m).filter (fun l=>(terminal next (bottom i) l).1.1=i-(m:ℤ)-1))
    (Finset.filter_subset _ _) (fun l hl=>(Finset.mem_filter.mp hl).2) (by omega : i≠i-(m:ℤ)-1)
  have hr:=side_sum_bound hH hi hD
    ((sideExits D H i m).filter (fun l=>¬(terminal next (bottom i) l).1.1=i-(m:ℤ)-1))
    (Finset.filter_subset _ _) (fun l hl=>(sideExit_column hH hi hD (Finset.mem_filter.mp hl).1).2.resolve_left
      (Finset.mem_filter.mp hl).2) (by omega : i≠i+(m:ℤ)+1)
  have hs:=Finset.sum_filter_add_sum_filter_not (sideExits D H i m)
    (fun l=>(terminal next (bottom i) l).1.1=i-(m:ℤ)-1) (fun l : List Bool=>rho^l.length)
  calc
    _ ≤ ∑l∈sideExits D H i m,‖wordWeight factor l‖ := norm_sum_le _ _
    _ = ∑l∈sideExits D H i m,rho^l.length := by simp only [wordWeight_norm]
    _ ≤ _ := by
      rw [←hs]
      have he₁ : i-(m:ℤ)-1-i= -(m:ℤ)-1 := by ring
      have he₂ : i+(m:ℤ)+1-i=(m:ℤ)+1 := by ring
      rw [he₁] at hl
      rw [he₂] at hr
      simpa only [mul_add] using add_le_add hl hr



theorem infinite_boundary_flux {D : Vertex→Prop} {H : ℕ} (hH : 1≤H) {i : ℤ}
    (hi : D (bottom i).1) (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ))
    (hs : Summable (exitWeight D i)) : ∑'l,exitWeight D i l=1 := by
  have hleft : Summable (fun m : ℕ=>K H (-(m:ℤ)-1)) :=
    (stripSumsFinite hH).2.2.1.comp_injective (i:=fun m : ℕ=> -(m:ℤ)-1) (by intro m n he; dsimp at he; omega)
  have hright : Summable (fun m : ℕ=>K H ((m:ℤ)+1)) :=
    (stripSumsFinite hH).2.2.1.comp_injective (i:=fun m : ℕ=> (m:ℤ)+1) (by intro m n he; dsimp at he; omega)
  have hb : Tendsto (fun m : ℕ=>(rho^(2*H))⁻¹*(K H (-(m:ℤ)-1)+K H ((m:ℤ)+1))) atTop (𝓝 0) := by
    simpa using (hleft.tendsto_atTop_zero.add hright.tendsto_atTop_zero).const_mul ((rho^(2*H))⁻¹)
  have hz : Tendsto (fun m : ℕ=>∑l∈sideExits D H i m,wordWeight factor l) atTop (𝓝 0) :=
    squeeze_zero_norm (fun m=>sideExit_bound hH hi hD m) hb
  have ht:=(physicalExit_limit hH hi hD hs).add hz
  simp only [add_zero] at ht
  have hc : Tendsto (fun m : ℕ=>(∑l∈physicalExits D H i m,wordWeight factor l)+
      (∑l∈sideExits D H i m,wordWeight factor l)) atTop (𝓝 1) := by
    simpa only [finite_split hD] using (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(1:ℂ)) atTop (𝓝 1))
  exact tendsto_nhds_unique ht hc

end

 

 

noncomputable section
open scoped Classical BigOperators
open FiniteBranchTree


variable {D : Vertex→Prop} {B : Type*} (P : BoundaryPorts D B) {H : ℕ} {i : ℤ}

lemma boundaryPathWeight_nonneg (H : ℕ) (i : ℤ) (x : B×List Triangle) :
    0≤boundaryPathWeight P H i x := by
  unfold boundaryPathWeight
  split_ifs <;> positivity [rho_pos]

lemma exitPathEquiv_length (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) (x : ExitWord D i) :
    (exitPathEquiv P hD x).val.2.length=x.val.length := by
  change ((visited Prod.fst next (bottom i) x.val).map retractVertex).length=x.val.length
  simp only [List.length_map,visited_length]

lemma boundaryPath_summable_iff :
    Summable (fun x : BoundaryPath P H i=>rho^x.val.2.length) ↔ Summable (boundaryPathWeight P H i) := by
  change Summable (fun x : {x | ValidBoundaryPath P H i x}=>rho^x.val.2.length) ↔ _
  exact summable_subtype_iff_indicator (s:={x | ValidBoundaryPath P H i x})
    (f:=fun x : B×List Triangle=>rho^x.2.length)

lemma exitWord_summable_iff :
    Summable (fun x : ExitWord D i=>rho^x.val.length) ↔
    Summable (fun l=>if IsExit D i l then rho^l.length else 0) := by
  exact summable_subtype_iff_indicator (s:={l | IsExit D i l}) (f:=fun l : List Bool=>rho^l.length)

lemma exit_weight_norm (l : List Bool) :
    ‖exitWeight D i l‖=if IsExit D i l then rho^l.length else 0 := by
  unfold exitWeight
  split_ifs <;> simp only [wordWeight_norm,norm_zero]

 

theorem exitWeight_summable (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ))
    (hs : Summable (boundaryPathWeight P H i)) : Summable (exitWeight D i) := by
  have hpath := (boundaryPath_summable_iff P (H:=H) (i:=i)).mpr hs
  have hw : Summable (fun x : ExitWord D i=>rho^(exitPathEquiv P hD x).val.2.length) :=
    ((exitPathEquiv P (i:=i) hD).summable_iff
      (f:=fun x : BoundaryPath P H i=>rho^x.val.2.length)).mpr hpath
  have hw' : Summable (fun x : ExitWord D i=>rho^x.val.length) :=
    hw.congr (fun x=>congrArg (fun n : ℕ=>rho^n) (exitPathEquiv_length P hD x))
  have hi := (exitWord_summable_iff (D:=D) (i:=i)).mp hw'
  apply (summable_norm_iff (f:=exitWeight D i)).mp
  exact hi.congr (fun l=>(exit_weight_norm (D:=D) (i:=i) l).symm)

 
theorem exitWeight_tsum (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) (θ : B→ℤ)
    (hθ : ∀x : ExitWord D i,turn x.val=θ (exitPort P x)) :
    (∑'l,exitWeight D i l)=
      ∑'x : B×List Triangle,(boundaryPathWeight P H i x:ℂ)*Diagram.phase^(θ x.1) := by
  calc
    _ = ∑'x : ExitWord D i,wordWeight factor x.val :=
      (tsum_subtype {l | IsExit D i l} (wordWeight factor)).symm
    _ = ∑'x : ExitWord D i,(rho:ℂ)^(exitPathEquiv P hD x).val.2.length *
        Diagram.phase^(θ (exitPathEquiv P hD x).val.1) := by
      apply tsum_congr
      intro x
      rw [wordWeight_eq,exitPathEquiv_length,hθ]
      rfl
    _ = ∑'x : BoundaryPath P H i,(rho:ℂ)^x.val.2.length*Diagram.phase^(θ x.val.1) :=
      (exitPathEquiv P (i:=i) hD).tsum_eq (fun x : BoundaryPath P H i=>(rho:ℂ)^x.val.2.length*Diagram.phase^(θ x.val.1))
    _ = _ := by
      change (∑'x : {x | ValidBoundaryPath P H i x},(rho:ℂ)^x.val.2.length*Diagram.phase^(θ x.val.1))=_
      rw [tsum_subtype {x | ValidBoundaryPath P H i x} (fun x : B×List Triangle=>(rho:ℂ)^x.2.length*Diagram.phase^(θ x.1))]
      apply tsum_congr
      intro x
      simp only [Set.indicator,Set.mem_ofPred_eq,boundaryPathWeight]
      split_ifs <;> simp

 

theorem boundary_flux (hH : 1≤H) (hi : D (bottom i).1)
    (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) (hs : Summable (boundaryPathWeight P H i))
    (θ : B→ℤ) (hθ : ∀x : ExitWord D i,turn x.val=θ (exitPort P x)) :
    (∑'x : B×List Triangle,(boundaryPathWeight P H i x:ℂ)*Diagram.phase^(θ x.1))=1 := by
  rw [←exitWeight_tsum P hD θ hθ]
  exact infinite_boundary_flux hH hi hD (exitWeight_summable P hD hs)

end

 

 

noncomputable section
open scoped Classical
open FiniteBranchTree


lemma steppedVertices_embed (N : ℕ) (s : ℤ) (v : Triangle) :
    steppedVertices N s (embedTriangle v) ↔ steppedDomain N s v := by
  dsimp [steppedVertices,embedTriangle,steppedDomain]
  omega

lemma steppedVertices_bound (N : ℕ) (s : ℤ) (v : Vertex) (hv : steppedVertices N s v) :
    0≤v.2.1 ∧ v.2.1<((N+1:ℕ):ℤ) := by
  dsimp [steppedVertices] at hv
  exact ⟨hv.1,by omega⟩

end
end CriticalStrip.HoneycombBranch

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PhysicalPorts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.HoneycombBranch
noncomputable section
open scoped Classical BigOperators
open FiniteBranchTree

lemma retract_bottom (j : ℤ) : retractVertex (bottom j).1=up j 0 := rfl
lemma retract_top (H : ℕ) (hH : 1≤H) (j : ℤ) : retractVertex (top H j).1=down j (H-1) := by
  dsimp [retractVertex,top,down]
  congr 2
  omega
lemma retract_side (N : ℕ) (s : ℤ) : retractVertex (sidePort N s).1=up s N := by
  simp [retractVertex,sidePort,up]

lemma betweenBridgeWeight_nonneg (H : ℕ) (i j : ℤ) (p : List Triangle) :
    0≤betweenBridgeWeight H i j p := by
  unfold betweenBridgeWeight
  split_ifs <;> positivity [rho_pos]

lemma betweenBridgeWeight_translate (H : ℕ) (i j : ℤ) (p : List Triangle) :
    betweenBridgeWeight H i j (p.map (translateTriangle i))=bridgeWeight H (j-i) p := by
  have hi : up i 0=translateTriangle i (up 0 0) := by simp
  have hj : down j (H-1)=translateTriangle i (down (j-i) (H-1)) := by simp
  simp only [betweenBridgeWeight,bridgeWeight,hi,hj,pathBetween_translate_iff,pathBetween_source,List.length_map]

lemma betweenBridgeWeight_summable (H : ℕ) (hH : 1≤H) (i : ℤ) :
    Summable (fun x : ℤ×List Triangle=>betweenBridgeWeight H i x.1 x.2) := by
  have hf:=stripSumsFinite hH
  have hi (j : ℤ) : Summable (betweenBridgeWeight H i j) := by
    rw [←(translatePaths i).summable_iff]
    apply (hf.2.1 (j-i)).congr
    intro p
    exact (betweenBridgeWeight_translate H i j p).symm
  have he (j : ℤ) : (∑'p,betweenBridgeWeight H i j p)=bridgeKernel H (j-i) := by
    rw [←(translatePaths i).tsum_eq]
    exact tsum_congr (betweenBridgeWeight_translate H i j)
  apply (summable_prod_of_nonneg (fun x=>betweenBridgeWeight_nonneg H i x.1 x.2)).mpr
  refine ⟨hi,?_⟩
  simp_rw [he]
  exact hf.2.2.2.1.comp_injective (i:=fun j : ℤ=>j-i) (by intro a b hh; dsimp at hh; omega)

lemma betweenArchWeight_summable (H : ℕ) (hH : 1≤H) (i : ℤ) :
    Summable (fun x : ℤ×List Triangle=>betweenArchWeight H i x.1 x.2) := by
  have hf:=stripSumsFinite hH
  apply (summable_prod_of_nonneg (fun x=>betweenArchWeight_nonneg H i x.1 x.2)).mpr
  refine ⟨fun j=>(summable_betweenArchWeight_iff H i j).mpr (hf.1 _),?_⟩
  change Summable (fun j=>betweenArchKernel H i j)
  simp_rw [betweenArchKernel_eq]
  exact hf.2.2.1.comp_injective (i:=fun j : ℤ=>j-i) (by intro a b hh; dsimp at hh; omega)

lemma boundaryPathWeight_step_bottom (N : ℕ) (hN : 1≤N) (s i j : ℤ) (p : List Triangle) :
    boundaryPathWeight (stepBoundaryPorts N hN s) (N+1) i (.inl j,p)=stepArchWeight N s i j p := by
  have hc : ValidBoundaryPath (stepBoundaryPorts N hN s) (N+1) i (.inl j,p) ↔
      i≠j ∧ PathBetween (N+1) (up i 0) (up j 0) p ∧ (∀v∈p,steppedDomain N s v) := by
    simp only [ValidBoundaryPath,stepBoundaryPorts,stepPort,retract_bottom,steppedVertices_embed]
    have hb : bottom i≠bottom j ↔ i≠j := by simp [bottom]
    rw [hb]
  unfold boundaryPathWeight stepArchWeight betweenArchWeight
  rw [hc]
  split_ifs <;> tauto

lemma boundaryPathWeight_step_side (N : ℕ) (hN : 1≤N) (s i : ℤ) (p : List Triangle) :
    boundaryPathWeight (stepBoundaryPorts N hN s) (N+1) i (.inr (.inr ()),p)=stepSideWeight N s i p := by
  have hc : ValidBoundaryPath (stepBoundaryPorts N hN s) (N+1) i (.inr (.inr ()),p) ↔
      PathBetween (N+1) (up i 0) (up s N) p ∧ (∀v∈p,steppedDomain N s v) := by
    simp only [ValidBoundaryPath,stepBoundaryPorts,stepPort,retract_side,steppedVertices_embed]
    have hn : bottom i≠sidePort N s := by simp [bottom,sidePort]
    change (bottom i≠sidePort N s ∧ PathBetween (N+1) (up i 0) (up s N) p ∧ _) ↔ _
    exact and_iff_right hn
  simp only [boundaryPathWeight,stepSideWeight,hc]


 

 


lemma summable_sumProd {A B C E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : (A⊕B)×C→E}
    (ha : Summable (fun x : A×C=>f (.inl x.1,x.2)))
    (hb : Summable (fun x : B×C=>f (.inr x.1,x.2))) : Summable f := by
  apply ((Equiv.sumProdDistrib A B C).symm.summable_iff).mp
  exact Summable.sum _ ha hb

lemma tsum_sumProd {A B C E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : (A⊕B)×C→E}
    (ha : Summable (fun x : A×C=>f (.inl x.1,x.2)))
    (hb : Summable (fun x : B×C=>f (.inr x.1,x.2))) :
    (∑'x,f x)=(∑'x : A×C,f (.inl x.1,x.2))+(∑'x : B×C,f (.inr x.1,x.2)) := by
  rw [←(Equiv.sumProdDistrib A B C).symm.tsum_eq f]
  exact ha.tsum_sum hb

lemma phase_im (k : ℤ) : (Diagram.phase^k).im=Real.sin ((k:ℝ)*lambda) := by
  rw [Diagram.phase_pow]
  simp [Complex.exp_im,Diagram.lambda,lambda]

variable {D : Vertex→Prop} {B : Type*} (P : BoundaryPorts D B) {H : ℕ} {i : ℤ}

lemma boundary_complex_summable (hs : Summable (boundaryPathWeight P H i)) (θ : B→ℤ) :
    Summable (fun x : B×List Triangle=>(boundaryPathWeight P H i x:ℂ)*Diagram.phase^(θ x.1)) := by
  apply hs.of_norm_bounded
  intro x
  simp [norm_zpow,phase_norm,Real.norm_of_nonneg (boundaryPathWeight_nonneg P H i x)]

lemma boundary_imaginary_summable (hs : Summable (boundaryPathWeight P H i)) (θ : B→ℤ) :
    Summable (fun x : B×List Triangle=>boundaryPathWeight P H i x*Real.sin ((θ x.1:ℝ)*lambda)) := by
  have hh := (Complex.hasSum_im (boundary_complex_summable P hs θ).hasSum).summable
  simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,phase_im] using hh


theorem boundary_imaginary_flux (hH : 1≤H) (hi : D (bottom i).1)
    (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) (hs : Summable (boundaryPathWeight P H i))
    (θ : B→ℤ) (hθ : ∀x : ExitWord D i,turn x.val=θ (exitPort P x)) :
    (∑'x : B×List Triangle,boundaryPathWeight P H i x*Real.sin ((θ x.1:ℝ)*lambda))=0 := by
  have hh:=congrArg Complex.im (boundary_flux P hH hi hD hs θ hθ)
  rw [Complex.im_tsum (boundary_complex_summable P hs θ)] at hh
  simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,phase_im,Complex.one_im] using hh

end

 

 

noncomputable section
open scoped Classical BigOperators
open FiniteBranchTree



lemma extendStepTop_injective (N : ℕ) (s j : ℤ) : Function.Injective (extendStepTop N s j) := by
  intro p q h
  unfold extendStepTop at h
  split_ifs at h
  · exact List.append_cancel_right h
  · exact h

lemma extendStepTop_spec {N : ℕ} (hN : 1≤N) (s i j : ℤ) {p : List Triangle}
    (hp : ValidBoundaryPath (stepBoundaryPorts N hN s) (N+1) i (.inr (.inl j),p)) :
    PathBetween (N+1) (up i 0) (down j N) (extendStepTop N s j p) := by
  have hpath:=hp.2.1
  change PathBetween (N+1) (up i 0) (retractVertex (stepTop N s j).1) p at hpath
  have hD : ∀v∈p,steppedDomain N s v := fun v hv=>
    (steppedVertices_embed N s v).mp (hp.2.2 v hv)
  by_cases hj : j < s
  · rw [stepTop,ite_eq_left hj,retract_top N hN] at hpath
    have hu : up j N∉p := by
      intro hm
      have he:=hD _ hm
      dsimp [steppedDomain,up] at he
      omega
    have hd : down j N∉p := by
      intro hm
      have he:=hD _ hm
      dsimp [steppedDomain,down] at he
      omega
    have hdu : adjacent (down j (N-1)) (up j N) := by
      simp [adjacent,upDownAdjacent,up,down]
      omega
    have hud : adjacent (up j N) (down j N) := by simp [adjacent,upDownAdjacent,up,down]
    have hp':=(hpath.append_vertex (Nat.lt_succ_self N) hu hdu).append_vertex
      (Nat.lt_succ_self N) (by simpa only [List.mem_append,List.mem_singleton,down,up,Prod.mk.injEq,Bool.false_eq_true,and_false,or_false] using hd) hud
    simpa [extendStepTop,hj,List.append_assoc] using hp'
  · rw [stepTop,ite_eq_right hj,retract_top (N+1) (by omega)] at hpath
    simpa [extendStepTop,hj] using hpath

lemma extendStepTop_weight {N : ℕ} (hN : 1≤N) (s i j : ℤ) (p : List Triangle) :
    rho^2*boundaryPathWeight (stepBoundaryPorts N hN s) (N+1) i (.inr (.inl j),p) ≤
      betweenBridgeWeight (N+1) i j (extendStepTop N s j p) := by
  unfold boundaryPathWeight
  split_ifs with hp
  · have hB : 0<N+1 ∧ PathBetween (N+1) (up i 0) (down j ((N+1)-1)) (extendStepTop N s j p) :=
      ⟨by omega,by simpa using extendStepTop_spec hN s i j hp⟩
    rw [betweenBridgeWeight,ite_eq_left hB]
    by_cases hj : j < s
    · simp only [extendStepTop,ite_eq_left hj,List.length_append,List.length_cons,List.length_nil]
      rw [pow_add]
      simp [mul_comm]
    · simp only [extendStepTop,ite_eq_right hj]
      have hr : rho^2≤1 := rho_sq_lt_one.le
      exact (mul_le_mul_of_nonneg_right hr (pow_nonneg rho_pos.le _)).trans_eq (one_mul _)
  · simp only [mul_zero]
    exact betweenBridgeWeight_nonneg _ _ _ _

lemma stepBoundary_top_summable {N : ℕ} (hN : 1≤N) (s i : ℤ) :
    Summable (fun x : ℤ×List Triangle=>
      boundaryPathWeight (stepBoundaryPorts N hN s) (N+1) i (.inr (.inl x.1),x.2)) := by
  let e : ℤ×List Triangle→ℤ×List Triangle := fun x=>(x.1,extendStepTop N s x.1 x.2)
  have he : Function.Injective e := by
    intro x y hh
    have hj:=congrArg Prod.fst hh
    change x.1=y.1 at hj
    have hp:=congrArg Prod.snd hh
    change extendStepTop N s x.1 x.2=extendStepTop N s y.1 y.2 at hp
    rw [hj] at hp
    exact Prod.ext hj (extendStepTop_injective N s y.1 hp)
  have hg:=(betweenBridgeWeight_summable (N+1) (by omega) i).comp_injective he
  have hm : Summable (fun x : ℤ×List Triangle=>rho^2*
      boundaryPathWeight (stepBoundaryPorts N hN s) (N+1) i (.inr (.inl x.1),x.2)) :=
    hg.of_nonneg_of_le (fun x=>mul_nonneg (sq_nonneg _) (boundaryPathWeight_nonneg _ _ _ _))
      (fun x=>extendStepTop_weight hN s i x.1 x.2)
  exact (summable_mul_left_iff (pow_ne_zero _ rho_pos.ne')).mp hm

lemma stepArchWeight_summable {N : ℕ} (hN : 1≤N) (s i : ℤ) :
    Summable (fun x : ℤ×List Triangle=>stepArchWeight N s i x.1 x.2) :=
  (betweenArchWeight_summable (N+1) (by omega) i).of_nonneg_of_le
    (fun x=>stepArchWeight_nonneg N s i x.1 x.2) (fun x=>stepArchWeight_le N s i x.1 x.2)

 

theorem stepBoundary_summable {N : ℕ} (hN : 1≤N) (s i : ℤ) :
    Summable (boundaryPathWeight (stepBoundaryPorts N hN s) (N+1) i) := by
  apply summable_sumProd
  · simpa only [boundaryPathWeight_step_bottom] using stepArchWeight_summable hN s i
  · apply summable_sumProd
    · exact stepBoundary_top_summable hN s i
    · have hs := (stepSideWeight_summable s (stripSumsFinite (show 1≤N+1 by omega))).prod_factor i
      apply (summable_prod_of_nonneg (fun x=>boundaryPathWeight_nonneg _ _ _ _)).mpr
      refine ⟨?_,(hasSum_fintype _).summable⟩
      intro u
      cases u
      simpa only [boundaryPathWeight_step_side] using hs


 

 


lemma summable_sumProd_left {A B C E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : (A⊕B)×C→E} (hf : Summable f) :
    Summable (fun x : A×C=>f (.inl x.1,x.2)) := by
  apply hf.comp_injective
  intro x y h
  exact Prod.ext (Sum.inl.inj (congrArg (fun z : (A⊕B)×C=>z.1) h)) (congrArg (fun z : (A⊕B)×C=>z.2) h)

lemma summable_sumProd_right {A B C E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : (A⊕B)×C→E} (hf : Summable f) :
    Summable (fun x : B×C=>f (.inr x.1,x.2)) := by
  apply hf.comp_injective
  intro x y h
  exact Prod.ext (Sum.inr.inj (congrArg (fun z : (A⊕B)×C=>z.1) h)) (congrArg (fun z : (A⊕B)×C=>z.2) h)

lemma stepTurn_sine_right (i : ℤ) (n : ℕ) :
    Real.sin ((stepTurn i (.inl (i+(n:ℤ)+1)):ℝ)*lambda) = -Real.sin (3*lambda) := by
  have hh : i≤ i+(n:ℤ)+1 := by omega
  simp [stepTurn,hh,neg_mul,Real.sin_neg]

lemma stepTurn_sine_left (i : ℤ) (n : ℕ) :
    Real.sin ((stepTurn i (.inl (i-1-(n:ℤ))):ℝ)*lambda) = Real.sin (3*lambda) := by
  have hh : ¬(i≤ i-1-(n:ℤ)) := by omega
  simp [stepTurn,hh]

lemma stepArchKernel_self (N : ℕ) (s i : ℤ) : stepArchKernel N s i i=0 := by
  simp [stepArchKernel,stepArchWeight,betweenArchWeight]

lemma step_bottom_imaginary_tsum {N : ℕ} (hN : 1≤N) (s i : ℤ) :
    (∑'x : ℤ×List Triangle,stepArchWeight N s i x.1 x.2 * Real.sin ((stepTurn i (.inl x.1):ℝ)*lambda))=
    Real.sin (3*lambda)*(stepArchLeft N s i-stepArchRight N s i) := by
  have hB:=summable_sumProd_left (boundary_imaginary_summable (stepBoundaryPorts N hN s)
    (stepBoundary_summable hN s i) (stepTurn i))
  simp only [boundaryPathWeight_step_bottom] at hB
  let f : ℤ→ℝ:=fun j=>stepArchKernel N s i j * Real.sin ((stepTurn i (.inl j):ℝ)*lambda)
  have hprod (j : ℤ) : (∑'p,stepArchWeight N s i j p * Real.sin ((stepTurn i (.inl j):ℝ)*lambda))=f j := by
    rw [tsum_mul_right]; rfl
  have hf : Summable f := hB.prod.congr hprod
  have hr := hf.comp_injective (i:=fun n : ℕ=>i+(n:ℤ)+1) (by intro a b hh; dsimp at hh; omega)
  have hl := hf.comp_injective (i:=fun n : ℕ=>i-1-(n:ℤ)) (by intro a b hh; dsimp at hh; omega)
  have he (n : ℕ) : i+ -((n:ℤ)+1)=i-1-(n:ℤ) := by ring
  have hh := tsum_of_add_one_of_neg_add_one (f:=fun j : ℤ=>f (i+j))
    (by simpa only [Function.comp_def,add_assoc] using hr)
    (by simpa only [Function.comp_def,he] using hl)
  rw [hB.tsum_prod]
  simp_rw [hprod]
  rw [←(Equiv.addLeft i).tsum_eq f]
  change (∑'j : ℤ,f (i+j))=_
  rw [hh]
  have hr' (n : ℕ) : f (i+((n:ℤ)+1)) = stepArchKernel N s i (i+(n:ℤ)+1) * (-Real.sin (3*lambda)) := by
    simp only [f,←add_assoc,stepTurn_sine_right]
  have hl' (n : ℕ) : f (i+ -((n:ℤ)+1)) = stepArchKernel N s i (i-1-(n:ℤ)) * Real.sin (3*lambda) := by
    simp only [f,he,stepTurn_sine_left]
  have hz : f (i+0)=0 := by simp only [f,add_zero,stepArchKernel_self,zero_mul]
  simp_rw [hr',hl',hz,add_zero,tsum_mul_right]
  change stepArchRight N s i * (-Real.sin (3*lambda)) + stepArchLeft N s i * Real.sin (3*lambda) = _
  ring

 

theorem physical_stepped_flux_oai {N : ℕ} (hN : 1≤N) (s : ℤ) : SteppedBoundaryFlux N s := by
  intro i
  let P:=stepBoundaryPorts N hN s
  let F : StepEndpoint×List Triangle→ℝ :=
    fun x=>boundaryPathWeight P (N+1) i x*Real.sin ((stepTurn i x.1:ℝ)*lambda)
  have hs : Summable F := boundary_imaginary_summable P (stepBoundary_summable hN s i) (stepTurn i)
  have hf : (∑'x,F x)=0 := boundary_imaginary_flux P (by omega)
    (by dsimp [steppedVertices,bottom]; omega) (steppedVertices_bound N s)
      (stepBoundary_summable hN s i) (stepTurn i) (step_turn N hN s i)
  have hb:=summable_sumProd_left hs
  have hn:=summable_sumProd_right hs
  have ht:=summable_sumProd_left hn
  have hp:=summable_sumProd_right hn
  have hsplit : (∑'x : ℤ×List Triangle,F (.inl x.1,x.2)) +
      ((∑'x : ℤ×List Triangle,F (.inr (.inl x.1),x.2)) +
       (∑'x : Unit×List Triangle,F (.inr (.inr x.1),x.2)))=0 :=
    (congrArg (fun y : ℝ => (∑'x : ℤ×List Triangle,F (.inl x.1,x.2)) + y)
      (tsum_sumProd (f:=fun x : (ℤ⊕Unit)×List Triangle => F (.inr x.1,x.2)) ht hp)).symm.trans ((tsum_sumProd (f:=F) hb hn).symm.trans hf)
  have hbot : (∑'x : ℤ×List Triangle,F (.inl x.1,x.2))=
      Real.sin (3*lambda)*(stepArchLeft N s i-stepArchRight N s i) := by
    simpa only [F,P,boundaryPathWeight_step_bottom] using step_bottom_imaginary_tsum hN s i
  have htop : (∑'x : ℤ×List Triangle,F (.inr (.inl x.1),x.2))=0 := by
    simp [F,stepTurn]
  have hside : (∑'x : Unit×List Triangle,F (.inr (.inr x.1),x.2))=
      Real.sin lambda*stepSideKernel N s i := by
    rw [hp.tsum_prod]
    simp [F,P,stepTurn,boundaryPathWeight_step_side,tsum_mul_left,stepSideKernel,mul_comm]
  have hvalue := congrArg₂ (fun a b : ℝ => a+b) hbot
    (congrArg₂ (fun a b : ℝ => a+b) htop hside)
  have hresult := hvalue.symm.trans hsplit
  simpa only [zero_add] using hresult

end
end CriticalStrip.HoneycombBranch





end OAI
end

theorem solution : type_of% @OAI.CriticalStrip.HoneycombBranch.physical_stepped_flux_oai := @OAI.CriticalStrip.HoneycombBranch.physical_stepped_flux_oai
