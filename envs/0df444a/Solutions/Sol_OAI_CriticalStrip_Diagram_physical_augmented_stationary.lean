-- Prove2me | solution 1 for OAI.CriticalStrip.Diagram.physical_augmented_stationary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T02:16:40.179611+00:00
-- url     : https://prove2.me/submissions/550d2f44-b35c-4115-974a-8525ae051e07

import Mathlib
import Definitions.Def_OAIQ042S015
import Theorems.Thm_OAI_CriticalStrip_Diagram_homogeneous_angleScalar_ne_zero

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

lemma rationalAt_angle_spectralWeights {n : ℕ} (u : Fin n → ℝ)
    (hL : ∀i,L (3*lambda-u i)≠0) (i : Fin n) (t : Tile) :
    RationalAt (angleEvaluation u).toRingHom ((spectralWeights n i).tile t)
      ((physicalWeights (3*lambda-u i)).tile t:ℂ) := by
  apply rationalAt_angle_weights _ _ (hL i)
  rw [anglePhase_sub,show anglePhase (3*lambda)=phase^3 from anglePhase_nat_mul 3 _]
  exact ((rationalAt_const_complex (angleEvaluation u) phase).pow 3).div
      (rationalAt_angle_variable u i) (anglePhase_ne_zero _)

end
end CriticalStrip.Diagram







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

end





end CriticalStrip.Diagram





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_DeformationWeights
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

end
end CriticalStrip.Diagram





namespace CriticalStrip.Diagram
noncomputable section
open _root_.Matrix
open scoped BigOperators Classical

lemma homogeneous_L_ne_zero : L (3*lambda-lambda)≠0 :=
  (L_deformation_pos (t:=lambda) ⟨lambda_pos.le,le_rfl⟩).ne'



end
end CriticalStrip.Diagram

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





namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators
open _root_.Matrix Filter Topology

lemma physical_augmented_stationary_oai (N : ℕ) :
    (restrictedColumn (SewnRectangle.leftWeights N)).mulVec
        (fun p=>angleAugmented (fun _ : Fin N=>lambda) p.val)+
      injectionColumn (SewnRectangle.leftWeights N)=
      fun p=>angleAugmented (fun _ : Fin N=>lambda) p.val := by
  simpa only [show 3*lambda-lambda=2*lambda by ring,SewnRectangle.leftWeights] using
    angleAugmented_restricted_stationary (fun _ : Fin N=>lambda)
      (fun _=>homogeneous_L_ne_zero) (homogeneous_angleScalar_ne_zero N)

end
end CriticalStrip.Diagram





end OAI
end

theorem solution : type_of% @OAI.CriticalStrip.Diagram.physical_augmented_stationary_oai := @OAI.CriticalStrip.Diagram.physical_augmented_stationary_oai
