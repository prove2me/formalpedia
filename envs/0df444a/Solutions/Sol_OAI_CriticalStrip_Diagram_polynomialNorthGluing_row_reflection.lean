-- Prove2me | solution 1 for OAI.CriticalStrip.Diagram.polynomialNorthGluing_row_reflection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T02:30:21.17893+00:00
-- url     : https://prove2.me/submissions/ae78448a-c10d-4aba-8155-6c2416a0b953

import Mathlib
import Definitions.Def_OAIQ042S015

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



end


 

noncomputable section
open scoped Classical BigOperators

namespace Graph


lemma DrainsAt.map {V W : Type*} {r : V → V → Prop} {s : W → W → Prop}
    (e : V ≃ W) (he : ∀ v w, s (e v) (e w) ↔ r v w) {root : V}
    (h : DrainsAt r root) : DrainsAt s (e root) := by
  intro x y hxy
  obtain ⟨v,rfl⟩ := e.surjective x
  obtain ⟨w,rfl⟩ := e.surjective y
  exact Graph.map_reach e (fun v w hvw => .single ((he v w).mpr hvw))
    (h v w ((he v w).mp hxy))



end Graph
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
namespace Graph
lemma closure_drains_local {V : Type*} {n : ℕ} {r : V → V → Prop}
    {a : Fin n → V} {q : Pairing n} {root : Fin n}
    (h : DrainsAt (boundaryClosure r a q) (a root)) : DrainsBoundary r a := by
  intro v w hvw
  have hr := h v w (Or.inl hvw)
  clear hvw w h
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨root, .refl⟩
  | @head x y hxy hpath ih =>
    rcases hxy with hxy | ⟨i,j,_,rfl,_⟩
    · obtain ⟨i,hi⟩ := ih
      exact ⟨i,hi.head hxy⟩
    · exact ⟨i,.refl⟩

end Graph

namespace Pairing

lemma GluesAt.symm {n : ℕ} {root : Fin n} {p q : Pairing n}
    (h : GluesAt root p q) : GluesAt root q p := by
  refine ⟨(h.2.1 root).mp h.1,fun i => (h.2.1 i).symm,?_⟩
  intro i j hij
  exact Relation.ReflTransGen.mono (r := p.join q) (p := q.join p) (fun _ _ hh => hh.symm) _ _ (h.2.2 i j hij.symm)

end Pairing

namespace Pairing


lemma GateCompatible.transpose {n : ℕ} {p q : Pairing n} {a b : Fin n}
    (hab : a≠b) {t : Tile} (h : GateCompatible p q a b t) :
    GateCompatible q p a b t.transpose := by
  have hp := (p.cutShape_compatible a b t).mp h.1
  have hqa : t.Occupied 2 ↔ q.Occupied a := by simpa [stepSupport] using h.2 a
  have hqb : t.Occupied 3 ↔ q.Occupied b := by simpa [stepSupport,Ne.symm hab] using h.2 b
  refine ⟨(q.cutShape_compatible a b t.transpose).mpr ?_,?_⟩
  · constructor
    · exact hqa.symm.trans (t.transpose_occupied (2 : Fin 4)).symm
    · exact hqb.symm.trans (t.transpose_occupied (3 : Fin 4)).symm
  · intro i
    by_cases hia : i=a
    · subst i
      simp only [stepSupport,ite_true]
      exact (t.transpose_occupied (0 : Fin 4)).trans hp.1.symm
    · by_cases hib : i=b
      · subst i
        simp only [stepSupport,ite_eq_right (Ne.symm hab),ite_true]
        exact (t.transpose_occupied (1 : Fin 4)).trans hp.2.symm
      · simpa [stepSupport,hia,hib] using (h.2 i).symm


lemma closedStep_flip {n : ℕ} {p q : Pairing n} {a b : Fin n} (hab : a≠b)
    {t : Tile} (h : GateCompatible p q a b t) (v w : StepVertex n) :
    closedStep q p a b t.transpose (flipStep v) (flipStep w) ↔
      closedStep p q a b t v w := by
  have hp := (p.cutShape_compatible a b t).mp h.1
  have hqa : t.Occupied 2 ↔ q.Occupied a := by simpa [stepSupport] using h.2 a
  have hqb : t.Occupied 3 ↔ q.Occupied b := by simpa [stepSupport,Ne.symm hab] using h.2 b
  have ho (i : Fin n) (hia : i≠a) (hib : i≠b) : q.Occupied i ↔ p.Occupied i := by
    simpa [stepSupport,hia,hib] using (h.2 i).symm
  have ht0 : t.transpose.Occupied 0 ↔ t.Occupied 2 := t.transpose_occupied 2
  have ht1 : t.transpose.Occupied 1 ↔ t.Occupied 3 := t.transpose_occupied 3
  have ht2 : t.transpose.Occupied 2 ↔ t.Occupied 0 := t.transpose_occupied 0
  have ht3 : t.transpose.Occupied 3 ↔ t.Occupied 1 := t.transpose_occupied 1
  cases v with
  | old i =>
    cases w with
    | old j => simp [closedStep,Graph.boundaryClosure,stepWiring,flipStep]
    | box k =>
      fin_cases k <;>
        simp [closedStep,Graph.boundaryClosure,stepWiring,flipStep,Tile.transposePort,
          ht2,ht3,←hp.1,←hp.2]
    | out j =>
      simp only [closedStep,Graph.boundaryClosure,stepWiring,flipStep]
      constructor <;> rintro (⟨hij,hia,hib,hi⟩ | ⟨k,l,_,hk,hl⟩)
      · subst j; exact Or.inl ⟨rfl,hia,hib,(ho i hia hib).mp hi⟩
      · cases hl
      · subst j; exact Or.inl ⟨rfl,hia,hib,(ho i hia hib).mpr hi⟩
      · cases hk
  | box k =>
    cases w with
    | old i =>
      fin_cases k <;>
        simp [closedStep,Graph.boundaryClosure,stepWiring,flipStep,Tile.transposePort,
          ht2,ht3,←hp.1,←hp.2]
    | box l => simp [closedStep,Graph.boundaryClosure,stepWiring,flipStep]
    | out i =>
      fin_cases k <;>
        simp [closedStep,Graph.boundaryClosure,stepWiring,flipStep,Tile.transposePort,
          hqa,hqb]
  | out i =>
    cases w with
    | old j =>
      simp only [closedStep,Graph.boundaryClosure,stepWiring,flipStep]
      constructor <;> rintro (⟨hij,hia,hib,hi⟩ | ⟨k,l,_,hk,hl⟩)
      · subst j; exact Or.inl ⟨rfl,hia,hib,(ho i hia hib).mp hi⟩
      · cases hk
      · subst j; exact Or.inl ⟨rfl,hia,hib,(ho i hia hib).mpr hi⟩
      · cases hl
    | box k =>
      fin_cases k <;>
        simp [closedStep,Graph.boundaryClosure,stepWiring,flipStep,Tile.transposePort,
          hqa,hqb]
    | out j => simp [closedStep,Graph.boundaryClosure,stepWiring,flipStep]

 
lemma glues_tile_iff_closedStep {n : ℕ} {p q : Pairing n} {a b root : Fin n}
    (hab : a.val+1=b.val) (hra : root ≠ a) (hrb : root ≠ b) (t : Tile) :
    (∃ r, p.tileStep a b hab t = some r ∧ GluesAt root r q) ↔
      p.Occupied root ∧ GateCompatible p q a b t ∧
        Graph.DrainsAt (closedStep p q a b t) (.out root) := by
  constructor
  · rintro ⟨r,hr,hg⟩
    refine ⟨?_,⟨p.tileStep_compatible a b hab t r hr,?_⟩,?_⟩
    · have hh := (p.tileStep_support a b hab t r hr root).mp hg.1
      simpa only [stepSupport,ite_eq_right hra,ite_eq_right hrb] using hh
    · intro i
      exact (p.tileStep_support a b hab t r hr i).symm.trans (hg.2.1 i)
    · exact ((p.stepWiring_realizes a b hab t r hr).closure_drains_iff
        (fun _ _ h => StepVertex.out.inj h) root).mpr hg.2.2
  · rintro ⟨hp,hc,hd⟩
    have hn := p.tileStep_ne_none_of_drains a b hab t hc.1
      (Graph.closure_drains_local hd)
    obtain ⟨r,hr⟩ := Option.ne_none_iff_exists'.mp hn
    refine ⟨r,hr,?_,?_,?_⟩
    · apply (p.tileStep_support a b hab t r hr root).mpr
      simpa only [stepSupport,ite_eq_right hra,ite_eq_right hrb] using hp
    · intro i
      exact (p.tileStep_support a b hab t r hr i).trans (hc.2 i)
    · exact ((p.stepWiring_realizes a b hab t r hr).closure_drains_iff
        (fun _ _ h => StepVertex.out.inj h) root).mp hd

lemma glues_tile_flip {n : ℕ} {p q : Pairing n} {a b root : Fin n}
    (hab : a.val+1=b.val) (hra : root ≠ a) (hrb : root ≠ b) (t : Tile)
    (h : ∃ r, p.tileStep a b hab t = some r ∧ GluesAt root r q) :
    ∃ r, q.tileStep a b hab t.transpose = some r ∧ GluesAt root r p := by
  obtain ⟨hp,hc,hd⟩ := (glues_tile_iff_closedStep hab hra hrb t).mp h
  have hne : a≠b := by intro hh; have := congrArg Fin.val hh; omega
  have hq : q.Occupied root := (hc.2 root).mp
    (by simpa only [stepSupport,ite_eq_right hra,ite_eq_right hrb] using hp)
  apply (glues_tile_iff_closedStep hab hra hrb t.transpose).mpr
  refine ⟨hq,hc.transpose hne,?_⟩
  have hf := hd.map (Function.Involutive.toPerm (@flipStep n) flipStep_involutive)
    (closedStep_flip hne hc)
  apply hf.mono_root
  exact .single (Or.inl ⟨rfl,hra,hrb,hq⟩)

 

theorem glues_tile_adjoint {n : ℕ} {p q : Pairing n} {a b root : Fin n}
    (hab : a.val+1=b.val) (hra : root ≠ a) (hrb : root ≠ b) (t : Tile) :
    (∃ r, p.tileStep a b hab t = some r ∧ GluesAt root r q) ↔
      (∃ r, q.tileStep a b hab t.transpose = some r ∧ GluesAt root p r) := by
  constructor
  · intro h
    obtain ⟨r,hr,hg⟩ := glues_tile_flip hab hra hrb t h
    exact ⟨r,hr,hg.symm⟩
  · rintro ⟨r,hr,hg⟩
    simpa only [Tile.transpose_transpose] using glues_tile_flip hab hra hrb
      t.transpose ⟨r,hr,hg.symm⟩

lemma gluesAt_comm {n : ℕ} (root : Fin n) (p q : Pairing n) :
    GluesAt root p q ↔ GluesAt root q p := ⟨GluesAt.symm,GluesAt.symm⟩

end Pairing



lemma mul_optionMatrix_apply {K P Q R : Type*} [Semiring K] [Fintype Q]
    (A : Matrix R Q K) (f : P → Option Q) (r : R) (p : P) :
    (A * (optionMatrix f : Matrix Q P K)) r p = (f p).elim 0 (A r) := by
  rcases Option.eq_none_or_eq_some (f p) with h | ⟨q,h⟩
  · simp [Matrix.mul_apply,optionMatrix,h]
  · simp [Matrix.mul_apply,optionMatrix,h,mul_ite]

lemma transpose_optionMatrix_mul_apply {K P Q R : Type*} [Semiring K] [Fintype Q]
    (A : Matrix Q R K) (f : P → Option Q) (p : P) (r : R) :
    ((optionMatrix f : Matrix Q P K).transpose * A) p r = (f p).elim 0 (fun q => A q r) := by
  rcases Option.eq_none_or_eq_some (f p) with h | ⟨q,h⟩
  · simp [Matrix.mul_apply,optionMatrix,h]
  · simp [Matrix.mul_apply,optionMatrix,h,ite_mul]

lemma tileMatrix_glue_adjoint {K : Type*} [Semiring K] {n : ℕ} (a : Position n)
    (root : Fin n) (hra : root≠a.left) (hrb : root≠a.right) (t : Tile) :
    (glueMatrix root : Matrix _ _ K) *
        optionMatrix (fun p => p.tileStep a.left a.right a.adjacent t) =
      (optionMatrix (fun p => p.tileStep a.left a.right a.adjacent t.transpose)).transpose *
        glueMatrix root := by
  ext q p
  rw [mul_optionMatrix_apply,transpose_optionMatrix_mul_apply]
  have hh := Pairing.glues_tile_adjoint (p:=p) (q:=q) a.adjacent hra hrb t
  rcases Option.eq_none_or_eq_some (p.tileStep a.left a.right a.adjacent t) with hp | ⟨r,hp⟩
  <;> rcases Option.eq_none_or_eq_some (q.tileStep a.left a.right a.adjacent t.transpose)
    with hq | ⟨s,hq⟩
  · simp [hp,hq]
  · have hs : ¬ Pairing.GluesAt root p s := by simpa [hp,hq] using hh.symm
    simpa [hp,hq,glueMatrix,Pairing.gluesAt_comm root s p] using
      (ite_eq_right hs : (if Pairing.GluesAt root p s then (1:K) else 0) = 0).symm
  · have hr : ¬ Pairing.GluesAt root r q := by simpa [hp,hq] using hh
    simp [hp,hq,glueMatrix,Pairing.gluesAt_comm root q r,hr]
  · have he : Pairing.GluesAt root r q ↔ Pairing.GluesAt root p s := by
      simpa [hp,hq] using hh
    simp only [hp,hq,Option.elim_some,glueMatrix,Pairing.gluesAt_comm root q r,
      Pairing.gluesAt_comm root s p,he]

 

theorem localR_glue_adjoint {K : Type*} [CommRing K] {n : ℕ} (a : Position n)
    (root : Fin n) (hra : root≠a.left) (hrb : root≠a.right) (w : Weights K) :
    (glueMatrix root : Matrix _ _ K) * localR a w = (localR a w).transpose * glueMatrix root := by
  simp only [localR,Finset.mul_sum,Matrix.mul_smul,Finset.sum_mul,
    Matrix.transpose_sum,Matrix.transpose_smul,Matrix.smul_mul]
  rw [← Equiv.sum_comp Tile.transposeEquiv]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Tile.transposeEquiv,Equiv.coe_fn_mk,Tile.weight_transpose]
  rw [tileMatrix_glue_adjoint a root hra hrb]
  simp only [Tile.transpose_transpose]







lemma LastMatrix.source_mulVec {K : Type*} [CommRing K] {n m : ℕ}
    {M : Matrix (Pairing (m+1)) (Pairing (n+1)) K} (hM : LastMatrix M)
    (V : Pairing (n+1) → K) (p : SourcePairing m) :
    M.mulVec V p.val = (sourceBlock M).mulVec (fun q => V q.val) p := by
  simp only [Matrix.mulVec, dotProduct, sourceBlock]
  symm
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro q hq
    have hn : ¬q.Occupied (Fin.last n) := by
      intro h
      exact hq ⟨⟨q,h⟩,rfl⟩
    rw [hM p.val q (by simp [p.property, hn]), zero_mul]
  · intro q; rfl


lemma northNumerator_covariance {n : ℕ} (r : ℕ) (hr : r+2≤n) :
    northNumerator n =
      (sourceBlock (localR (PartialColumn.rowPosition r hr).padTop
        (torusWeights (variableF ⟨r+1,by omega⟩ / variableF ⟨r,by omega⟩)))).mulVec
        (fun p => permSpectral (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩)
          (northNumerator n p)) := by
  funext p
  have hh := congrArg (fun U : Pairing (n+1) → Polynomial (SpectralField n) =>
      (U p.val).coeff (n-1)) (rationalNodalPolynomial_covariance r hr)
  rw [nodalExchangePolynomial_coeff] at hh
  change northNumerator n p = _ at hh
  exact hh.trans ((LastMatrix.local _ _).source_mulVec _ p)



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

lemma reflectLaurent_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : Laurent n) :
    reflectLaurent n (permLaurent σ f) = permLaurent σ (reflectLaurent n f) := by
  have h : (reflectLaurent n).comp (permLaurent σ) =
      (permLaurent σ).comp (reflectLaurent n) := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change reflectLaurent n (permLaurent σ (monomialL _ _)) =
      permLaurent σ (reflectLaurent n (monomialL _ _))
    all_goals rw [permLaurent_monomial, reflectLaurent_monomial,
      reflectLaurent_monomial, permLaurent_monomial]
    all_goals simp only [Function.comp_apply, Equiv.sum_comp]
    all_goals rfl
  exact DFunLike.congr_fun h f

lemma reflectSpectral_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : SpectralField n) :
    reflectSpectral n (permSpectral σ f) = permSpectral σ (reflectSpectral n f) := by
  have h : (reflectSpectral n).comp (permSpectral σ) =
      (permSpectral σ).comp (reflectSpectral n) := by
    apply IsFractionRing.ringHom_ext (A := SpectralRing n)
    intro f
    change reflectSpectral n (permSpectral σ (evalLaurent f)) =
      permSpectral σ (reflectSpectral n (evalLaurent f))
    simp only [reflectSpectral_evalLaurent, permSpectral_evalLaurent, reflectLaurent_perm]
  exact DFunLike.congr_fun h f






lemma sourceBlock_map {K L : Type*} {n m : ℕ} (f : K → L)
    (M : Matrix (Pairing (m+1)) (Pairing (n+1)) K) :
    (sourceBlock M).map f = sourceBlock (M.map f) := rfl

lemma sourceBlock_transpose {K : Type*} {n m : ℕ}
    (M : Matrix (Pairing (m+1)) (Pairing (n+1)) K) :
    sourceBlock M.transpose = (sourceBlock M).transpose := rfl

lemma LastMatrix.source_mul {K : Type*} [CommRing K] {n m r : ℕ}
    {M : Matrix (Pairing (r+1)) (Pairing (m+1)) K} (hM : LastMatrix M)
    (N : Matrix (Pairing (m+1)) (Pairing (n+1)) K) :
    sourceBlock (M*N) = sourceBlock M * sourceBlock N := by
  ext p q
  exact hM.source_mulVec (fun a => N a q.val) p

lemma glueMatrix_last {K : Type*} [Zero K] [One K] (n : ℕ) :
    LastMatrix (glueMatrix (Fin.last n) : Matrix _ _ K) := by
  intro p q h
  apply ite_eq_right
  intro hg
  exact h (hg.2.1 _)

lemma LastMatrix.transpose {K : Type*} [Zero K] {n m : ℕ}
    {M : Matrix (Pairing (m+1)) (Pairing (n+1)) K} (hM : LastMatrix M) :
    LastMatrix M.transpose := by
  intro p q h
  exact hM q p (fun hh => h hh.symm)


lemma sourceGlue_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (n : ℕ) (v w : SourcePairing n → K) :
    f (sourceGlue n v w) = sourceGlue n (f ∘ v) (f ∘ w) := by
  simp only [sourceGlue, dotProduct, Matrix.mulVec, map_sum, map_mul,
    sourceBlock, glueMatrix, Function.comp_apply, apply_ite, map_one, map_zero]

lemma sourceGlue_adjoint {K : Type*} [CommRing K] {n : ℕ}
    (a : Position n) (w : Weights K) (v z : SourcePairing n → K) :
    sourceGlue n v ((sourceBlock (localR a.padTop w)).mulVec z) =
      sourceGlue n ((sourceBlock (localR a.padTop w)).mulVec v) z := by
  have ha : Fin.last n ≠ a.padTop.left := by
    intro he
    have hh := congrArg Fin.val he
    have := a.left.isLt
    simp only [Position.padTop, Fin.val_last, Fin.val_castSucc] at hh
    omega
  have hb : Fin.last n ≠ a.padTop.right := by
    intro he
    have hh := congrArg Fin.val he
    have := a.right.isLt
    simp only [Position.padTop, Fin.val_last, Fin.val_castSucc] at hh
    omega
  have h := congrArg sourceBlock (localR_glue_adjoint a.padTop (Fin.last n) ha hb w)
  rw [(glueMatrix_last n).source_mul, (LastMatrix.local a w).transpose.source_mul,
    sourceBlock_transpose] at h
  unfold sourceGlue
  rw [Matrix.mulVec_mulVec, h, ←Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

lemma polynomialNorthSource_eval_numerator (n : ℕ) (p : SourcePairing n) :
    evalLaurent (polynomialNorthSource n p) =
      constF n (1/(2*(d:ℂ))) * northNumerator n p := by
  unfold polynomialNorthSource evalLaurent
  rw [map_mul, map_constantL, ←Polynomial.coeff_map, (vacuumData n).map_P]
  rfl

lemma polynomialNorthSource_covariance {n : ℕ} (r : ℕ) (hr : r+2≤n) :
    (fun p => evalLaurent (polynomialNorthSource n p)) =
      (sourceBlock (localR (PartialColumn.rowPosition r hr).padTop
        (torusWeights (variableF ⟨r+1,by omega⟩ / variableF ⟨r,by omega⟩)))).mulVec
        (fun p => permSpectral (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩)
          (evalLaurent (polynomialNorthSource n p))) := by
  simp only [polynomialNorthSource_eval_numerator, map_mul, permSpectral_const]
  change constF n (1/(2*(d:ℂ))) • northNumerator n =
    Matrix.mulVec _ (constF n (1/(2*(d:ℂ))) • _)
  rw [Matrix.mulVec_smul]
  exact congrArg (fun v => constF n (1/(2*(d:ℂ))) • v) (northNumerator_covariance r hr)

lemma permSpectral_swap_involutive {n : ℕ} (i j : Fin n) :
    Function.Involutive (permSpectral (Equiv.swap i j)) := by
  have h : (permSpectral (Equiv.swap i j)).comp (permSpectral (Equiv.swap i j)) =
      RingHom.id _ := by
    apply IsFractionRing.ringHom_ext (A := SpectralRing n)
    intro f
    change permSpectral (Equiv.swap i j) (permSpectral (Equiv.swap i j) (evalLaurent f)) = evalLaurent f
    rw [permSpectral_evalLaurent, permSpectral_evalLaurent]
    have hl : (permLaurent (Equiv.swap i j)).comp (permLaurent (Equiv.swap i j)) =
        RingHom.id _ := by
      apply AddMonoidAlgebra.ringHom_ext <;> intro e
      all_goals change permLaurent _ (permLaurent _ (monomialL _ _)) = monomialL _ _
      all_goals rw [permLaurent_monomial, permLaurent_monomial]; congr 1
      all_goals ext k; simp
    exact congrArg evalLaurent (DFunLike.congr_fun hl f)
  exact fun f => DFunLike.congr_fun h f



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
-- module Solutions.OAIQ042_SS.StripMass_NorthGluing
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

lemma polynomialNorthGluing_eval (n : ℕ) :
    evalLaurent (polynomialNorthGluing n) =
      sourceGlue n (fun p => reflectSpectral n (evalLaurent (polynomialNorthSource n p)))
        (fun p => evalLaurent (polynomialNorthSource n p)) := by
  unfold polynomialNorthGluing evalLaurent
  rw [sourceGlue_map]
  change sourceGlue n (fun p => evalLaurent (reflectLaurent n (polynomialNorthSource n p)))
      (fun p => evalLaurent (polynomialNorthSource n p)) = _
  congr 1
  funext p
  exact (reflectSpectral_evalLaurent (polynomialNorthSource n p)).symm


lemma perm_reflect_ratio {n : ℕ} (i j : Fin n) :
    permSpectral (Equiv.swap i j) (reflectSpectral n (variableF j / variableF i)) =
      variableF j / variableF i := by
  simp only [map_div₀, reflectSpectral_variable, map_pow, permSpectral_const,
    permSpectral_variable, Equiv.swap_apply_left, Equiv.swap_apply_right]
  field_simp [variableF_ne_zero, constF_phase_ne_zero]

lemma polynomialNorthSource_reflected_covariance {n : ℕ} (r : ℕ) (hr : r+2≤n) :
    (fun p => permSpectral (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩)
      (reflectSpectral n (evalLaurent (polynomialNorthSource n p)))) =
      (sourceBlock (localR (PartialColumn.rowPosition r hr).padTop
        (torusWeights (variableF ⟨r+1,by omega⟩ / variableF ⟨r,by omega⟩)))).mulVec
        (fun p => reflectSpectral n (evalLaurent (polynomialNorthSource n p))) := by
  let σ := Equiv.swap (⟨r,by omega⟩ : Fin n) (⟨r+1,by omega⟩ : Fin n)
  let R : Matrix (SourcePairing n) (SourcePairing n) (SpectralField n) := sourceBlock (localR (PartialColumn.rowPosition r hr).padTop
        (torusWeights (variableF ⟨r+1,by omega⟩ / variableF ⟨r,by omega⟩)))
  have hR : (R.map (reflectSpectral n)).map (permSpectral σ) = R := by
    unfold R σ
    rw [sourceBlock_map, localR_map_hom, reflectSpectral_torusWeights,
      sourceBlock_map, localR_map_hom, permSpectral_torusWeights, perm_reflect_ratio]
  have h := congrArg (fun V : SourcePairing n → SpectralField n =>
      fun p => permSpectral σ (reflectSpectral n (V p)))
    (polynomialNorthSource_covariance r hr)
  funext p
  have hh := congrFun h p
  change permSpectral σ (reflectSpectral n (evalLaurent (polynomialNorthSource n p))) =
    permSpectral σ (reflectSpectral n (R.mulVec
      (fun q => permSpectral σ (evalLaurent (polynomialNorthSource n q))) p)) at hh
  rw [RingHom.map_mulVec, RingHom.map_mulVec, hR] at hh
  change _ = R.mulVec (fun q => permSpectral σ (reflectSpectral n
    (permSpectral σ (evalLaurent (polynomialNorthSource n q))))) p at hh
  have hv : (fun q => permSpectral σ (reflectSpectral n
    (permSpectral σ (evalLaurent (polynomialNorthSource n q))))) =
      (fun q => reflectSpectral n (evalLaurent (polynomialNorthSource n q))) := by
    funext q
    rw [reflectSpectral_perm]
    exact permSpectral_swap_involutive ⟨r,by omega⟩ ⟨r+1,by omega⟩ _
  rw [hv] at hh
  exact hh

 

lemma polynomialNorthGluing_exchange {n : ℕ} (r : ℕ) (hr : r+2≤n) :
    permLaurent (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩) (polynomialNorthGluing n) =
      polynomialNorthGluing n := by
  apply IsFractionRing.injective (SpectralRing n) (SpectralField n)
  change evalLaurent (permLaurent (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩)
    (polynomialNorthGluing n)) = evalLaurent (polynomialNorthGluing n)
  rw [←permSpectral_evalLaurent, polynomialNorthGluing_eval, sourceGlue_map]
  change sourceGlue n
    (fun p => permSpectral (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩)
      (reflectSpectral n (evalLaurent (polynomialNorthSource n p))))
    (fun p => permSpectral (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩)
      (evalLaurent (polynomialNorthSource n p))) = _
  rw [polynomialNorthSource_reflected_covariance r hr, ←sourceGlue_adjoint,
    ←polynomialNorthSource_covariance r hr]


end




end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SplitGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators

lemma rowReflectSpectral_involutive {n : ℕ} (i : Fin n) :
    Function.Involutive (rowReflectSpectral i) := by
  have h : (rowReflectSpectral i).comp (rowReflectSpectral i) = RingHom.id _ := by
    apply IsFractionRing.ringHom_ext (A := SpectralRing n)
    intro f
    change rowReflectSpectral i (rowReflectSpectral i (evalLaurent f)) = evalLaurent f
    rw [rowReflectSpectral_evalLaurent,rowReflectSpectral_evalLaurent,rowReflectLaurent_involutive]
  exact fun f => DFunLike.congr_fun h f

lemma reflectLaurent_rowReflect {n : ℕ} (i : Fin n) (f : Laurent n) :
    reflectLaurent n (rowReflectLaurent i f) = rowReflectLaurent i (reflectLaurent n f) := by
  have he (e : Fin n → ℤ) : ∑ j, reflectExponentAt i e j = ∑ j,e j - 2*e i := by
    rw [reflectExponentAt,Finset.sum_update_of_mem (Finset.mem_univ i)]
    have h := Finset.sum_sdiff (f:=e) (Finset.subset_univ ({i} : Finset (Fin n)))
    simp only [Finset.sum_singleton] at h
    omega
  have h : (reflectLaurent n).comp (rowReflectLaurent i) =
      (rowReflectLaurent i).comp (reflectLaurent n) := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change reflectLaurent n (rowReflectLaurent i (monomialL _ _)) =
      rowReflectLaurent i (reflectLaurent n (monomialL _ _))
    all_goals rw [rowReflectLaurent_monomial,reflectLaurent_monomial,
      reflectLaurent_monomial,rowReflectLaurent_monomial,reflectExponentAt_neg]
    all_goals simp only [mul_assoc,←zpow_add₀ phase_ne_zero,he,Pi.neg_apply]
    all_goals (congr 2; ring_nf)
  exact DFunLike.congr_fun h f

lemma reflectSpectral_rowReflect {n : ℕ} (i : Fin n) (f : SpectralField n) :
    reflectSpectral n (rowReflectSpectral i f) = rowReflectSpectral i (reflectSpectral n f) := by
  have h : (reflectSpectral n).comp (rowReflectSpectral i) =
      (rowReflectSpectral i).comp (reflectSpectral n) := by
    apply IsFractionRing.ringHom_ext (A := SpectralRing n)
    intro f
    change reflectSpectral n (rowReflectSpectral i (evalLaurent f)) =
      rowReflectSpectral i (reflectSpectral n (evalLaurent f))
    simp only [reflectSpectral_evalLaurent,rowReflectSpectral_evalLaurent,reflectLaurent_rowReflect]
  exact DFunLike.congr_fun h f

lemma rowReflectLaurent_perm {n : ℕ} (i : Fin n) (σ : Equiv.Perm (Fin n)) (f : Laurent n) :
    rowReflectLaurent (σ i) (permLaurent σ f) = permLaurent σ (rowReflectLaurent i f) := by
  have he (e : Fin n → ℤ) : reflectExponentAt (σ i) (e ∘ σ.symm) = reflectExponentAt i e ∘ σ.symm := by
    ext j
    by_cases h:j=σ i
    · simp [reflectExponentAt,h]
    · have h' : σ.symm j ≠ i := by intro hh; exact h ((σ.apply_symm_apply j).symm.trans (congrArg σ hh))
      simp [reflectExponentAt,h,h']
  have h : (rowReflectLaurent (σ i)).comp (permLaurent σ) =
      (permLaurent σ).comp (rowReflectLaurent i) := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change rowReflectLaurent (σ i) (permLaurent σ (monomialL _ _)) =
      permLaurent σ (rowReflectLaurent i (monomialL _ _))
    all_goals rw [permLaurent_monomial,rowReflectLaurent_monomial,
      rowReflectLaurent_monomial,permLaurent_monomial]
    all_goals simp only [Function.comp_apply,Equiv.symm_apply_apply]; congr 1; exact he _
  exact DFunLike.congr_fun h f

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_BottomGauge
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


lemma rawColumn_bottom_gauge {K : Type*} [CommRing K] {n : ℕ}
    (w v : Fin (n+1) → Tile → K) (a : K)
    (htail : ∀ i : Fin n, v i.succ = w i.succ)
    (hbottom : ∀ t : Tile, ¬t.Occupied 0 →
      v 0 t * (if t.Occupied 1 then a else 1) =
      (if t.Occupied 2 then a else 1) * w 0 t)
    (p q : Pairing (n+1)) :
    rawColumn v q p * occupancyGauge a p 0 = occupancyGauge a q 0 * rawColumn w q p := by
  simp only [rawColumn,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs with h
  · rw [Fin.prod_univ_succ,Fin.prod_univ_succ]
    simp only [htail]
    have hh := hbottom (t 0) (h.south 0 rfl)
    simp only [h.west,h.east] at hh
    change v 0 (t 0) * occupancyGauge a p 0 = occupancyGauge a q 0 * w 0 (t 0) at hh
    calc
      _ = (v 0 (t 0)*occupancyGauge a p 0) * ∏ i:Fin n,w i.succ (t i.succ) := by ring
      _ = _ := by rw [hh]; ring
  · simp

lemma lastCoefficient_bottom_gauge {K : Type*} [CommRing K] {n : ℕ}
    (w v : Fin (n+1) → Tile → K) (a : K)
    (htail : ∀ i : Fin n, v i.succ = w i.succ)
    (hbottom : ∀ t : Tile, ¬t.Occupied 0 →
      v 0 t * (if t.Occupied 1 then a else 1) =
      (if t.Occupied 2 then a else 1) * w 0 t)
    (p q : Pairing (n+1+1)) :
    lastCoefficient v q p * occupancyGauge a p 0 =
      occupancyGauge a q 0 * lastCoefficient w q p := by
  simp only [lastCoefficient,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs with h
  · rw [Fin.prod_univ_succ,Fin.prod_univ_succ]
    simp only [htail]
    have hs : ¬(t 0).Occupied 0 := by simpa using h.south 0 rfl
    have hw : (t 0).Occupied 1 ↔ p.Occupied 0 := by simpa using h.west 0
    have he : (t 0).Occupied 2 ↔ q.Occupied 0 := by simpa using h.east 0
    have hh := hbottom (t 0) hs
    simp only [hw,he] at hh
    change v 0 (t 0) * occupancyGauge a p 0 = occupancyGauge a q 0 * w 0 (t 0) at hh
    calc
      _ = (v 0 (t 0)*occupancyGauge a p 0) * ∏ i:Fin n,w i.succ (t i.succ) := by ring
      _ = _ := by rw [hh]; ring
  · simp

lemma Weights.vacantSouth_gauge {K : Type*} [Field K] (w v : Weights K)
    (hA : v.A=w.U) (hB : v.B=w.B) (hU : v.U=w.A) (hw : w.U≠0)
    (t : Tile) (ht : ¬t.Occupied 0) :
    v.tile t * (if t.Occupied 1 then w.A/w.U else 1) =
      (if t.Occupied 2 then w.A/w.U else 1) * w.tile t := by
  cases t <;> simp_all [Tile.Occupied,Tile.Adj,Tile.edges,Weights.tile]
  <;> field_simp

lemma matrix_mulVec_gauge {K : Type*} [CommRing K] {I J : Type*} [Fintype I]
    (M M' : Matrix J I K) (a : I → K) (b : J → K)
    (h : ∀ j i,M' j i*a i=b j*M j i) (v : I → K) :
    M'.mulVec (fun i=>a i*v i) = fun j=>b j*M.mulVec v j := by
  funext j
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [←mul_assoc,h]
  ring

lemma normalizedVacuum_gauge_pair {K : Type*} [Field K] {n : ℕ}
    (w v : Fin n → Weights K) (hw : VacuumRegular w) (hv : VacuumRegular v)
    (a : Pairing n → K) (he : a (empty n)=1)
    (hc : ∀ q p,column v q p*a p=a q*column w q p) :
    normalizedVacuum v = fun p=>a p*normalizedVacuum w p := by
  symm
  apply normalizedVacuum_unique _ hv
  constructor
  · change a (empty n)*normalizedVacuum w (empty n)=1
    rw [he,(normalizedVacuum_stationary w hw).1,one_mul]
  · rw [matrix_mulVec_gauge _ _ _ _ hc,(normalizedVacuum_stationary w hw).2]

 

 


lemma spectralRow_den_ne_zero {n : ℕ} (i : Fin n) : spectralA i + constF n C ≠ 0 := by
  rw [←twice_rowDenominator]
  exact mul_ne_zero (by norm_num) (rowDenominator_map_ne_zero i)

lemma rowReflectSpectral_weightsA {n : ℕ} (i : Fin n) :
    rowReflectSpectral i (spectralWeights n i).A = (spectralWeights n i).U := by
  have h := congrArg (rowReflectSpectral i) (clearedSpectralRow_vertical₀ i)
  simp only [clearedSpectralRow,Weights.tile,map_mul,map_add,map_ofNat,rowReflectSpectral_const,
    rowReflectSpectral_spectralA,rowReflectSpectral_torusSin,rowReflectSpectral_variable,ite_true] at h
  apply mul_left_cancel₀ (spectralRow_den_ne_zero i)
  exact h.trans (clearedSpectralRow_cap i).symm

lemma rowReflectSpectral_weightsU {n : ℕ} (i : Fin n) :
    rowReflectSpectral i (spectralWeights n i).U = (spectralWeights n i).A := by
  rw [←rowReflectSpectral_weightsA,rowReflectSpectral_involutive]

lemma rowReflectSpectral_weightsB {n : ℕ} (i : Fin n) :
    rowReflectSpectral i (spectralWeights n i).B = (spectralWeights n i).B := by
  have h := congrArg (rowReflectSpectral i) (clearedSpectralRow_diagonal₁ i)
  simp only [clearedSpectralRow,Weights.tile,map_mul,map_add,map_sub,rowReflectSpectral_const,
    rowReflectSpectral_spectralA] at h
  apply mul_left_cancel₀ (spectralRow_den_ne_zero i)
  exact h.trans (clearedSpectralRow_diagonal₁ i).symm

lemma spectralWeights_A_ne_zero {n : ℕ} (i : Fin n) : (spectralWeights n i).A≠0 := by
  have hd : constF n d ≠0 :=
    (map_ne_zero (algebraMap ℂ (SpectralField n))).mpr (by exact_mod_cast d_ne_zero)
  have hs : torusSin (variableF i)≠0 := by
    apply torusSin_monomial_ne_zero _ _ 1 one_ne_zero
    intro he
    have h := congrFun he i
    simp [variableExponent] at h
  have h := mul_ne_zero (mul_ne_zero (by norm_num : (2:SpectralField n)≠0) hd) hs
  rw [←clearedSpectralRow_vertical₀] at h
  exact (mul_ne_zero_iff.mp h).2

lemma spectralWeights_U_ne_zero {n : ℕ} (i : Fin n) : (spectralWeights n i).U≠0 := by
  rw [←rowReflectSpectral_weightsA]
  exact (map_ne_zero (rowReflectSpectral i)).mpr (spectralWeights_A_ne_zero i)

lemma rowReflectSpectral_weights_other {n : ℕ} (i j : Fin n) (h : j≠i) :
    (spectralWeights n j).map (rowReflectSpectral i) = spectralWeights n j := by
  simp only [spectralWeights,rowReflectSpectral_torusWeights,map_div₀,map_pow,
    rowReflectSpectral_const,rowReflectSpectral_variable,ite_eq_right h]

lemma rowGauge_ne_zero {n : ℕ} (i : Fin n) : rowGauge i ≠0 :=
  div_ne_zero (spectralWeights_A_ne_zero i) (spectralWeights_U_ne_zero i)

lemma reflectSpectral_rowGauge {n : ℕ} (i : Fin n) :
    reflectSpectral n (rowGauge i) = (rowGauge i)⁻¹ := by
  have h : (spectralWeights n i).map (reflectSpectral n) =
      (spectralWeights n i).map (rowReflectSpectral i) := by
    simp only [spectralWeights,reflectSpectral_torusWeights,rowReflectSpectral_torusWeights,
      map_div₀,map_pow,reflectSpectral_const,rowReflectSpectral_const,
      reflectSpectral_variable,rowReflectSpectral_variable,ite_true]
  have ha := congrArg Weights.A h
  have hu := congrArg Weights.U h
  change reflectSpectral n (spectralWeights n i).A = rowReflectSpectral i (spectralWeights n i).A at ha
  change reflectSpectral n (spectralWeights n i).U = rowReflectSpectral i (spectralWeights n i).U at hu
  simp only [rowGauge,map_div₀,ha,hu,rowReflectSpectral_weightsA,rowReflectSpectral_weightsU,inv_div]

lemma rowReflectSpectral_bottom_tile (n : ℕ) (t : Tile) (ht : ¬t.Occupied 0) :
    rowReflectSpectral (0:Fin (n+1)) ((spectralWeights (n+1) 0).tile t) *
      (if t.Occupied 1 then rowGauge (0:Fin (n+1)) else 1) =
    (if t.Occupied 2 then rowGauge (0:Fin (n+1)) else 1) * (spectralWeights (n+1) 0).tile t := by
  have h := Weights.vacantSouth_gauge (spectralWeights (n+1) 0)
      ((spectralWeights (n+1) 0).map (rowReflectSpectral 0))
      (rowReflectSpectral_weightsA 0) (rowReflectSpectral_weightsB 0)
      (rowReflectSpectral_weightsU 0) (spectralWeights_U_ne_zero 0) t ht
  simpa [Weights.map_tile, rowGauge] using h

lemma rowReflectSpectral_bottom_column (n : ℕ) (p q : Pairing (n+1)) :
    rowReflectSpectral (0:Fin (n+1)) (column (spectralWeights (n+1)) q p) *
      occupancyGauge (rowGauge (0:Fin (n+1))) p 0 =
    occupancyGauge (rowGauge (0:Fin (n+1))) q 0 * column (spectralWeights (n+1)) q p := by
  rw [column_eq_raw]
  have hmap := congrFun (congrFun (rawColumn_map (rowReflectSpectral (0:Fin (n+1)))
    (fun i=>(spectralWeights (n+1) i).tile)) q) p
  rw [Matrix.map_apply] at hmap
  rw [hmap]
  apply rawColumn_bottom_gauge _ _ _ _ (rowReflectSpectral_bottom_tile n) p q
  intro i
  have h := rowReflectSpectral_weights_other (0:Fin (n+1)) i.succ (Fin.succ_ne_zero i)
  funext t
  have hh := congrArg (fun w=>w.tile t) h
  simpa [Weights.map_tile] using hh

lemma rowReflectSpectral_bottom_lastCoefficient (n : ℕ) (p q : Pairing (n+1+1)) :
    rowReflectSpectral (0:Fin (n+1)) (lastCoefficient (fun i=>(spectralWeights (n+1) i).tile) q p) *
      occupancyGauge (rowGauge (0:Fin (n+1))) p 0 =
    occupancyGauge (rowGauge (0:Fin (n+1))) q 0 *
      lastCoefficient (fun i=>(spectralWeights (n+1) i).tile) q p := by
  rw [←lastCoefficient_map]
  apply lastCoefficient_bottom_gauge _ _ _ _ (rowReflectSpectral_bottom_tile n) p q
  intro i
  have h := rowReflectSpectral_weights_other (0:Fin (n+1)) i.succ (Fin.succ_ne_zero i)
  funext t
  have hh := congrArg (fun w=>w.tile t) h
  simpa [Weights.map_tile] using hh

lemma rowReflectSpectral_bottom_vacuum (n : ℕ) (p : Pairing (n+1)) :
    rowReflectSpectral (0:Fin (n+1)) (normalizedVacuum (spectralWeights (n+1)) p) =
      occupancyGauge (rowGauge (0:Fin (n+1))) p 0 * normalizedVacuum (spectralWeights (n+1)) p := by
  have hm := normalizedVacuum_map (rowReflectSpectral (0:Fin (n+1))) (spectralWeights (n+1))
    (spectral_regular (n+1))
  have hv := (spectral_regular (n+1)).map (rowReflectSpectral (0:Fin (n+1))) (spectralWeights (n+1))
  have hc (q p : Pairing (n+1)) : column
      (fun i=>(spectralWeights (n+1) i).map (rowReflectSpectral 0)) q p *
      occupancyGauge (rowGauge (0:Fin (n+1))) p 0 =
    occupancyGauge (rowGauge (0:Fin (n+1))) q 0 * column (spectralWeights (n+1)) q p := by
    rw [←column_map]
    exact rowReflectSpectral_bottom_column n p q
  rw [normalizedVacuum_gauge_pair _ _ (spectral_regular (n+1)) hv _
    (occupancyGauge_empty _ _) hc] at hm
  exact congrFun hm p

lemma rowReflectSpectral_bottom_rationalVacuum (n : ℕ) (p : Pairing (n+1)) :
    rowReflectSpectral (0:Fin (n+1)) (rationalVacuum (n+1) p) =
      occupancyGauge (rowGauge (0:Fin (n+1))) p 0 * rationalVacuum (n+1) p := by
  simp only [rationalVacuum,map_mul,rowReflectSpectral_normalization,rowReflectSpectral_bottom_vacuum]
  ring

 

 


lemma matrix_one_sub_gauge {K : Type*} [CommRing K] {I : Type*} [Fintype I] [DecidableEq I]
    (M M' : Matrix I I K) (a : I → K)
    (h : ∀ j i, M' j i*a i=a j*M j i) :
    ∀ j i, (1-M') j i*a i=a j*(1-M) j i := by
  classical
  intro j i
  simp only [Matrix.sub_apply,sub_mul,mul_sub,h]
  congr 1
  by_cases he : j=i
  · subst i; simp
  · simp [he]

lemma rowReflectSpectral_bottom_sourceTransfer (n : ℕ)
    (p q : SourcePairing (n+1)) :
    rowReflectSpectral (0:Fin (n+1))
      (sourceTransfer (fun i=>(spectralWeights (n+1) i).tile) q p) *
      occupancyGauge (rowGauge (0:Fin (n+1))) p.val 0 =
    occupancyGauge (rowGauge (0:Fin (n+1))) q.val 0 *
      sourceTransfer (fun i=>(spectralWeights (n+1) i).tile) q p :=
  rowReflectSpectral_bottom_lastCoefficient n p.val q.val

lemma rowReflectSpectral_bottom_northSource (n : ℕ)
    (p : Pairing (n+1)) (q : SourcePairing (n+1)) :
    rowReflectSpectral (0:Fin (n+1))
      (northSource (fun i=>(spectralWeights (n+1) i).tile) q p) *
      occupancyGauge (rowGauge (0:Fin (n+1))) p 0 =
    occupancyGauge (rowGauge (0:Fin (n+1))) q.val 0 *
      northSource (fun i=>(spectralWeights (n+1) i).tile) q p := by
  classical
  have h := rowReflectSpectral_bottom_lastCoefficient n p.padTop q.val
  have he : occupancyGauge (rowGauge (0:Fin (n+1))) p.padTop 0 =
      occupancyGauge (rowGauge (0:Fin (n+1))) p 0 := by
    change (if p.padTop.Occupied (0:Fin (n+1)).castSucc then _ else _) = _
    simp only [Pairing.padTop_occupied_castSucc,occupancyGauge]
  simpa only [northSource,he] using h

 

lemma rowReflectSpectral_bottom_northNumerator (n : ℕ) (p : SourcePairing (n+1)) :
    rowReflectSpectral (0:Fin (n+1)) (northNumerator (n+1) p) =
      occupancyGauge (rowGauge (0:Fin (n+1))) p.val 0 * northNumerator (n+1) p := by
  classical
  let f := rowReflectSpectral (0:Fin (n+1))
  let T := sourceTransfer (fun i=>(spectralWeights (n+1) i).tile)
  let B := northSource (fun i=>(spectralWeights (n+1) i).tile)
  let a := fun q : SourcePairing (n+1) => occupancyGauge (rowGauge (0:Fin (n+1))) q.val 0
  let b := fun q : Pairing (n+1) => occupancyGauge (rowGauge (0:Fin (n+1))) q 0
  have hT : ∀ j i,T.map f j i*a i=a j*T j i :=
    fun j i => rowReflectSpectral_bottom_sourceTransfer n i j
  have hB : ∀ j i,B.map f j i*b i=a j*B j i :=
    fun j i => rowReflectSpectral_bottom_northSource n i j
  have hmap : (1-T).map f = 1-T.map f := by
    ext j i
    simp only [Matrix.map_apply,Matrix.sub_apply,map_sub,Matrix.one_apply,apply_ite,map_one,map_zero]
  have hd : (1-T.map f).det≠0 := by
    rw [←hmap]
    change (f.mapMatrix (1-T)).det≠0
    rw [←RingHom.map_det]
    exact (map_ne_zero f).mpr (spectral_source_regular (n+1))
  have he := congrArg (fun v : SourcePairing (n+1) → SpectralField (n+1) =>
      fun q => f (v q)) (northNumerator_equation (n+1))
  have hv : (fun q => f (rationalVacuum (n+1) q)) =
      fun q => b q*rationalVacuum (n+1) q := by
    funext q
    exact rowReflectSpectral_bottom_rationalVacuum n q
  have hf : f (2*constF (n+1) d)=2*constF (n+1) d := by
    simp only [f, map_mul,map_ofNat,rowReflectSpectral_const]
  have he' : (1-T.map f).mulVec (fun q=>f (northNumerator (n+1) q)) =
      fun q=>(2*constF (n+1) d)*(B.map f).mulVec (fun q=>b q*rationalVacuum (n+1) q) q := by
    funext q
    have hh := congrFun he q
    change f ((1-T).mulVec (northNumerator (n+1)) q) =
      f ((2*constF (n+1) d)*B.mulVec (rationalVacuum (n+1)) q) at hh
    rw [RingHom.map_mulVec,hmap,map_mul,hf,
      RingHom.map_mulVec] at hh
    change _ = (2*constF (n+1) d)*(B.map f).mulVec (fun q=>f (rationalVacuum (n+1) q)) q at hh
    rw [hv] at hh
    exact hh
  have hm := matrix_mulVec_gauge (1-T) (1-T.map f) a a
    (matrix_one_sub_gauge T (T.map f) a hT) (northNumerator (n+1))
  have hh : (fun q=> f (northNumerator (n+1) q)) =
      (fun q=>a q*northNumerator (n+1) q) := by
    apply Matrix.mulVec_injective_of_det_ne_zero hd
    rw [he',hm,matrix_mulVec_gauge B (B.map f) b a hB]
    change (fun q=>(2*constF (n+1) d)*(a q*B.mulVec (rationalVacuum (n+1)) q)) =
      fun q=>a q*(1-T).mulVec (northNumerator (n+1)) q
    rw [northNumerator_equation]
    funext q
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  exact congrFun hh p

lemma polynomialNorthSource_bottom_reflection (n : ℕ) (p : SourcePairing (n+1)) :
    rowReflectSpectral (0:Fin (n+1)) (evalLaurent (polynomialNorthSource (n+1) p)) =
      occupancyGauge (rowGauge (0:Fin (n+1))) p.val 0 *
        evalLaurent (polynomialNorthSource (n+1) p) := by
  classical
  simp only [polynomialNorthSource_eval_numerator,map_mul,rowReflectSpectral_const,
    rowReflectSpectral_bottom_northNumerator]
  ring

lemma map_occupancyGauge {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    {n : ℕ} (a : K) (p : Pairing n) (i : Fin n) :
    f (occupancyGauge a p i) = occupancyGauge (f a) p i := by
  classical
  unfold occupancyGauge
  split_ifs <;> simp

lemma sourceGlue_gauge {K : Type*} [Field K] (n : ℕ) (a : K) (ha : a≠0)
    (v w : SourcePairing n → K) (i : Fin (n+1)) :
    sourceGlue n (fun p=>occupancyGauge a⁻¹ p.val i*v p)
      (fun p=>occupancyGauge a p.val i*w p) = sourceGlue n v w := by
  classical
  rw [sourceGlue_eq_sum,sourceGlue_eq_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  split_ifs with h
  · rw [one_mul,one_mul]
    simp only [occupancyGauge,h.2.1 i]
    split_ifs
    · field_simp
    · simp
  · simp

 

theorem polynomialNorthGluing_bottom_reflection (n : ℕ) :
    rowReflectLaurent (0:Fin (n+1)) (polynomialNorthGluing (n+1)) =
      polynomialNorthGluing (n+1) := by
  classical
  apply IsFractionRing.injective (SpectralRing (n+1)) (SpectralField (n+1))
  change evalLaurent (rowReflectLaurent 0 (polynomialNorthGluing (n+1))) =
    evalLaurent (polynomialNorthGluing (n+1))
  rw [←rowReflectSpectral_evalLaurent,polynomialNorthGluing_eval,sourceGlue_map]
  simp only [Function.comp_def,←reflectSpectral_rowReflect,
    polynomialNorthSource_bottom_reflection,map_mul,map_occupancyGauge,
    reflectSpectral_rowGauge]
  exact sourceGlue_gauge _ _ (rowGauge_ne_zero _) _ _ _

 

theorem polynomialNorthGluing_row_reflection_oai {n : ℕ} (i : Fin n) :
    rowReflectLaurent i (polynomialNorthGluing n) = polynomialNorthGluing n := by
  classical
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := i.isLt; omega : n≠0)
  have h : ∀ k (hk : k<n+1), rowReflectLaurent ⟨k,hk⟩ (polynomialNorthGluing (n+1)) =
      polynomialNorthGluing (n+1) := by
    intro k
    induction k with
    | zero => intro hk; exact polynomialNorthGluing_bottom_reflection n
    | succ k ih =>
      intro hk
      let j : Fin (n+1) := ⟨k,by omega⟩
      let j' : Fin (n+1) := ⟨k+1,hk⟩
      have hx := polynomialNorthGluing_exchange k (by omega : k+2≤n+1)
      have hr := rowReflectLaurent_perm j (Equiv.swap j j') (polynomialNorthGluing (n+1))
      simp only [Equiv.swap_apply_left] at hr
      change permLaurent (Equiv.swap j j') (polynomialNorthGluing (n+1)) = _ at hx
      rw [hx,ih] at hr
      exact hr.trans hx
  exact h i.val i.isLt

end




end CriticalStrip.Diagram

end OAI
end

theorem solution : type_of% @OAI.CriticalStrip.Diagram.polynomialNorthGluing_row_reflection_oai := @OAI.CriticalStrip.Diagram.polynomialNorthGluing_row_reflection_oai
