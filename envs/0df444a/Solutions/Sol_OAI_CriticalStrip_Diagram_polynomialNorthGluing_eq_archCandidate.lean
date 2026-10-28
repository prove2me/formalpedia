-- Prove2me | solution 1 for OAI.CriticalStrip.Diagram.polynomialNorthGluing_eq_archCandidate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T02:27:50.589891+00:00
-- url     : https://prove2.me/submissions/839e4728-fbe1-46f2-956e-ae343dce3397

import Mathlib
import Definitions.Def_OAIQ042S015
import Theorems.Thm_OAI_CriticalStrip_Diagram_polynomialNorthGluing_delete
import Theorems.Thm_OAI_CriticalStrip_Diagram_polynomialNorthGluing_merge
import Theorems.Thm_OAI_CriticalStrip_Diagram_polynomialNorthGluing_row_reflection

section
-- module Solutions.OAIQ042_SS.StripMass_LocalPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical
open Finset

variable {K : Type*} [CommRing K]

lemma functionMatrix_mul {P Q R : Type*} [Fintype Q] (f : P → Q) (g : Q → R) :
    (functionMatrix (K := K) g : Matrix R Q K) * functionMatrix (K := K) f = functionMatrix (g ∘ f) := by
  exact optionMatrix_mul (some ∘ f) (some ∘ g)

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



theorem polynomialNorthSource_box (n : ℕ) (p : SourcePairing n) :
    LaurentBox (polynomialNorthSource n p) (fun _ => 2*n) := by
  simpa only [polynomialNorthSource, zero_add] using (LaurentBox.constant (1/(2*(d:ℂ)))).mul
    ((vacuumData n).box_P p.val (n-1))

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



lemma glueMatrix_transpose {K : Type*} [Zero K] [One K] {n : ℕ} (root : Fin n) :
    (glueMatrix root : Matrix _ _ K).transpose = glueMatrix root := by
  ext p q
  simp only [Matrix.transpose_apply,glueMatrix,Pairing.gluesAt_comm root q p]

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

lemma northNumerator_parity {n : ℕ} (k : Fin n) (p : SourcePairing n) :
    signSpectral k (northNumerator n p) =
      occupancySign p.val k.castSucc * northNumerator n p := by
  have h := congrArg (fun P : Polynomial (SpectralField n) => P.coeff (n-1))
    (rationalNodalPolynomial_parity k p.val)
  simpa [northNumerator] using h



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

lemma reflectLaurent_sign {n : ℕ} (i : Fin n) (f : Laurent n) :
    reflectLaurent n (signLaurent i f) = signLaurent i (reflectLaurent n f) := by
  have h : (reflectLaurent n).comp (signLaurent i) =
      (signLaurent i).comp (reflectLaurent n) := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change reflectLaurent n (signLaurent i (monomialL _ _)) =
      signLaurent i (reflectLaurent n (monomialL _ _))
    all_goals rw [signLaurent_monomial, reflectLaurent_monomial,
      reflectLaurent_monomial, signLaurent_monomial]
    all_goals simp only [Pi.neg_apply, zpow_neg, ←inv_zpow, inv_neg_one]; congr 1; ring
  exact DFunLike.congr_fun h f

lemma reflectSpectral_sign {n : ℕ} (i : Fin n) (f : SpectralField n) :
    reflectSpectral n (signSpectral i f) = signSpectral i (reflectSpectral n f) := by
  have h : (reflectSpectral n).comp (signSpectral i) =
      (signSpectral i).comp (reflectSpectral n) := by
    apply IsFractionRing.ringHom_ext (A := SpectralRing n)
    intro f
    change reflectSpectral n (signSpectral i (evalLaurent f)) =
      signSpectral i (reflectSpectral n (evalLaurent f))
    simp only [reflectSpectral_evalLaurent, signSpectral_evalLaurent, reflectLaurent_sign]
  exact DFunLike.congr_fun h f

lemma LaurentBox.reflect {n : ℕ} {f : Laurent n} {b : Fin n → ℕ}
    (hf : LaurentBox f b) : LaurentBox (reflectLaurent n f) b := by
  rw [←AddMonoidAlgebra.sum_coeff_single f]
  change LaurentBox (reflectLaurent n (∑ e ∈ f.coeff.support, monomialL e (f.coeff e))) b
  rw [map_sum]
  apply LaurentBox.sum
  intro e he
  rw [reflectLaurent_monomial]
  apply LaurentBox.single
  intro i
  have hh := hf e (Finsupp.mem_support_iff.mp he) i
  simp only [Pi.neg_apply]
  omega



 


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


lemma sourceGlue_symmetric {K : Type*} [CommRing K] (n : ℕ)
    (v w : SourcePairing n → K) : sourceGlue n v w = sourceGlue n w v := by
  unfold sourceGlue
  rw [Matrix.dotProduct_mulVec, ←glueMatrix_transpose (Fin.last n),
    sourceBlock_transpose,Matrix.vecMul_transpose, dotProduct_comm]
  rw [← sourceBlock_transpose, glueMatrix_transpose]

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

lemma polynomialNorthSource_parity {n : ℕ} (k : Fin n) (p : SourcePairing n) :
    signSpectral k (evalLaurent (polynomialNorthSource n p)) =
      occupancySign p.val k.castSucc * evalLaurent (polynomialNorthSource n p) := by
  simp only [polynomialNorthSource_eval_numerator, map_mul, signSpectral_const,
    northNumerator_parity]
  ring

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
lemma polynomialNorthGluing_box (n : ℕ) :
    LaurentBox (polynomialNorthGluing n) (fun _ => 4*n) := by
  rw [polynomialNorthGluing, sourceGlue_eq_sum]
  apply LaurentBox.sum
  intro p _
  apply LaurentBox.sum
  intro q _
  split_ifs
  · rw [one_mul]
    convert (polynomialNorthSource_box n p).reflect.mul (polynomialNorthSource_box n q) using 1
    all_goals try with_reducible_and_instances rfl
    ext i
    change 4*n = 2*n+2*n
    omega
  · simp only [zero_mul,mul_zero]
    exact LaurentBox.zero _

lemma map_occupancySign {K L : Type*} [Ring K] [Ring L]
    (f : K →+* L) {n : ℕ} (p : Pairing n) (i : Fin n) :
    f (occupancySign p i) = occupancySign p i := by
  unfold occupancySign
  split_ifs <;> simp

lemma sourceGlue_signTwist {K : Type*} [CommRing K] (n : ℕ)
    (v w : SourcePairing n → K) (i : Fin (n+1)) :
    sourceGlue n (fun p => occupancySign p.val i * v p)
        (fun p => occupancySign p.val i * w p) = sourceGlue n v w := by
  rw [sourceGlue_eq_sum, sourceGlue_eq_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  split_ifs with h
  · rw [one_mul, one_mul]
    have hs : (occupancySign p.val i : K) = occupancySign q.val i := by
      simp only [occupancySign, h.2.1 i]
    rw [hs]
    calc
      _ = (occupancySign q.val i * occupancySign q.val i) * (v p * w q) := by ring
      _ = _ := by rw [occupancySign_mul_self,one_mul]
  · simp

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

 
lemma polynomialNorthGluing_parity (n : ℕ) (i : Fin n) :
    signLaurent i (polynomialNorthGluing n) = polynomialNorthGluing n := by
  apply IsFractionRing.injective (SpectralRing n) (SpectralField n)
  change evalLaurent (signLaurent i (polynomialNorthGluing n)) =
    evalLaurent (polynomialNorthGluing n)
  rw [←signSpectral_evalLaurent, polynomialNorthGluing_eval, sourceGlue_map]
  simp only [Function.comp_def, ←reflectSpectral_sign, polynomialNorthSource_parity,
    map_mul, map_occupancySign]
  exact sourceGlue_signTwist n _ _ _

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


lemma sourceGlue_scale {K : Type*} [CommRing K] (n : ℕ) (a b : K)
    (v w : SourcePairing n → K) :
    sourceGlue n (a • v) (b • w) = (a*b)*sourceGlue n v w := by
  simp only [sourceGlue,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  ring



end




end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SplitProjection
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

lemma join_map {n m : ℕ} (f : Fin n ↪o Fin m) (p q : Pairing n) (i j : Fin m) :
    join (p.map f) (q.map f) i j ↔ ∃ a b, join p q a b ∧ f a=i ∧ f b=j := by
  simp only [join,map_adj]
  constructor
  · rintro (⟨a,b,h,rfl,rfl⟩|⟨a,b,h,rfl,rfl⟩)
    · exact ⟨a,b,Or.inl h,rfl,rfl⟩
    · exact ⟨a,b,Or.inr h,rfl,rfl⟩
  · rintro ⟨a,b,h,rfl,rfl⟩
    exact h.elim (fun hh => Or.inl ⟨a,b,hh,rfl,rfl⟩)
      (fun hh => Or.inr ⟨a,b,hh,rfl,rfl⟩)

lemma join_map_reach {n m : ℕ} (f : Fin n ↪o Fin m) (p q : Pairing n) (i j : Fin n) :
    Relation.ReflTransGen (join (p.map f) (q.map f)) (f i) (f j) ↔
      Relation.ReflTransGen (join p q) i j := by
  constructor
  · intro hh
    have h : ∀ {y}, Relation.ReflTransGen (join (p.map f) (q.map f)) (f i) y →
        ∃ k, f k=y ∧ Relation.ReflTransGen (join p q) i k := by
      intro y hy
      induction hy with
      | refl => exact ⟨i,rfl,.refl⟩
      | @tail y z hy hyz ih =>
        obtain ⟨k,hk,hpath⟩ := ih
        obtain ⟨a,b,hab,ha,hb⟩ := (join_map f p q y z).mp hyz
        have hka : k=a := f.injective (hk.trans ha.symm)
        subst k
        exact ⟨b,hb,hpath.tail hab⟩
    obtain ⟨k,hk,hpath⟩ := h hh
    exact f.injective hk ▸ hpath
  · intro hh
    exact Graph.map_reach f (fun a b hab => .single
      ((join_map f p q (f a) (f b)).mpr ⟨a,b,hab,rfl,rfl⟩)) hh

lemma gluesAt_map {n m : ℕ} (f : Fin n ↪o Fin m) (root : Fin n) (p q : Pairing n) :
    GluesAt (f root) (p.map f) (q.map f) ↔ GluesAt root p q := by
  constructor
  · rintro ⟨hp,ho,hd⟩
    refine ⟨(map_occupied f p root).mp hp,?_,?_⟩
    · intro i
      simpa only [map_occupied] using ho (f i)
    · intro i j hij
      apply (join_map_reach f p q i root).mp
      exact hd (f i) (f j) ((join_map f p q _ _).mpr ⟨i,j,hij,rfl,rfl⟩)
  · rintro ⟨hp,ho,hd⟩
    refine ⟨(map_occupied f p root).mpr hp,?_,?_⟩
    · intro i
      constructor
      · rintro ⟨j,hij⟩
        obtain ⟨a,b,hab,rfl,rfl⟩ := (map_adj f p i j).mp hij
        exact (map_occupied f q a).mpr ((ho a).mp ⟨b,hab⟩)
      · rintro ⟨j,hij⟩
        obtain ⟨a,b,hab,rfl,rfl⟩ := (map_adj f q i j).mp hij
        exact (map_occupied f p a).mpr ((ho a).mpr ⟨b,hab⟩)
    · intro i j hij
      obtain ⟨a,b,hab,rfl,rfl⟩ := (join_map f p q i j).mp hij
      exact (join_map_reach f p q a root).mpr (hd a b hab)

end Pairing



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ProjectionInjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators



lemma torusEvaluation_twistedReflect {n m : ℕ} (k : Fin n → ℤ)
    (z : Fin n → SpectralField m) (hz : ∀ i,z i≠0) (f : Laurent n) :
    torusEvaluation z hz (twistedReflectLaurent k f) =
      torusEvaluation (fun i => constF m phase^k i/z i)
        (fun i =>div_ne_zero (zpow_ne_zero _ (constF_phase_ne_zero m)) (hz i)) f := by
  have he : (torusEvaluation z hz).toRingHom.comp (twistedReflectLaurent k) =
      (torusEvaluation (fun i => constF m phase^k i/z i)
        (fun i =>div_ne_zero (zpow_ne_zero _ (constF_phase_ne_zero m)) (hz i))).toRingHom := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change torusEvaluation z hz (twistedReflectLaurent k (monomialL _ _)) =
      torusEvaluation _ _ (monomialL _ _)
    all_goals rw [twistedReflectLaurent_monomial]
    all_goals simp only [torusEvaluation_monomial,constF,map_mul,map_prod,map_zpow₀,
      Pi.neg_apply,zpow_neg,zpow_mul,div_eq_mul_inv,mul_zpow,inv_zpow,
      Finset.prod_mul_distrib,mul_assoc]
  exact DFunLike.congr_fun he f

lemma sum_zpow_eq_prod {K : Type*} [CommGroupWithZero K] {ι : Type*}
    (a : K) (ha : a≠0) (s : Finset ι) (v : ι → ℤ) :
    a^(∑ i∈s,v i) = ∏ i∈s,a^v i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [Finset.sum_insert hi,Finset.prod_insert hi,zpow_add₀ ha,ih]

lemma reflectLaurent_eq_twisted (n : ℕ) : reflectLaurent n=twistedReflectLaurent (fun _:Fin n =>3) := by
  apply AddMonoidAlgebra.ringHom_ext <;> intro e
  all_goals change reflectLaurent n (monomialL _ _) = twistedReflectLaurent _ (monomialL _ _)
  all_goals rw [reflectLaurent_monomial,twistedReflectLaurent_monomial,
    Finset.mul_sum,sum_zpow_eq_prod phase phase_ne_zero]

lemma torusEvaluation_reflect {n m : ℕ} (z : Fin n → SpectralField m)
    (hz : ∀ i,z i≠0) (f : Laurent n) :
    torusEvaluation z hz (reflectLaurent n f) =
      torusEvaluation (fun i => constF m phase^3/z i)
        (fun i =>div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero m)) (hz i)) f := by
  rw [reflectLaurent_eq_twisted,torusEvaluation_twistedReflect]
  rfl



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SplitGluing
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

lemma sourceGlue_smul_right {K : Type*} [CommRing K] (n : ℕ) (a : K)
    (v w : SourcePairing n → K) : sourceGlue n v (a • w) = a*sourceGlue n v w := by
  simpa only [one_smul,one_mul] using sourceGlue_scale n (1:K) a v w

lemma sourceGlue_smul_left {K : Type*} [CommRing K] (n : ℕ) (a : K)
    (v w : SourcePairing n → K) : sourceGlue n (a • v) w = a*sourceGlue n v w := by
  simpa only [one_smul,mul_one] using sourceGlue_scale n a (1:K) v w

lemma sourceGlue_algMap {R K L : Type*} [CommSemiring R] [CommRing K] [CommRing L]
    [Algebra R K] [Algebra R L] (f : K →ₐ[R] L) (n : ℕ)
    (v w : SourcePairing n → K) :
    f (sourceGlue n v w) = sourceGlue n (f ∘ v) (f ∘ w) :=
  sourceGlue_map f.toRingHom n v w






lemma lastCoefficient_cons_padBottom {K : Type*} [CommRing K] {n : ℕ}
    (r : Tile → K) (w : Fin n → Tile → K) (p q : Pairing (n+1)) :
    lastCoefficient (Fin.cons r w) q.padBottom p.padBottom =
      r .vacant * lastCoefficient w q p := by
  have h := rawColumn_padBottom (Fin.snoc w (fun _ => (1:K))) r p q
  rw [Fin.cons_snoc_eq_snoc_cons,rawColumn_last_factor,rawColumn_last_factor] at h
  simpa only [mul_one] using h

lemma lastFactor_padBottom {K : Type*} [CommRing K] {n : ℕ}
    (d c C : K) (p q : Pairing (n+1)) :
    lastFactor d c C p.padBottom q.padBottom = lastFactor d c C p q := by
  simp only [lastFactor,←Fin.succ_last,Pairing.padBottom_occupied_succ]

lemma firstZeroPolynomial_padBottom {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (d c C : K)
    (P : Pairing (n+1) → Polynomial K) (q : Pairing (n+1)) :
    firstZeroPolynomial w d c C P q.padBottom = lastTransform w d c C P q := by
  unfold firstZeroPolynomial lastTransform
  symm
  apply Fintype.sum_of_injective Pairing.padBottom Pairing.padBottom_injective
  · intro p hp
    have h : p.Occupied 0 := by
      by_contra h
      exact hp ⟨p.restrict (Fin.succOrderEmb (n+1)),p.padBottom_restrict h⟩
    simp [vacantBottomExtension,h]
  · intro p
    rw [lastCoefficient_cons_padBottom,lastFactor_padBottom,vacantBottomExtension_padBottom]
    simp [Weights.tile]

lemma rationalFirstZeroPolynomial_vacant (n : ℕ) (q : Pairing (n+1)) :
    firstZeroPolynomial (fun j => (spectralWeights n j).tile)
      (constF n d) (constF n c) (constF n C) (rationalNodalPolynomial n) q.padBottom =
      (Polynomial.X+Polynomial.C (constF n C))*rationalNodalPolynomial n q := by
  rw [firstZeroPolynomial_padBottom]
  exact sub_eq_zero.mp (rationalResidualPolynomial_zero n q)


lemma SourcePairing.padBottom_injective {n : ℕ} :
    Function.Injective (@SourcePairing.padBottom n) := by
  intro p q h
  exact Subtype.ext (Pairing.padBottom_injective (congrArg Subtype.val h))

lemma SourcePairing.padBottom_range {n : ℕ} (p : SourcePairing (n+1)) :
    p ∈ Set.range SourcePairing.padBottom ↔ ¬p.val.Occupied 0 := by
  constructor
  · rintro ⟨q,rfl⟩
    exact q.val.padBottom_not_occupied_zero
  · intro h
    have hp := p.val.padBottom_restrict h
    let q := p.val.restrict (Fin.succOrderEmb (n+1))
    have hq : q.Occupied (Fin.last n) := by
      rw [←Pairing.padBottom_occupied_succ q (Fin.last n),hp]
      exact p.property
    exact ⟨⟨q,hq⟩,Subtype.ext hp⟩

lemma vacantBottomSourceExtension_padBottom {K : Type*} [Zero K] {n : ℕ}
    (v : SourcePairing n → K) (q : SourcePairing n) :
    vacantBottomSourceExtension v q.padBottom=v q := by
  rw [vacantBottomSourceExtension,dite_eq_left ⟨q,rfl⟩]
  congr 1
  exact SourcePairing.padBottom_injective (Classical.choose_spec (show q.padBottom ∈ Set.range SourcePairing.padBottom from ⟨q,rfl⟩))

lemma coefficient_X_add_source {n : ℕ} (p : SourcePairing n) :
    ((Polynomial.X+Polynomial.C (constF n C))*rationalNodalPolynomial n p.val).coeff n =
      northNumerator n p := by
  by_cases hn : n=0
  · subst n
    exact (p.ne_empty (p.val.eq_empty_of_le_one (by omega))).elim
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hz := rationalNodalPolynomial_degree (k+1) p.val (k+1) (by simp [p.property])
    simp only [add_mul,Polynomial.coeff_add,Polynomial.coeff_X_mul,Polynomial.coeff_C_mul,hz,
      mul_zero,add_zero,northNumerator,Nat.succ_sub_one]

 

theorem polynomialNorthSource_firstFlat (n : ℕ) (p : SourcePairing n) :
    firstFlatEvaluation n (polynomialNorthSource (n+1) p.padBottom) =
      (∏ j:Fin n,(spectralA j+constF n C))*evalLaurent (polynomialNorthSource n p) := by
  have h := congrFun (rationalNodalPolynomial_firstFlat
    (vacuumData n).interpolant (vacuumData (n+1)).P
    (vacuumData (n+1)).map_P) p.val.padBottom
  have hc := congrArg (fun P : Polynomial (SpectralField n) => P.coeff n) h
  rw [rationalFirstZeroPolynomial_vacant,Polynomial.coeff_map,Polynomial.coeff_C_mul,
    coefficient_X_add_source] at hc
  change firstFlatEvaluation n (((vacuumData (n+1)).P p.val.padBottom).coeff n) = _ at hc
  rw [polynomialNorthSource_eval_numerator]
  unfold polynomialNorthSource
  rw [map_mul]
  simp only [Nat.add_sub_cancel,SourcePairing.padBottom]
  rw [hc]
  rw [show firstFlatEvaluation n (constantL (n+1) (1/(2*(d:ℂ)))) =
    constF n (1/(2*(d:ℂ))) from torusEvaluation_constant _ _ _]
  ring

 

theorem polynomialNorthSource_firstThree (n : ℕ) :
    (fun p => firstThreeEvaluation n (polynomialNorthSource (n+1) p)) =
      (∏ j:Fin n,(spectralA j+constF n C)) •
        vacantBottomSourceExtension (fun p => evalLaurent (polynomialNorthSource n p)) := by
  funext p
  have h := congrFun (rationalNodalPolynomial_firstThree
    (polynomialVacuumVector n) (polynomialVacuumVector_eval n)
    (vacuumData (n+1)).P (vacuumData (n+1)).map_P) p.val
  have hc := congrArg (fun P : Polynomial (SpectralField n) => P.coeff n) h
  rw [Polynomial.coeff_map,Polynomial.coeff_C_mul] at hc
  change firstThreeEvaluation n (((vacuumData (n+1)).P p.val).coeff n) = _ at hc
  simp only [Pi.smul_apply,smul_eq_mul]
  by_cases hp : p ∈ Set.range SourcePairing.padBottom
  · obtain ⟨q,rfl⟩ := hp
    simp only [SourcePairing.padBottom] at hc
    rw [firstThreePolynomial_padBottom,coefficient_X_add_source] at hc
    rw [vacantBottomSourceExtension_padBottom,polynomialNorthSource_eval_numerator]
    unfold polynomialNorthSource
    rw [map_mul]
    simp only [Nat.add_sub_cancel,SourcePairing.padBottom]
    rw [hc,show firstThreeEvaluation n (constantL (n+1) (1/(2*(d:ℂ)))) =
      constF n (1/(2*(d:ℂ))) from torusEvaluation_constant _ _ _]
    ring
  · have ho : p.val.Occupied 0 := not_not.mp (fun h => hp ((SourcePairing.padBottom_range p).mpr h))
    simp only [firstThreePolynomial,vacantBottomExtension,ho,ite_true,mul_zero,
      Polynomial.coeff_zero] at hc
    simp only [vacantBottomSourceExtension,dite_eq_right hp,mul_zero]
    unfold polynomialNorthSource
    rw [map_mul]
    simp only [Nat.add_sub_cancel]
    rw [hc,mul_zero]

lemma firstFlatEvaluation_reflect {n : ℕ} (f : Laurent (n+1)) :
    firstFlatEvaluation n (reflectLaurent (n+1) f) =
      reflectSpectral n (firstThreeEvaluation n f) := by
  unfold firstFlatEvaluation firstThreeEvaluation
  rw [torusEvaluation_reflect,
    torusEvaluation_fieldMap (reflectSpectral n) (reflectSpectral_const n)]
  congr 2
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [firstFlatPoint,firstThreePoint,Fin.cons_zero,div_one,map_pow,reflectSpectral_const]
  · simp only [firstFlatPoint,firstThreePoint,Fin.cons_succ,reflectSpectral_variable]

lemma vacantBottomSourceExtension_map {K L : Type*} [Zero K] [Zero L] {n : ℕ}
    (f : K → L) (hf : f 0=0) (v : SourcePairing n → K) (p : SourcePairing (n+1)) :
    f (vacantBottomSourceExtension v p) = vacantBottomSourceExtension (f ∘ v) p := by
  unfold vacantBottomSourceExtension
  split_ifs <;> simp [hf]

lemma sourceGlue_vacantBottom_right {K : Type*} [CommRing K] {n : ℕ}
    (v : SourcePairing (n+1) → K) (w : SourcePairing n → K) :
    sourceGlue (n+1) v (vacantBottomSourceExtension w) =
      sourceGlue n (v ∘ SourcePairing.padBottom) w := by
  rw [sourceGlue_eq_sum,sourceGlue_eq_sum]
  have hinner (p : SourcePairing (n+1)) :
      (∑ q : SourcePairing (n+1), v p *
        ((if Pairing.GluesAt (Fin.last (n+1)) p.val q.val then (1:K) else 0) *
          vacantBottomSourceExtension w q)) =
        ∑ q : SourcePairing n, v p *
          ((if Pairing.GluesAt (Fin.last (n+1)) p.val q.padBottom.val then (1:K) else 0)*w q) := by
    symm
    apply Fintype.sum_of_injective SourcePairing.padBottom SourcePairing.padBottom_injective
    · intro q hq
      simp [vacantBottomSourceExtension,hq]
    · intro q
      rw [vacantBottomSourceExtension_padBottom]
  simp_rw [hinner]
  symm
  apply Fintype.sum_of_injective SourcePairing.padBottom SourcePairing.padBottom_injective
  · intro p hp
    apply Finset.sum_eq_zero
    intro q _
    have hh : ¬Pairing.GluesAt (Fin.last (n+1)) p.val q.padBottom.val := by
      intro h
      have ho : ¬p.val.Occupied 0 := fun ho =>
        q.val.padBottom_not_occupied_zero ((h.2.1 0).mp ho)
      exact hp ((SourcePairing.padBottom_range p).mpr ho)
    rw [ite_eq_right hh,zero_mul,mul_zero]
  · intro p
    apply Finset.sum_congr rfl
    intro q _
    have hh : Pairing.GluesAt (Fin.last (n+1)) p.padBottom.val q.padBottom.val ↔
        Pairing.GluesAt (Fin.last n) p.val q.val :=
      Pairing.gluesAt_map (Fin.succOrderEmb _) (Fin.last n) p.val q.val
    simp only [hh,Function.comp_apply]

lemma sourceGlue_vacantBottom_left {K : Type*} [CommRing K] {n : ℕ}
    (v : SourcePairing n → K) (w : SourcePairing (n+1) → K) :
    sourceGlue (n+1) (vacantBottomSourceExtension v) w =
      sourceGlue n v (w ∘ SourcePairing.padBottom) := by
  rw [sourceGlue_symmetric,sourceGlue_vacantBottom_right,sourceGlue_symmetric]

 

theorem polynomialNorthGluing_firstFlat (n : ℕ) :
    firstFlatEvaluation n (polynomialNorthGluing (n+1)) =
      (∏ j:Fin n,(spectralA j+constF n C))^2 * evalLaurent (polynomialNorthGluing n) := by
  unfold polynomialNorthGluing
  rw [sourceGlue_algMap (firstFlatEvaluation n)]
  have hv : (fun p : SourcePairing (n+1) => firstFlatEvaluation n
      (reflectLaurent (n+1) (polynomialNorthSource (n+1) p))) =
      (∏ j:Fin n,(spectralA j+constF n C)) •
        vacantBottomSourceExtension (fun p => evalLaurent (reflectLaurent n (polynomialNorthSource n p))) := by
    funext p
    rw [firstFlatEvaluation_reflect,congrFun (polynomialNorthSource_firstThree n) p]
    simp only [Pi.smul_apply,smul_eq_mul,map_mul,map_prod,map_add,reflectSpectral_const,
      reflectSpectral_spectralA,vacantBottomSourceExtension_map _ (map_zero _)]
    congr 2
    funext q
    exact reflectSpectral_evalLaurent _
  change ((firstFlatEvaluation n) ∘ (fun p => reflectLaurent (n+1) (polynomialNorthSource (n+1) p))) = _ at hv
  rw [hv,sourceGlue_smul_left,sourceGlue_vacantBottom_left]
  have hw : ((firstFlatEvaluation n) ∘ polynomialNorthSource (n+1)) ∘ SourcePairing.padBottom =
      (∏ j:Fin n,(spectralA j+constF n C)) •
        (fun p => evalLaurent (polynomialNorthSource n p)) := by
    funext p
    exact polynomialNorthSource_firstFlat n p
  rw [hw,sourceGlue_smul_right]
  unfold evalLaurent
  rw [sourceGlue_map]
  simp only [pow_two,mul_assoc]
  rfl


end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_BottomGauge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram




noncomputable section
open scoped Classical BigOperators LaurentPolynomial

lemma permLaurent_one {n : ℕ} (f : Laurent n) : permLaurent 1 f = f := by
  have h : permLaurent (1 : Equiv.Perm (Fin n)) = RingHom.id _ := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change permLaurent 1 (monomialL _ _) = monomialL _ _
    all_goals simp only [permLaurent_monomial,
      Equiv.Perm.one_def,Equiv.refl_symm,Equiv.coe_refl,Function.comp_id]
  exact DFunLike.congr_fun h f

lemma permLaurent_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (f : Laurent n) :
    permLaurent (σ*τ) f = permLaurent σ (permLaurent τ f) := by
  have h : permLaurent (σ*τ) = (permLaurent σ).comp (permLaurent τ) := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change permLaurent (σ*τ) (monomialL _ _) = permLaurent σ (permLaurent τ (monomialL _ _))
    all_goals simp only [permLaurent_monomial,
      Equiv.Perm.mul_def,Equiv.symm_trans,Equiv.coe_trans,Function.comp_assoc]
  exact DFunLike.congr_fun h f

 
lemma permLaurent_invariant_of_adjacent {n : ℕ} (f : Laurent n)
    (h : ∀ r (hr : r+2≤n), permLaurent (Equiv.swap (⟨r,by omega⟩:Fin n)
      ⟨r+1,by omega⟩) f = f) (σ : Equiv.Perm (Fin n)) : permLaurent σ f = f := by
  cases n with
  | zero =>
    have he : σ=1 := Subsingleton.elim _ _
    rw [he,permLaurent_one]
  | succ n =>
    let S : Submonoid (Equiv.Perm (Fin (n+1))) :=
      { carrier := {τ | permLaurent τ f=f}
        one_mem' := permLaurent_one f
        mul_mem' := by
          intro τ υ hτ hυ
          change permLaurent (τ*υ) f = f
          rw [permLaurent_mul,hυ,hτ] }
    have hm : Submonoid.closure (Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ)) ≤ S := by
      rw [Submonoid.closure_le]
      rintro _ ⟨i,rfl⟩
      exact h i.val (by have := i.isLt; omega)
    rw [Equiv.Perm.mclosure_swap_castSucc_succ] at hm
    exact hm (show σ ∈ (⊤ : Submonoid _) from trivial)

lemma polynomialNorthGluing_permute {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permLaurent σ (polynomialNorthGluing n) = polynomialNorthGluing n :=
  permLaurent_invariant_of_adjacent _ polynomialNorthGluing_exchange σ

 

lemma laurent_eq_zero_of_many_roots {K : Type*} [Field K]
    (f : LaurentPolynomial K) (m : ℕ)
    (hb : LaurentInterval f (-(m:ℤ)) m) (s : Finset K) (hc : 2*m < s.card)
    (hz : ∀ z∈s,z≠0)
    (he : ∀ z (h:z∈s), LaurentPolynomial.eval₂ (RingHom.id K) (Units.mk0 z (hz z h)) f=0) :
    f=0 := by
  let p := LaurentPolynomial.trunc (f*LaurentPolynomial.T m)
  have hp : p.degree < s.card := by
    apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
    intro k hk
    rw [laurent_trunc_coeff,laurent_shift_coeff]
    by_contra hn
    have := hb ((k:ℤ)-m) hn
    omega
  have hev (z : K) (hs:z∈s) : p.eval z=0 := by
    have h:=congrArg (LaurentPolynomial.eval₂ (RingHom.id K) (Units.mk0 z (hz z hs))) hb.shift_trunc
    rw [LaurentPolynomial.eval₂_toLaurent] at h
    change p.eval z = _ at h
    rw [(LaurentPolynomial.eval₂ (RingHom.id K) (Units.mk0 z (hz z hs))).map_mul,
      he z hs,zero_mul] at h
    exact h
  have hp0 : p=0 := Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero s hp hev
  have hh:=hb.shift_trunc
  change p.toLaurent=_ at hh
  rw [hp0,map_zero] at hh
  exact (LaurentPolynomial.isUnit_T (R:=K) (m:ℤ)).mul_left_eq_zero.mp hh.symm

lemma torusEvaluation_rowReflect {n m : ℕ} (i : Fin n)
    (z : Fin n → SpectralField m) (hz : ∀ j,z j≠0) (f : Laurent n) :
    torusEvaluation z hz (rowReflectLaurent i f) =
      torusEvaluation (Function.update z i (constF m phase^3/z i))
        (fun j => by by_cases h:j=i <;> simp [h,hz,constF_phase_ne_zero]) f := by
  have hmono (e : Fin n → ℤ) (c : ℂ) :
      torusEvaluation z hz (rowReflectLaurent i (monomialL e c)) =
        torusEvaluation (Function.update z i (constF m phase^3/z i))
          (fun j => by by_cases h:j=i <;> simp [h,hz,constF_phase_ne_zero]) (monomialL e c) := by
    rw [rowReflectLaurent_monomial,torusEvaluation_monomial,torusEvaluation_monomial]
    rw [←Finset.mul_prod_erase _ (fun j => z j ^ reflectExponentAt i e j) (Finset.mem_univ i),
      ←Finset.mul_prod_erase _ (fun j => (Function.update z i (constF m phase^3/z i)) j ^ e j) (Finset.mem_univ i)]
    have hh : (∏ j ∈ Finset.univ.erase i, z j ^ reflectExponentAt i e j) =
        ∏ j ∈ Finset.univ.erase i, (Function.update z i (constF m phase^3/z i)) j ^ e j := by
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j≠i := (Finset.mem_erase.mp hj).1
      simp only [reflectExponentAt,Function.update_of_ne hji]
    rw [hh]
    simp only [reflectExponentAt,Function.update_self,zpow_neg,
      constF,map_mul,map_zpow₀,zpow_mul,div_eq_mul_inv]
    simp only [mul_zpow,inv_zpow]
    ac_rfl
  have he : (torusEvaluation z hz).toRingHom.comp (rowReflectLaurent i) =
      (torusEvaluation (Function.update z i (constF m phase^3/z i))
        (fun j => by by_cases h:j=i <;> simp [h,hz,constF_phase_ne_zero])).toRingHom := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals exact hmono _ _
  exact DFunLike.congr_fun he f

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ArchRoots
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators LaurentPolynomial

lemma archRootShift_lt (k : ArchShiftIndex) : archRootShift k<16 := by
  rcases k with ⟨a,b,s⟩
  cases a <;> cases b <;> fin_cases s <;> decide

lemma archRootShift_injective : Function.Injective archRootShift := by
  decide

lemma archRootCoefficient_injective (b : Bool) : Function.Injective (archRootCoefficient b) := by
  intro k l h
  apply archRootShift_injective
  apply phase_primitive.pow_inj (archRootShift_lt k) (archRootShift_lt l)
  cases b with
  | false => exact h
  | true =>
    simp only [archRootCoefficient,ite_true] at h
    apply inv_injective
    exact mul_left_cancel₀ (pow_ne_zero 3 phase_ne_zero)
      (by simpa only [div_eq_mul_inv] using h)

lemma archRootExponent_support {n : ℕ} (j : Fin (n+1)) (b : Bool) (k : ArchShiftIndex) (i : Fin (n+2)) :
    archRootExponent (some (j,b,k)) i≠0 ↔ i=j.succ := by
  cases b <;> simp [archRootExponent,variableExponent,Pi.single_apply]

lemma archRoot_injective {n : ℕ} : Function.Injective (@archRoot n) := by
  intro x y h
  have he : monomialL (archRootExponent x) (archRootScalar x) =
      monomialL (archRootExponent y) (archRootScalar y) :=
    IsFractionRing.injective (SpectralRing (n+2)) (SpectralField (n+2)) h
  rcases AddMonoidAlgebra.single_inj.mp he with ⟨he,hc⟩|⟨hz,_⟩
  · cases x with
    | none =>
      cases y with
      | none => rfl
      | some y =>
        have hh := (archRootExponent_support y.1 y.2.1 y.2.2 y.1.succ).mpr rfl
        rw [←he] at hh
        exact (hh rfl).elim
    | some x =>
      cases y with
      | none =>
        have hh := (archRootExponent_support x.1 x.2.1 x.2.2 x.1.succ).mpr rfl
        rw [he] at hh
        exact (hh rfl).elim
      | some y =>
        rcases x with ⟨j,b,k⟩
        rcases y with ⟨l,a,r⟩
        have hi : j=l := by
          have hh := (archRootExponent_support j b k j.succ).mpr rfl
          rw [he] at hh
          exact Fin.succ_injective _ ((archRootExponent_support l a r j.succ).mp hh)
        subst l
        have hb : b=a := by
          have hh := congrFun he j.succ
          cases b <;> cases a <;> simp [archRootExponent,variableExponent] at hh ⊢
        subst a
        have hk := archRootCoefficient_injective b hc
        rw [hk]
  · exact (archRootScalar_ne_zero _ hz).elim

lemma archRoot_none (n : ℕ) : archRoot (none : ArchRootIndex n) = 1 := by
  simp [archRoot,archRootExponent,archRootScalar,monomialL,evalLaurent,← AddMonoidAlgebra.one_def]

lemma archRoot_some {n : ℕ} (j : Fin (n+1)) (b : Bool) (k : ArchShiftIndex) :
    archRoot (some (j,b,k)) =
      if b then constF (n+2) phase^3/(constF (n+2) phase^archRootShift k*variableF j.succ)
      else constF (n+2) phase^archRootShift k*variableF j.succ := by
  cases b <;> simp [archRoot,archRootExponent,archRootScalar,archRootCoefficient,
    evalLaurent_monomial_product,variableExponent,Pi.single_apply,constF,div_eq_mul_inv,
    Finset.prod_ite_eq']
  all_goals ac_rfl

 

lemma arch_pair_zero {n m : ℕ} (f : Laurent (n+2))
    (hp : ∀ σ,permLaurent σ f=f) (s : ℕ) (hs : pairEvaluation n s f=0)
    (j : Fin (n+1)) (z : Fin (n+2) → SpectralField m) (hz : ∀ i,z i≠0)
    (he : z j.succ=constF m phase^s*z 0) : torusEvaluation z hz f=0 := by
  let σ := Equiv.swap (1:Fin (n+2)) j.succ
  have hσ0 : σ 0=0 := Equiv.swap_apply_of_ne_of_ne (by intro h; have : (0:ℕ)=1 := congrArg Fin.val h; omega) (Fin.succ_ne_zero j).symm
  have hσ1 : σ 1=j.succ := Equiv.swap_apply_left _ _
  have hzero := pairEvaluation_zero_universal s f hs (z ∘ σ) (fun i=>hz _)
    (by simpa only [Function.comp_apply,hσ0,hσ1] using he)
  rw [←torusEvaluation_permLaurent,hp] at hzero
  exact hzero

lemma arch_pair_zero_reverse {n m : ℕ} (f : Laurent (n+2))
    (hp : ∀ σ,permLaurent σ f=f) (s : ℕ) (hs : pairEvaluation n s f=0)
    (j : Fin (n+1)) (z : Fin (n+2) → SpectralField m) (hz : ∀ i,z i≠0)
    (he : z 0=constF m phase^s*z j.succ) : torusEvaluation z hz f=0 := by
  let σ := Equiv.swap (0:Fin (n+2)) j.succ
  have hzero := arch_pair_zero f hp s hs j (z ∘ σ) (fun i=>hz _)
    (by simpa only [σ,Function.comp_apply,Equiv.swap_apply_left,Equiv.swap_apply_right] using he)
  rw [←torusEvaluation_permLaurent,hp] at hzero
  exact hzero







lemma archEvaluate_neg {n : ℕ} (f : Laurent (n+1)) (h : signLaurent 0 f = f)
    (x : SpectralField (n+1)) (hx : x≠0) :
    archEvaluate f (-x) (neg_ne_zero.mpr hx) = archEvaluate f x hx := by
  have he := torusEvaluation_signLaurent 0 (Function.update variableF 0 x)
    (fun j => by by_cases h:j=0 <;> simp [h,hx,variableF_ne_zero]) f
  rw [h] at he
  simpa only [Function.update_self,Function.update_idem,archEvaluate] using he.symm

lemma archEvaluate_reflect {n : ℕ} (f : Laurent (n+1)) (h : rowReflectLaurent 0 f = f)
    (x : SpectralField (n+1)) (hx : x≠0) :
    archEvaluate f (constF (n+1) phase^3/x)
      (div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero _)) hx) = archEvaluate f x hx := by
  have he := torusEvaluation_rowReflect 0 (Function.update variableF 0 x)
    (fun j => by by_cases h:j=0 <;> simp [h,hx,variableF_ne_zero]) f
  rw [h] at he
  simpa only [Function.update_self,Function.update_idem,archEvaluate] using he.symm

lemma archEvaluate_pair {n : ℕ} (f : Laurent (n+2))
    (hp : ∀ σ,permLaurent σ f=f) (s : ℕ) (hs : pairEvaluation n s f=0)
    (j : Fin (n+1)) (b : Bool) :
    archEvaluate f ((if b then (constF (n+2) phase^s)⁻¹ else constF (n+2) phase^s)*variableF j.succ)
      (by cases b <;> simp [constF_phase_ne_zero,variableF_ne_zero]) = 0 := by
  unfold archEvaluate
  cases b with
  | false =>
    apply arch_pair_zero_reverse f hp s hs j
    simp only [Function.update_self,Function.update_of_ne (Fin.succ_ne_zero j),Bool.false_eq_true,ite_false]
  | true =>
    apply arch_pair_zero f hp s hs j
    simp only [Function.update_self,Function.update_of_ne (Fin.succ_ne_zero j),ite_true]
    field_simp [constF_phase_ne_zero]

lemma archShift_value (k : ArchShiftIndex) :
    phase^archRootShift k =
      (if k.2.1 then -1 else 1) *
        (if k.1 then (phase^(k.2.2.val+2))⁻¹ else phase^(k.2.2.val+2)) := by
  rcases k with ⟨a,b,s⟩
  have hp := phase_more_powers
  cases a <;> cases b <;> fin_cases s <;>
    simp [archRootShift,hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2.1,hp.2.2.2.2.2]

lemma archEvaluate_shift {n : ℕ} (f : Laurent (n+2))
    (hp : ∀ σ,permLaurent σ f=f) (hsg : signLaurent 0 f=f)
    (h2 : pairEvaluation n 2 f=0) (h3 : pairEvaluation n 3 f=0)
    (j : Fin (n+1)) (k : ArchShiftIndex) :
    archEvaluate f (constF (n+2) phase^archRootShift k*variableF j.succ)
      (mul_ne_zero (pow_ne_zero _ (constF_phase_ne_zero _)) (variableF_ne_zero _)) = 0 := by
  have hbase := archEvaluate_pair f hp (k.2.2.val+2)
    (by rcases k with ⟨a,b,s⟩; fin_cases s <;> assumption) j k.1
  have hm : constF (n+2) phase^archRootShift k*variableF j.succ =
      if k.2.1 then -((if k.1 then (constF (n+2) phase^(k.2.2.val+2))⁻¹
        else constF (n+2) phase^(k.2.2.val+2))*variableF j.succ)
      else ((if k.1 then (constF (n+2) phase^(k.2.2.val+2))⁻¹
        else constF (n+2) phase^(k.2.2.val+2))*variableF j.succ) := by
    have hc := congrArg (algebraMap ℂ (SpectralField (n+2))) (archShift_value k)
    rcases k with ⟨a,b,s⟩
    cases a <;> cases b <;>
      simp only [Bool.false_eq_true,ite_false,ite_true,map_pow,map_mul,map_neg,map_one,map_inv₀] at hc ⊢
    all_goals dsimp only [constF]; rw [hc]; simp
  cases hb : k.2.1
  · simpa only [hm,hb,Bool.false_eq_true,ite_false] using hbase
  · have hh := (archEvaluate_neg f hsg _ _).trans hbase
    simpa only [hm,hb,ite_true] using hh

 

lemma archEvaluate_roots {n : ℕ} (f : Laurent (n+2))
    (hp : ∀ σ,permLaurent σ f=f) (hsg : signLaurent 0 f=f)
    (hr : rowReflectLaurent 0 f=f) (hflat : firstFlatEvaluation (n+1) f=0)
    (h2 : pairEvaluation n 2 f=0) (h3 : pairEvaluation n 3 f=0)
    (k : ArchRootIndex n) : archEvaluate f (archRoot k) (archRoot_ne_zero k)=0 := by
  cases k with
  | none =>
    unfold archEvaluate
    apply firstFlatEvaluation_zero_universal f hflat
    simp only [Function.update_self,archRoot_none]
  | some k =>
    rcases k with ⟨j,b,k⟩
    cases b with
    | false =>
      simpa only [archRoot_some,Bool.false_eq_true,ite_false] using archEvaluate_shift f hp hsg h2 h3 j k
    | true =>
      have hh := (archEvaluate_reflect f hr _ _).trans (archEvaluate_shift f hp hsg h2 h3 j k)
      simpa only [archRoot_some,ite_true] using hh

 

theorem archLaurent_interpolation_zero {n : ℕ} (f : Laurent (n+2))
    (hb : LaurentBox f (fun _ =>4*(n+2)))
    (hp : ∀ σ,permLaurent σ f=f) (hsg : signLaurent 0 f=f)
    (hr : rowReflectLaurent 0 f=f) (hflat : firstFlatEvaluation (n+1) f=0)
    (h2 : pairEvaluation n 2 f=0) (h3 : pairEvaluation n 3 f=0) : f=0 := by
  apply fullPeel_injective (0:Fin (n+2))
  rw [map_zero]
  refine laurent_eq_zero_of_many_roots (fullPeel (0:Fin (n+2)) f) (4*(n+2))
    (hb.fullPeel 0) (Finset.univ.image (@archRoot n)) ?_
    (fun z hz => by obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hz; exact archRoot_ne_zero k) ?_
  · rw [Finset.card_image_of_injective _ archRoot_injective,Finset.card_univ]
    simp only [ArchRootIndex,ArchShiftIndex,Fintype.card_option,Fintype.card_prod,
      Fintype.card_fin,Fintype.card_bool]
    omega
  · intro z hz
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hz
    rw [fullPeel_eval]
    exact archEvaluate_roots f hp hsg hr hflat h2 h3 k

end
 

 

noncomputable section
open scoped Classical BigOperators



lemma previousCoeff_map {K L : Type*} [Semiring K] [Semiring L]
    (g : K →+* L) (n : ℕ) (P : Polynomial K) :
    previousCoeff n (P.map g) = g (previousCoeff n P) := by
  by_cases h:n=0 <;> simp [previousCoeff,h]


lemma map_scalarValue {K L : Type*} [CommRing K] [CommRing L]
    (g : K →+* L) (f : ℂ →+* K) {n : ℕ} (a : Fin n → K) :
    g (scalarValue f a) = scalarValue (g.comp f) (g ∘ a) := by
  exact MvPolynomial.map_eval₂Hom _ _ _ _

lemma nextScalar_map {K L : Type*} [CommRing K] [CommRing L]
    (g : K →+* L) (f : ℂ →+* K) {n : ℕ} (a : Fin n → K) :
    (nextScalar f a).map g = nextScalar (g.comp f) (g ∘ a) :=
  map_firstScalarHom g f a _

lemma nextScalar_top {K : Type*} [CommRing K]
    (f : ℂ →+* K) {n : ℕ} (a : Fin n → K) :
    (nextScalar f a).coeff n = scalarValue f a :=
  scalarPolynomial_first_top_continuation f n _ _ _ _

lemma nextScalar_degree {K : Type*} [CommRing K]
    (f : ℂ →+* K) {n : ℕ} (a : Fin n → K) : (nextScalar f a).natDegree ≤ n :=
  scalarPolynomial_first_degree f n _ _ _ _


lemma nextScalar_permute {K : Type*} [CommRing K]
    (f : ℂ →+* K) {n : ℕ} (a : Fin n → K) (σ : Equiv.Perm (Fin n)) :
    nextScalar f (a ∘ σ) = nextScalar f a := by
  have h := scalarValue_permute (Polynomial.C.comp f)
    (Fin.cons Polynomial.X (fun i => Polynomial.C (a i))) (headPerm σ)
  have hv : (Fin.cons Polynomial.X (fun i => Polynomial.C (a i))) ∘ headPerm σ =
      Fin.cons Polynomial.X (fun i => Polynomial.C (a (σ i))) := by
    funext i
    induction i using Fin.cases <;> rfl
  rw [hv] at h
  exact h



lemma map_scalarArchNumerator {K L : Type*} [CommRing K] [CommRing L]
    (g : K →+* L) (f : ℂ →+* K) {n : ℕ} (a : Fin n → K) :
    g (scalarArchNumerator f a) = scalarArchNumerator (g.comp f) (g ∘ a) := by
  simp only [scalarArchNumerator,map_sub,map_mul,map_sum,map_pow,map_scalarValue,
    ←previousCoeff_map,nextScalar_map,RingHom.comp_apply,Function.comp_apply]

lemma scalarArchNumerator_permute {K : Type*} [CommRing K]
    (f : ℂ →+* K) {n : ℕ} (a : Fin n → K) (σ : Equiv.Perm (Fin n)) :
    scalarArchNumerator f (a ∘ σ) = scalarArchNumerator f a := by
  rw [scalarArchNumerator,scalarValue_permute,nextScalar_permute]
  have h : (∑i,a (σ i))=∑i,a i := Equiv.sum_comp σ a
  exact congrArg (fun z => z*scalarValue f a^2-f (2*(d:ℂ)-1)*scalarValue f a*previousCoeff n (nextScalar f a)) h

lemma rowCosineL_map {n : ℕ} (i : Fin n) : evalLaurent (rowCosineL i)=spectralA i := by
  rw [rowCosineL,cosineL_map _ _ (inv_ne_zero (pow_ne_zero _ phase_ne_zero)),map_monomialL_two_variable]
  simp only [constF,map_inv₀,map_pow]
  congr 1
  simp [constF,div_eq_mul_inv,mul_comm]

lemma rowCosineL_algebraMap {n : ℕ} (i : Fin n) :
    algebraMap (SpectralRing n) (SpectralField n) (rowCosineL i)=spectralA i := rowCosineL_map i

lemma rowCosineL_box {n : ℕ} (i : Fin n) : LaurentBox (rowCosineL i) (fun _=>2) := by
  apply LaurentBox.cosine
  intro j
  by_cases h:j=i <;> simp [variableExponent,h]

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

lemma nextScalar_rowCosine (n : ℕ) :
    nextScalar (constantL n) rowCosineL = (vacuumData n).P (empty (n+1)) := by
  apply Polynomial.map_injective (algebraMap (SpectralRing n) (SpectralField n))
    (IsFractionRing.injective _ _)
  rw [nextScalar_map,(vacuumData n).map_P,rationalNodalPolynomial_empty]
  simp only [evalLaurent_constant_comp,Function.comp_def,rowCosineL_algebraMap,nextScalar]


lemma archCandidate_eval (n : ℕ) :
    evalLaurent (archCandidate n)=scalarArchNumerator (algebraMap ℂ (SpectralField n)) spectralA := by
  unfold archCandidate evalLaurent
  rw [map_scalarArchNumerator]
  simp only [evalLaurent_constant_comp,Function.comp_def,rowCosineL_algebraMap]

lemma scalarValue_rowCosine_box (n : ℕ) :
    LaurentBox (scalarValue (constantL n) rowCosineL) (fun _=>2*(n-1)) := by
  rw [scalarValue_rowCosine]
  cases n with
  | zero => intro e he i; exact Fin.elim0 i
  | succ n => exact (vacuumData n).box _

lemma previousCoeff_nextScalar_box (n : ℕ) :
    LaurentBox (previousCoeff n (nextScalar (constantL n) rowCosineL)) (fun _=>2*n) := by
  rw [nextScalar_rowCosine,previousCoeff]
  split_ifs
  · exact LaurentBox.zero _
  · exact (vacuumData n).box_P _ _

lemma archCandidate_box (n : ℕ) : LaurentBox (archCandidate n) (fun _=>4*n) := by
  unfold archCandidate scalarArchNumerator
  apply LaurentBox.sub
  · have h := (LaurentBox.sum Finset.univ rowCosineL (fun _=>2) (fun i _=>rowCosineL_box i)).mul
      ((scalarValue_rowCosine_box n).pow 2)
    apply h.mono
    intro i
    have := i.isLt
    simp only [Pi.add_apply]
    omega
  · have h := ((LaurentBox.constant (2*(d:ℂ)-1)).mul (scalarValue_rowCosine_box n)).mul (previousCoeff_nextScalar_box n)
    apply h.mono
    intro i
    simp only [Pi.add_apply,Pi.zero_apply]
    omega

lemma archCandidate_permute {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permLaurent σ (archCandidate n) = archCandidate n := by
  apply IsFractionRing.injective (SpectralRing n) (SpectralField n)
  change evalLaurent (permLaurent σ (archCandidate n))=evalLaurent (archCandidate n)
  rw [←permSpectral_evalLaurent,archCandidate_eval]
  rw [map_scalarArchNumerator]
  have hc : (permSpectral σ).comp (algebraMap ℂ (SpectralField n)) =
      algebraMap ℂ (SpectralField n) := by ext z; exact permSpectral_const σ z
  simp only [hc,Function.comp_def,permSpectral_spectralA]
  exact scalarArchNumerator_permute (algebraMap ℂ (SpectralField n)) spectralA σ

lemma archCandidate_parity {n : ℕ} (i : Fin n) : signLaurent i (archCandidate n)=archCandidate n := by
  apply IsFractionRing.injective (SpectralRing n) (SpectralField n)
  change evalLaurent (signLaurent i (archCandidate n))=evalLaurent (archCandidate n)
  rw [←signSpectral_evalLaurent,archCandidate_eval,map_scalarArchNumerator]
  have hc : (signSpectral i).comp (algebraMap ℂ (SpectralField n)) =
      algebraMap ℂ (SpectralField n) := by ext z; exact signSpectral_const i z
  simp only [hc,Function.comp_def,signSpectral_spectralA]

lemma archCandidate_row_reflection {n : ℕ} (i : Fin n) :
    rowReflectLaurent i (archCandidate n)=archCandidate n := by
  apply IsFractionRing.injective (SpectralRing n) (SpectralField n)
  change evalLaurent (rowReflectLaurent i (archCandidate n))=evalLaurent (archCandidate n)
  rw [←rowReflectSpectral_evalLaurent,archCandidate_eval,map_scalarArchNumerator]
  have hc : (rowReflectSpectral i).comp (algebraMap ℂ (SpectralField n)) =
      algebraMap ℂ (SpectralField n) := by ext z; exact rowReflectSpectral_const i z
  simp only [hc,Function.comp_def,rowReflectSpectral_spectralA]

 

 


lemma previousCoeff_C_mul {K : Type*} [CommRing K] (n : ℕ) (a : K) (P : Polynomial K) :
    previousCoeff n (Polynomial.C a * P) = a * previousCoeff n P := by
  by_cases h : n=0 <;> simp [previousCoeff,h,Polynomial.coeff_C_mul]

lemma previousCoeff_linear {K : Type*} [CommRing K] (n : ℕ) (a : K) (P : Polynomial K) :
    previousCoeff (n+1) ((Polynomial.X+Polynomial.C a)*P) =
      previousCoeff n P + a*P.coeff n := by
  cases n with
  | zero => simp [previousCoeff,add_mul]
  | succ n => simp [previousCoeff,add_mul,Polynomial.coeff_X_mul,Polynomial.coeff_C_mul]

lemma previousCoeff_quadratic {K : Type*} [CommRing K]
    (n : ℕ) (a b : K) (P : Polynomial K) (hP : P.natDegree ≤ n) :
    previousCoeff (n+2) (((Polynomial.X-Polynomial.C a)*(Polynomial.X-Polynomial.C b))*P) =
      previousCoeff n P - (a+b)*P.coeff n := by
  have hz : P.coeff (n+1)=0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have he : ((Polynomial.X-Polynomial.C a)*(Polynomial.X-Polynomial.C b))*P =
      (Polynomial.X+Polynomial.C (-a))*((Polynomial.X+Polynomial.C (-b))*P) := by simp; ring
  rw [he,show n+2=(n+1)+1 by omega,previousCoeff_linear,previousCoeff_linear]
  simp only [add_mul,Polynomial.coeff_add,Polynomial.coeff_X_mul,Polynomial.coeff_C_mul,hz,mul_zero,add_zero]
  ring

lemma specialization_constant_comp {n m : ℕ} (φ : Laurent n →ₐ[ℂ] SpectralField m) :
    φ.toRingHom.comp (constantL n) = algebraMap ℂ (SpectralField m) := by
  ext z
  exact φ.commutes z

lemma torusEvaluation_rowCosine {n m : ℕ} (z : Fin n → SpectralField m) (hz : ∀i,z i≠0) (i : Fin n) :
    torusEvaluation z hz (rowCosineL i) = torusCos ((z i)^2/constF m phase^3) := by
  have ha := RationalAt.algebraMap (φ := (torusEvaluation z hz).toRingHom)
    (F := SpectralField n) (rowCosineL i)
  rw [rowCosineL_algebraMap] at ha
  exact ha.unique (rationalAt_torusCos _ (((rationalAt_variable z hz i).pow 2).div
    ((rationalAt_const (torusEvaluation z hz) phase).pow 3) (pow_ne_zero _ (constF_phase_ne_zero _)))
    (div_ne_zero (pow_ne_zero _ (hz i)) (pow_ne_zero _ (constF_phase_ne_zero _))))

lemma firstFlatEvaluation_rowCosine {n : ℕ} (i : Fin (n+1)) :
    firstFlatEvaluation n (rowCosineL i) = (Fin.cons (constF n c) spectralA : Fin (n+1) → SpectralField n) i := by
  have ha := RationalAt.algebraMap (φ := (firstFlatEvaluation n).toRingHom)
    (F := SpectralField (n+1)) (rowCosineL i)
  rw [rowCosineL_algebraMap] at ha
  exact ha.unique (rationalAt_firstFlat_spectralA i)

lemma nextScalar_firstFlat (n : ℕ) :
    (nextScalar (constantL (n+1)) rowCosineL).map (firstFlatEvaluation n).toRingHom =
      Polynomial.C (∏ j:Fin n, (spectralA j+constF n C)) *
        ((Polynomial.X+Polynomial.C (constF n C))*nextScalar (algebraMap ℂ (SpectralField n)) spectralA) := by
  rw [nextScalar_rowCosine]
  have h := congrFun (rationalNodalPolynomial_firstFlat
    (vacuumData n).interpolant (vacuumData (n+1)).P (vacuumData (n+1)).map_P)
    (empty (n+1)).padBottom
  rw [rationalFirstZeroPolynomial_vacant,Pairing.padBottom_empty,rationalNodalPolynomial_empty] at h
  exact h

lemma matrixPolynomial_merge_empty {n m : ℕ} (r : ℕ) (hr : r+2≤n+1)
    (P : Pairing n → Polynomial (SpectralField m)) :
    matrixPolynomial (mergeMap r hr) P (empty (n+1))=P (empty n) := by
  ext k
  rw [matrixPolynomial_coeff,mergeMap_mulVec_empty]

lemma matrixPolynomial_delete_empty {n m : ℕ} (r : ℕ) (hr : r+2≤n+2)
    (P : Pairing n → Polynomial (SpectralField m)) :
    matrixPolynomial (deletionMap r hr) P (empty (n+2))=P (empty n) := by
  ext k
  rw [matrixPolynomial_coeff,deletionMap_mulVec_empty]

lemma nextScalar_pair_merge (n : ℕ) :
    (nextScalar (constantL (n+2)) rowCosineL).map (pairEvaluation n 2).toRingHom =
      Polynomial.C (mergePairScalar n) * ((Polynomial.X+Polynomial.C (fcos 0 (-1))) *
        (nextScalar (constantL (n+1)) rowCosineL).map (mergeEvaluation n).toRingHom) := by
  rw [nextScalar_rowCosine,nextScalar_rowCosine]
  have h := congrFun (rationalNodalPolynomial_pair_merge
    (polynomialVacuumVector (n+1)) (polynomialVacuumVector_eval (n+1))
    (vacuumData (n+1)).P (vacuumData (n+1)).map_P (vacuumData (n+1)).eval_P
    (vacuumData (n+2)).P (vacuumData (n+2)).map_P) (empty (n+3))
  rw [matrixPolynomial_merge_empty] at h
  simpa only [mergePairPolynomial,mul_assoc] using h

lemma nextScalar_pair_delete (n : ℕ) :
    (nextScalar (constantL (n+2)) rowCosineL).map (pairEvaluation n 3).toRingHom =
      Polynomial.C (deletePairScalar n) * (((Polynomial.X-Polynomial.C (fcos 0 (-9)))*(Polynomial.X-Polynomial.C (fcos 0 9))) *
        (nextScalar (constantL n) rowCosineL).map (deleteEvaluation n).toRingHom) := by
  rw [nextScalar_rowCosine,nextScalar_rowCosine]
  have h := congrFun (rationalNodalPolynomial_pair_delete
    (polynomialVacuumVector (n+1)) (polynomialVacuumVector_eval (n+1))
    (vacuumData n).P (vacuumData n).map_P (vacuumData n).eval_P
    (vacuumData (n+2)).P (vacuumData (n+2)).map_P) (empty (n+3))
  rw [matrixPolynomial_delete_empty] at h
  simpa only [deletePairPolynomial,mul_assoc] using h

lemma nextScalar_specialize {n m : ℕ} (φ : Laurent n →ₐ[ℂ] SpectralField m) :
    (nextScalar (constantL n) rowCosineL).map φ.toRingHom =
      nextScalar (algebraMap ℂ (SpectralField m)) (fun i =>φ (rowCosineL i)) := by
  rw [nextScalar_map,specialization_constant_comp]
  rfl

lemma archCandidate_specialize {n m : ℕ} (φ : Laurent n →ₐ[ℂ] SpectralField m) :
    φ (archCandidate n)=
      scalarArchNumerator (algebraMap ℂ (SpectralField m)) (fun i =>φ (rowCosineL i)) := by
  unfold archCandidate
  rw [show φ (scalarArchNumerator (constantL n) rowCosineL)=φ.toRingHom _ from rfl,
    map_scalarArchNumerator,specialization_constant_comp]
  rfl

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ArchTrig
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

lemma arch_flat_constants : (c:ℂ) = (2*(d:ℂ)-1)*(C:ℂ) := by
  have hh : c=(2*d-1)*C := by
    rw [←c_add_rho_eq_C,rho_eq_two_c_d]
    linear_combination -(4*c)*d_sq
  exact_mod_cast hh

lemma fcos_arch_merge {n : ℕ} (i : Fin n) (k : ℤ) :
    fcos i (k-2)+fcos i (k+2)-fcos i k=constF n (2*(d:ℂ)-1)*fcos i k := by
  have h := (fcos_sum_product i k).1
  simp only [constF,map_sub,map_mul,map_ofNat,map_one] at *
  linear_combination h

lemma fcos_arch_delete {n : ℕ} (i : Fin n) :
    fcos i (-3)+fcos i 3 = -constF n (2*(d:ℂ)-1)*(fcos i (-9)+fcos i 9) := by
  have ha := (fcos_sum_product i (-1)).1
  have hb := (fcos_sum_product i 1).1
  have hc := fcos_sub_eight i (-1)
  have hd := fcos_eight i 1
  norm_num only at ha hb hc hd
  rw [hc,hd]
  simp only [constF,map_sub,map_mul,map_ofNat,map_one] at *
  linear_combination ha+hb

 

 


lemma pairEvaluation_rowCosine {n : ℕ} (s : ℕ) (i : Fin (n+2)) :
    pairEvaluation n s (rowCosineL i)=pairCosines n s i := by
  rw [pairEvaluation,torusEvaluation_rowCosine,pairPoint_cosine]

lemma mergeEvaluation_rowCosine {n : ℕ} (i : Fin (n+1)) :
    mergeEvaluation n (rowCosineL i)=
      (Fin.cons (fcos 0 (-1)) (fun j:Fin n => fcos j.succ (-3)) : Fin (n+1) → SpectralField (n+1)) i := by
  rw [mergeEvaluation,torusEvaluation_rowCosine]
  exact congrFun (mergePoint_cosines n) i

lemma deleteEvaluation_rowCosine {n : ℕ} (i : Fin n) :
    deleteEvaluation n (rowCosineL i)=fcos i.succ (-3) := by
  unfold deleteEvaluation
  exact (torusEvaluation_rowCosine (deletePoint n)
    (fun j => show deletePoint n j ≠ 0 from variableF_ne_zero j.succ) i).trans
      (congrFun (deletePoint_cosines n) i)

lemma nextScalar_flat_previous (n : ℕ) :
    previousCoeff (n+1) (nextScalar (algebraMap ℂ (SpectralField n)) (Fin.cons (constF n c) spectralA)) =
      (∏j:Fin n,(spectralA j+constF n C)) *
        (previousCoeff n (nextScalar (algebraMap ℂ (SpectralField n)) spectralA) +
          constF n C * scalarValue (algebraMap ℂ (SpectralField n)) spectralA) := by
  have hp := congrArg (previousCoeff (n+1)) (nextScalar_firstFlat n)
  rw [nextScalar_specialize] at hp
  simp only [firstFlatEvaluation_rowCosine,previousCoeff_C_mul,previousCoeff_linear,nextScalar_top] at hp
  exact hp

 

theorem archCandidate_firstFlat (n : ℕ) :
    firstFlatEvaluation n (archCandidate (n+1))=
      (∏j:Fin n,(spectralA j+constF n C))^2 * evalLaurent (archCandidate n) := by
  rw [archCandidate_specialize,archCandidate_eval]
  simp only [firstFlatEvaluation_rowCosine]
  unfold scalarArchNumerator
  have hs := scalarValue_flat (algebraMap ℂ (SpectralField n)) (@spectralA n)
  rw [show (algebraMap ℂ (SpectralField n)) (c:ℂ)=constF n c from rfl] at hs
  rw [hs,nextScalar_flat_previous]
  simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
  have hc : constF n c=constF n (2*(d:ℂ)-1)*constF n C := by
    simpa only [constF,map_mul] using congrArg (constF n) arch_flat_constants
  change _ = (∏j:Fin n,(spectralA j+constF n C))^2 * _
  change constF n c = _ at hc
  change ((constF n c + ∑i:Fin n,spectralA i) * _ - _) = _
  simp only [constF] at hc ⊢
  rw [hc]
  ring

lemma nextScalar_merge_previous (n : ℕ) :
    previousCoeff (n+2) (nextScalar (algebraMap ℂ (SpectralField (n+1))) (pairCosines n 2)) =
      mergePairScalar n *
        (previousCoeff (n+1) (nextScalar (algebraMap ℂ (SpectralField (n+1)))
          (Fin.cons (fcos 0 (-1)) (fun j:Fin n =>fcos j.succ (-3)))) +
          fcos 0 (-1) * scalarValue (algebraMap ℂ (SpectralField (n+1)))
            (Fin.cons (fcos 0 (-1)) (fun j:Fin n =>fcos j.succ (-3)))) := by
  have hp := congrArg (previousCoeff (n+2)) (nextScalar_pair_merge n)
  rw [nextScalar_specialize,nextScalar_specialize] at hp
  simp only [pairEvaluation_rowCosine,mergeEvaluation_rowCosine,previousCoeff_C_mul] at hp
  rw [previousCoeff_linear (n+1),nextScalar_top] at hp
  exact hp

 
theorem archCandidate_merge (n : ℕ) :
    pairEvaluation n 2 (archCandidate (n+2))=
      mergePairScalar n^2 * mergeEvaluation n (archCandidate (n+1)) := by
  rw [archCandidate_specialize,archCandidate_specialize]
  simp only [pairEvaluation_rowCosine,mergeEvaluation_rowCosine]
  unfold scalarArchNumerator
  rw [scalar_pair_merge,nextScalar_merge_previous]
  have hc := fcos_arch_merge (0:Fin (n+1)) (-1)
  norm_num only at hc
  have hs : (∑i:Fin (n+2),pairCosines n 2 i)=
      (∑i:Fin (n+1),(Fin.cons (fcos 0 (-1)) (fun j:Fin n =>fcos j.succ (-3)) : Fin (n+1) → SpectralField (n+1)) i) +
        constF (n+1) (2*(d:ℂ)-1)*fcos 0 (-1) := by
    simp only [pairCosines,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
    norm_num only
    linear_combination hc
  rw [hs]
  dsimp only [constF]
  ring

lemma nextScalar_delete_previous (n : ℕ) :
    previousCoeff (n+2) (nextScalar (algebraMap ℂ (SpectralField (n+1))) (pairCosines n 3)) =
      deletePairScalar n *
        (previousCoeff n (nextScalar (algebraMap ℂ (SpectralField (n+1))) (fun j:Fin n =>fcos j.succ (-3))) -
          (fcos 0 (-9)+fcos 0 9) * scalarValue (algebraMap ℂ (SpectralField (n+1))) (fun j:Fin n =>fcos j.succ (-3))) := by
  have hp := congrArg (previousCoeff (n+2)) (nextScalar_pair_delete n)
  rw [nextScalar_specialize,nextScalar_specialize] at hp
  simp only [pairEvaluation_rowCosine,deleteEvaluation_rowCosine,previousCoeff_C_mul] at hp
  rw [previousCoeff_quadratic _ _ _ _ (nextScalar_degree _ _),nextScalar_top] at hp
  exact hp

 
theorem archCandidate_delete (n : ℕ) :
    pairEvaluation n 3 (archCandidate (n+2))=
      deletePairScalar n^2 * deleteEvaluation n (archCandidate n) := by
  rw [archCandidate_specialize,archCandidate_specialize]
  simp only [pairEvaluation_rowCosine,deleteEvaluation_rowCosine]
  unfold scalarArchNumerator
  rw [scalar_pair_delete,nextScalar_delete_previous]
  have hc := fcos_arch_delete (0:Fin (n+1))
  have hs : (∑i:Fin (n+2),pairCosines n 3 i)=
      (∑j:Fin n,fcos j.succ (-3)) - constF (n+1) (2*(d:ℂ)-1)*(fcos 0 (-9)+fcos 0 9) := by
    simp only [pairCosines,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
    norm_num only
    linear_combination hc
  rw [hs]
  dsimp only [constF]
  ring






lemma SourcePairing.one_eq (p : SourcePairing 1) : p=oneSourcePair := by
  apply Subtype.ext
  apply Subtype.ext
  apply Finset.ext
  rintro ⟨i,j⟩
  have hu := p.val.property.1
  have hp := p.property
  change ∃ k, p.val.Adj (1:Fin 2) k at hp
  obtain ⟨k,hk⟩ := hp
  have hk0 : k=0 := by
    fin_cases k
    · rfl
    · exact False.elim (p.val.adj_irrefl 1 hk)
  subst k
  have hmem : (0,1) ∈ p.val.val := by
    rcases hk with hk|hk
    · have hh := hu _ hk; simp at hh
    · exact hk
  fin_cases i <;> fin_cases j <;> simp only [oneSourcePair,twoPair,Finset.mem_singleton,Prod.mk.injEq]
  all_goals aesop (add safe (by have : ¬((1:Fin 2)<0) := by decide; exact this))

instance instSubsingletonSourcePairingOfNatNat : Subsingleton (SourcePairing 1) :=
  ⟨fun p q => p.one_eq.trans q.one_eq.symm⟩

lemma oneSourcePair_glues : Pairing.GluesAt (Fin.last 1) twoPair twoPair := by
  refine ⟨twoPair_occupied _,fun _ =>Iff.rfl,?_⟩
  intro i j hij
  fin_cases i
  · exact .single (Or.inl (by simp))
  · exact .refl

lemma sourceGlue_one {K : Type*} [CommRing K] (v w : SourcePairing 1 → K) :
    sourceGlue 1 v w=v oneSourcePair*w oneSourcePair := by
  rw [sourceGlue_eq_sum]
  simp only [Fintype.sum_subsingleton _ oneSourcePair,oneSourcePair,oneSourcePair_glues,ite_true,one_mul]

lemma sourceGlue_zero {K : Type*} [CommRing K] (v w : SourcePairing 0 → K) :
    sourceGlue 0 v w=0 := by
  have : IsEmpty (SourcePairing 0) := ⟨fun p =>p.ne_empty (p.val.eq_empty_of_le_one (by omega))⟩
  simp [sourceGlue, dotProduct]

lemma archCandidate_zero : archCandidate 0=0 := by
  simp [archCandidate,scalarArchNumerator,previousCoeff]

lemma polynomialNorthGluing_zero : polynomialNorthGluing 0=0 := sourceGlue_zero _ _

lemma empty_insertCup_two :
    (empty 2).insertCup 0 1 (by decide) (empty_not_occupied _) (empty_not_occupied _)=twoPair := by
  apply Subtype.ext
  simp [Pairing.insertCup,twoPair,empty]

lemma localR_deletion_twoPair {K : Type*} [Field K] :
    localR (PartialColumn.rowPosition 0 (show 2≤2 by omega)) (deletionWeights : Weights K) twoPair (empty 2)=1 := by
  simp only [localR,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  rw [Finset.sum_eq_single Tile.cup]
  · simp [Weights.tile,deletionWeights,optionMatrix,Pairing.tileStep,PartialColumn.rowPosition,empty_insertCup_two]
  · intro t _ ht
    cases t <;> simp_all [Weights.tile,deletionWeights,optionMatrix,Pairing.tileStep,
      PartialColumn.rowPosition]
    all_goals intro h; exact empty_not_occupied 0 (h ▸ twoPair_occupied 0)
  · simp

lemma deletionMap_zero_twoPair :
    (deletionMap (n:=0) (m:=1) 0 (by omega)).mulVec (fun _=>1) twoPair=1 := by
  let : Subsingleton (Pairing 0) := ⟨fun p q =>(p.eq_empty_of_le_one (by omega)).trans (q.eq_empty_of_le_one (by omega)).symm⟩
  rw [deletionMap]
  dsimp +instances only [CStarMatrix, CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid,
    CStarMatrix.ofMatrix, Equiv.refl, Equiv.symm]
  simp only [Equiv.coe_fn_mk, id_eq]
  simp only [Matrix.mulVec, dotProduct,Fintype.sum_subsingleton _ (empty 0),mul_one]
  rw [functionMatrix_mul,mul_functionMatrix]
  simpa only [Function.comp_apply,Pairing.map_empty] using (localR_deletion_twoPair (K:=SpectralField 1))

lemma reducedNodalDatum_one (p : SourcePairing 1) :
    reducedNodalDatum 0 p.val=4*constF 1 c*torusSin (constF 1 phase^3/variableF 0) := by
  rw [p.one_eq]
  simp only [reducedNodalDatum,reducedNodalHead,oneSourcePair,twoPair_occupied,
    matrixPrefix,Nat.lt_succ_self,reducedMovingStep,↓reduceDIte,↓reduceIte,Matrix.mul_one]
  simp only [Fin.mk_zero,↓reduceIte,Matrix.one_mulVec]
  have hv : (fun q:Pairing 0 =>insertSpectral (0:Fin 1) (rationalVacuum 0 q))=fun _=>1 := by
    funext q
    rw [rationalVacuum_zero,map_one]
  rw [hv]
  change 4*constF 1 c*torusSin (constF 1 phase^3/variableF 0) *
    (deletionMap (n:=0) (m:=1) 0 (by omega)).mulVec (fun _=>1) twoPair = _
  rw [deletionMap_zero_twoPair,mul_one]

lemma northNumerator_one (p : SourcePairing 1) :
    northNumerator 1 p=4*constF 1 c*torusSin (constF 1 phase^3/variableF 0) := by
  have hz : rationalNodalPolynomial 1 p.val=Polynomial.C ((rationalNodalPolynomial 1 p.val).coeff 0) := by
    apply Polynomial.eq_C_of_natDegree_le_zero
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    exact rationalNodalPolynomial_degree 1 p.val k (by simpa only [p.property,ite_true] using (show 1≤k by omega))
  have he := rationalNodalPolynomial_eval_div (0:Fin 1) p.val
  rw [hz,Polynomial.eval_C,reducedNodalDatum_eq] at he
  have hprod : (∏j:Fin 1,reflectionFactor (0:Fin 1) j)=1 := by
    apply Finset.prod_eq_one
    intro j _
    rw [Subsingleton.elim j 0]
    simp [reflectionFactor]
  rw [hprod,one_mul] at he
  exact he.trans (reducedNodalDatum_one p)

lemma polynomialNorthSource_one (p : SourcePairing 1) :
    evalLaurent (polynomialNorthSource 1 p)=
      (2*constF 1 c/constF 1 d)*torusSin (constF 1 phase^3/variableF 0) := by
  rw [polynomialNorthSource_eval_numerator,northNumerator_one]
  simp only [constF,map_div₀,map_mul,map_ofNat,map_one]
  ring

lemma scalarArchNumerator_one {K : Type*} [CommRing K] (f : ℂ →+* K) (a : Fin 1 → K) :
    scalarArchNumerator f a=a 0-f (2*(d:ℂ)-1)*(a 0+f (rho:ℂ)) := by
  have ha : a=fun _:Fin 1 =>a 0 := funext (fun i =>congrArg a (Subsingleton.elim i 0))
  rw [ha]
  unfold scalarArchNumerator
  rw [scalarValue_one]
  have he : nextScalar f (fun _:Fin 1=>a 0)=
      Polynomial.X+Polynomial.C (a 0)+Polynomial.C (f (rho:ℂ)) := by
    exact scalarValue_two (Polynomial.C.comp f) Polynomial.X (Polynomial.C (a 0))
  rw [he]
  simp [previousCoeff]

 

 


lemma arch_one_constants :
    ((2*(c:ℂ)/(d:ℂ))^2/2 = 2-2*(d:ℂ)) ∧
    ((2*(d:ℂ)-1)*(rho:ℂ)=(2-2*(d:ℂ))*(c:ℂ)) := by
  have hcs : 2*c^2 = 1-d := by
    have h := Real.cos_two_mul (3*lambda)
    rw [show 2*(3*lambda) = 6*lambda by ring,cos_six_lambda] at h
    change -d=2*c^2-1 at h
    linarith
  have hd : (d:ℂ)^2=(1/2:ℂ) := by
    simpa only [Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using congrArg Complex.ofReal d_sq
  have hdz : (d:ℂ)≠0 := by exact_mod_cast d_ne_zero
  have hc : 2*(c:ℂ)^2=1-(d:ℂ) := by exact_mod_cast hcs
  constructor
  · rw [div_pow,mul_pow,hd]
    norm_num
    linear_combination 2*hc
  · have hr : (rho:ℂ)=2*(c:ℂ)*(d:ℂ) := by exact_mod_cast rho_eq_two_c_d
    rw [hr]
    linear_combination 4*(c:ℂ)*hd

lemma arch_one_field_constants (n : ℕ) :
    ((2*constF n c/constF n d)^2/2 = 2-2*constF n d) ∧
    (constF n (2*(d:ℂ)-1)*constF n rho=(2-2*constF n d)*constF n c) := by
  constructor
  · simpa only [constF,map_div₀,map_pow,map_mul,map_ofNat,map_sub]
      using congrArg (algebraMap ℂ (SpectralField n)) arch_one_constants.1
  · simpa only [constF,map_mul,map_ofNat,map_sub,map_one]
      using congrArg (algebraMap ℂ (SpectralField n)) arch_one_constants.2

lemma polynomialNorthGluing_one : polynomialNorthGluing 1=archCandidate 1 := by
  apply IsFractionRing.injective (SpectralRing 1) (SpectralField 1)
  change evalLaurent (polynomialNorthGluing 1)=evalLaurent (archCandidate 1)
  rw [polynomialNorthGluing_eval,sourceGlue_one,polynomialNorthSource_one,
    archCandidate_eval,scalarArchNumerator_one]
  simp only [map_mul,map_div₀,map_ofNat,map_pow,reflectSpectral_torusSin,
    reflectSpectral_const,reflectSpectral_variable]
  have hz : constF 1 phase^3/(constF 1 phase^3/variableF 0)=variableF (0:Fin 1) := by
    field_simp [constF_phase_ne_zero,variableF_ne_zero]
  rw [hz]
  have hs := spectral_sine_pair (0:Fin 1)
  have hc := arch_one_field_constants 1
  change _ = spectralA 0-constF 1 (2*(d:ℂ)-1)*(spectralA 0+constF 1 rho)
  have hleft : (2*constF 1 c/constF 1 d)*torusSin (variableF 0)*
      ((2*constF 1 c/constF 1 d)*torusSin (constF 1 phase^3/variableF 0)) =
      ((2*constF 1 c/constF 1 d)^2/2) *
        (2*torusSin (variableF 0)*torusSin (constF 1 phase^3/variableF 0)) := by ring
  rw [hleft,hs,hc.1]
  have hη : constF 1 (2*(d:ℂ)-1)=2*constF 1 d-1 := by
    simp only [constF,map_sub,map_mul,map_ofNat,map_one]
  rw [hη] at hc ⊢
  linear_combination hc.2

 

theorem polynomialNorthGluing_eq_archCandidate_oai (n : ℕ) :
    polynomialNorthGluing n=archCandidate n := by
  induction n using Nat.twoStepInduction with
  | zero => rw [polynomialNorthGluing_zero,archCandidate_zero]
  | one => exact polynomialNorthGluing_one
  | more n ih₀ ih₁ =>
    apply sub_eq_zero.mp
    apply archLaurent_interpolation_zero
    · exact (polynomialNorthGluing_box _).sub (archCandidate_box _)
    · intro σ
      rw [map_sub,polynomialNorthGluing_permute,archCandidate_permute]
    · rw [map_sub,polynomialNorthGluing_parity,archCandidate_parity]
    · rw [map_sub,polynomialNorthGluing_row_reflection,archCandidate_row_reflection]
    · rw [map_sub,polynomialNorthGluing_firstFlat,archCandidate_firstFlat,ih₁,sub_self]
    · rw [map_sub,polynomialNorthGluing_merge,archCandidate_merge,ih₁,sub_self]
    · rw [map_sub,polynomialNorthGluing_delete,archCandidate_delete,ih₀,sub_self]






end
end CriticalStrip.Diagram

end OAI
end

theorem solution : type_of% @OAI.CriticalStrip.Diagram.polynomialNorthGluing_eq_archCandidate_oai := @OAI.CriticalStrip.Diagram.polynomialNorthGluing_eq_archCandidate_oai
