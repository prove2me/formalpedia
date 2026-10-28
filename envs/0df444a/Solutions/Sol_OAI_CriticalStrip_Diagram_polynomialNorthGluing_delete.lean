-- Prove2me | solution 1 for OAI.CriticalStrip.Diagram.polynomialNorthGluing_delete
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T02:23:31.258708+00:00
-- url     : https://prove2.me/submissions/88734d1f-3886-4b2d-aeac-0a1bca2cdd46

import Mathlib
import Definitions.Def_OAIQ042S015

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

lemma functionMatrix_mul_apply {P Q R : Type*} [Fintype P] (f : P → Q)
    (hf : Function.Injective f) (M : Matrix P R K) (p : P) (r : R) :
    (functionMatrix (K := K) f * M) (f p) r = M p r := by
  simp only [Matrix.mul_apply,functionMatrix,optionMatrix,Function.comp_apply,Option.some.injEq,
    hf.eq_iff]
  rw [sum_eq_single p]
  · simp
  · intro q _ hq; simp [hq]
  · simp

lemma functionMatrix_mul_outside {P Q R : Type*} [Fintype P] (f : P → Q)
    (M : Matrix P R K) (q : Q) (r : R) (h : ¬ ∃ p, f p=q) :
    (functionMatrix (K := K) f * M) q r=0 := by
  simp only [Matrix.mul_apply,functionMatrix,optionMatrix,Function.comp_apply,Option.some.injEq]
  apply sum_eq_zero
  intro p _
  rw [ite_eq_right (fun he => h ⟨p,he⟩),zero_mul]

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

lemma LastMatrix.source_coeff {K : Type*} [CommRing K] {n m : ℕ}
    {M : Matrix (Pairing (m+1)) (Pairing (n+1)) K} (hM : LastMatrix M)
    (V : Pairing (n+1) → Polynomial K) (p : SourcePairing m) (k : ℕ) :
    (matrixPolynomial M V p.val).coeff k =
      (sourceBlock M).mulVec (fun q => (V q.val).coeff k) p := by
  rw [matrixPolynomial_coeff, hM.source_mulVec]

 
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



lemma LastDegree.occupied_mul_top {K : Type*} [CommRing K] {n m d : ℕ}
    (P : Pairing (n+1) → Polynomial K) (hP : LastDegree m P)
    (F : Polynomial K) (hF : F.natDegree ≤ d) (q : Pairing (n+1))
    (hq : q.Occupied (Fin.last n)) (hm : 1 ≤ m) :
    (F*P q).coeff (m+d-1) = F.coeff d * (P q).coeff (m-1) := by
  rw [show m+d-1=d+(m-1) by omega]
  apply Polynomial.coeff_mul_add_eq_of_natDegree_le hF
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    (fun k hk => hP q k (by simp only [hq,ite_true]; omega))

 
lemma isEmpty_source_zero : IsEmpty (SourcePairing 0) :=
  ⟨fun p => p.ne_empty (p.val.eq_empty_of_le_one (by omega))⟩

 

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



theorem polynomialNorthSource_delete (n : ℕ) (p : SourcePairing (n+2)) :
    pairEvaluation n 3 (polynomialNorthSource (n+2) p) =
      deletePairScalar n *
        (sourceBlock (deletionMap (m:=n+1) 0 (show 2≤n+3 by omega))).mulVec
          (fun q => deleteEvaluation n (polynomialNorthSource n q)) p := by
  let P := (vacuumData (n+2)).P
  let Q := (vacuumData n).P
  let M : Matrix (Pairing (n+3)) (Pairing (n+1)) (SpectralField (n+1)) :=
    deletionMap 0 (by omega)
  have he := rationalNodalPolynomial_pair_delete (polynomialVacuumVector (n+1))
    (polynomialVacuumVector_eval (n+1)) Q (vacuumData n).map_P
    (vacuumData n).eval_P P (vacuumData (n+2)).map_P
  have hM : LastMatrix M := deletionMap_last 0 (show 2≤n+2 by omega)
  let Q' := fun q => (Q q).map (deleteEvaluation n).toRingHom
  have hQ : LastDegree n (matrixPolynomial M Q') :=
    hM.degree Q' (((vacuumData n).degree).map (deleteEvaluation n).toRingHom)
  have hh := congrArg (fun U : Pairing (n+3) → Polynomial (SpectralField (n+1)) =>
    (U p.val).coeff (n+1)) he
  change ((P p.val).map _).coeff (n+1) =
    (deletePairPolynomial n * matrixPolynomial M Q' p.val).coeff (n+1) at hh
  have ht : (deletePairPolynomial n * matrixPolynomial M Q' p.val).coeff (n+1) =
      deletePairScalar n * (sourceBlock M).mulVec (fun q => (Q' q.val).coeff (n-1)) p := by
    by_cases hn : 1 ≤ n
    · have ht := LastDegree.occupied_mul_top _ hQ _ (deletePairPolynomial_degree n) _
        p.property hn
      have hn' : n+2-1=n+1 := by omega
      rw [hn', deletePairPolynomial_top, hM.source_coeff] at ht
      exact ht
    · have hn : n=0 := by omega
      have hz : matrixPolynomial M Q' p.val=0 := by
        apply Polynomial.ext
        intro k
        rw [Polynomial.coeff_zero]
        exact hQ p.val k (by simp [p.property, hn])
      rw [hz, mul_zero, Polynomial.coeff_zero]
      have hne : IsEmpty (SourcePairing n) := hn ▸ isEmpty_source_zero
      let := hne
      simp [Matrix.mulVec, dotProduct]
  rw [ht, Polynomial.coeff_map] at hh
  have hh' : pairEvaluation n 3 ((P p.val).coeff (n+1)) =
      deletePairScalar n * (sourceBlock M).mulVec (fun q => (Q' q.val).coeff (n-1)) p := hh
  unfold polynomialNorthSource
  simp only [map_mul]
  have hc : pairEvaluation n 3 (constantL (n+2) (1/(2*(d:ℂ)))) =
      deleteEvaluation n (constantL n (1/(2*(d:ℂ)))) := by
    change pairEvaluation n 3 (algebraMap ℂ (Laurent (n+2)) _) =
      deleteEvaluation n (algebraMap ℂ (Laurent n) _)
    rw [AlgHom.commutes, AlgHom.commutes]
  rw [hc]
  simp only [show n+2-1=n+1 by omega]
  change _ * (pairEvaluation n 3 ((P p.val).coeff (n+1))) = _
  rw [hh']
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Q', Polynomial.coeff_map]
  apply Finset.sum_congr rfl
  intro q _
  change _ * (_ * (sourceBlock M p q * (deleteEvaluation n ((Q q.val).coeff (n-1))))) =
    _ * (sourceBlock M p q * (_ * (deleteEvaluation n ((Q q.val).coeff (n-1)))))
  ring







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

lemma mapRestrict_eq_of_supported {n m : ℕ} (f : Fin n ↪o Fin m) (p : Pairing m)
    (hp : ∀ i, p.Occupied i → ∃ j, f j=i) : (p.restrict f).map f=p := by
  apply ext_adj
  intro i j
  rw [map_adj]
  constructor
  · rintro ⟨a,b,hab,rfl,rfl⟩
    exact (restrict_adj f p a b).mp hab
  · intro hij
    obtain ⟨a,rfl⟩ := hp i ⟨j,hij⟩
    obtain ⟨b,rfl⟩ := hp j ⟨f a,adj_symm hij⟩
    exact ⟨a,b,(restrict_adj f p a b).mpr hij,rfl,rfl⟩

lemma mapRestrict_omit {n : ℕ} (a : Fin (n+1)) (p : Pairing (n+1))
    (hp : ¬p.Occupied a) : (p.restrict (Fin.succAboveOrderEmb a)).map
      (Fin.succAboveOrderEmb a)=p := by
  apply mapRestrict_eq_of_supported
  intro i hi
  have hia : i ≠ a := fun he => hp (he ▸ hi)
  exact Fin.exists_succAbove_eq hia

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

lemma gluesAt_map_supported {n m : ℕ} (f : Fin n ↪o Fin m) (root : Fin n)
    (p : Pairing m) (q : Pairing n) (h : GluesAt (f root) p (q.map f)) :
    ∃ r : Pairing n, r.map f=p := by
  refine ⟨p.restrict f,mapRestrict_eq_of_supported f p ?_⟩
  intro i hi
  obtain ⟨j,hij⟩ := (h.2.1 i).mp hi
  obtain ⟨a,b,_,ha,_⟩ := (map_adj f q i j).mp hij
  exact ⟨a,ha⟩

end Pairing

 

theorem functionMatrix_glue_adjoint {K : Type*} [CommRing K] {n m : ℕ}
    (f : Fin n ↪o Fin m) (root : Fin n) :
    (glueMatrix (f root) : Matrix _ _ K) * functionMatrix (Pairing.map f) =
      functionMatrix (Pairing.map f) * glueMatrix root := by
  ext q p
  refine (mul_functionMatrix (Pairing.map f) (glueMatrix (K:=K) (f root)) q p).trans ?_
  by_cases h : ∃ r : Pairing n, r.map f=q
  · obtain ⟨r,rfl⟩ := h
    refine Eq.trans ?_ (functionMatrix_mul_apply (Pairing.map f) (Pairing.map_injective f)
      (glueMatrix (K:=K) root) r p).symm
    simp only [glueMatrix,Pairing.gluesAt_map]
  · refine Eq.trans ?_ (functionMatrix_mul_outside (Pairing.map f) (glueMatrix (K:=K) root) q p h).symm
    apply ite_eq_right
    exact fun hh => h (Pairing.gluesAt_map_supported f root q p hh)



lemma localR_vacant_right {K : Type*} [CommRing K] {n : ℕ} (a : Position n)
    (w : Weights K) (p q : Pairing n) (hp : ¬p.Occupied a.right)
    (hq : ¬q.Occupied a.right) :
    localR a w q p = if p=q then (if p.Occupied a.left then w.A else 1) else 0 := by
  have hne : a.right ≠ a.left := by
    intro he
    have h := a.adjacent
    have he' := congrArg Fin.val he
    omega
  simp only [localR,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  by_cases ha : p.Occupied a.left
  · rw [Finset.sum_eq_single .vertical₀]
    · simp [Weights.tile,optionMatrix,Pairing.tileStep,ha,hp]
    · intro t _ ht
      have ho (htb : t.Occupied 3) : p.tileStep a.left a.right a.adjacent t ≠ some q := by
        intro he
        have hh := (p.tileStep_support a.left a.right a.adjacent t q he a.right).mpr
          (by simp [Pairing.stepSupport,hne,htb])
        exact hq hh
      cases t <;> try simp_all [Weights.tile,optionMatrix,Pairing.tileStep]
      intro he
      exact (ho (by unfold Tile.Occupied Tile.Adj Tile.edges; decide) he).elim
    · simp
  · rw [Finset.sum_eq_single .vacant]
    · simp [Weights.tile,optionMatrix,Pairing.tileStep,ha,hp]
    · intro t _ ht
      have ho (htb : t.Occupied 3) : p.tileStep a.left a.right a.adjacent t ≠ some q := by
        intro he
        have hh := (p.tileStep_support a.left a.right a.adjacent t q he a.right).mpr
          (by simp [Pairing.stepSupport,hne,htb])
        exact hq hh
      cases t <;> try simp_all [Weights.tile,optionMatrix,Pairing.tileStep]
      intro he
      exact (ho (by unfold Tile.Occupied Tile.Adj Tile.edges; decide) he).elim
    · simp



lemma transpose_functionMatrix_mul_apply {K P Q R : Type*} [CommRing K]
    [Fintype Q] (f : P → Q) (M : Matrix Q R K) (p : P) (r : R) :
    ((functionMatrix (K:=K) f).transpose * M) p r = M (f p) r := by
  simpa only [functionMatrix,Function.comp_apply,Option.elim_some] using
    transpose_optionMatrix_mul_apply M (some ∘ f) p r






lemma sum_tiles {K : Type*} [AddCommMonoid K] (f : Tile → K) :
    ∑ t, f t = f .vacant + f .vertical₀ + f .vertical₁ + f .diagonal₀ +
      f .diagonal₁ + f .cap + f .cup + f .verticalPair + f .capCup := by
  change (∑ t ∈ ({.vacant,.vertical₀,.vertical₁,.diagonal₀,.diagonal₁,.cap,.cup,
    .verticalPair,.capCup} : Finset Tile), f t) = _
  simp [add_assoc]

lemma mul_localR_apply {K Q : Type*} [CommRing K] {n : ℕ}
    (M : Matrix Q (Pairing n) K) (a : Position n) (w : Weights K)
    (q : Q) (p : Pairing n) :
    (M * localR a w) q p = ∑ t : Tile,
      w.tile t * (p.tileStep a.left a.right a.adjacent t).elim 0 (M q) := by
  simp only [localR,Matrix.mul_sum,Matrix.mul_smul,Matrix.sum_apply,Matrix.smul_apply,
    smul_eq_mul,mul_optionMatrix_apply]

lemma localR_apply {K : Type*} [CommRing K] {n : ℕ}
    (a : Position n) (w : Weights K) (q p : Pairing n) :
    localR a w q p = ∑ t : Tile,
      w.tile t * (p.tileStep a.left a.right a.adjacent t).elim 0
        (fun r => if r=q then 1 else 0) := by
  have h := mul_localR_apply (1 : Matrix (Pairing n) (Pairing n) K) a w q p
  have h1 : (1 : Matrix (Pairing n) (Pairing n) K) q = (fun r => if r=q then 1 else 0) := by
    funext r
    simp [Matrix.one_apply,eq_comm]
  rw [h1,Matrix.one_mul] at h
  exact h

lemma mul_vacantProjection_apply {K Q : Type*} [CommRing K] {n : ℕ}
    (M : Matrix Q (Pairing n) K) (b : Fin n) (q : Q) (p : Pairing n) :
    (M * vacantProjection (K:=K) b) q p = if p.Occupied b then 0 else M q p := by
  rw [vacantProjection,Matrix.mul_diagonal]
  by_cases hp : p.Occupied b <;> simp [hp]

lemma functionMatrix_mul_transpose_omit {K : Type*} [CommRing K] {n : ℕ}
    (b : Fin (n+1)) :
    functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb b)) *
      (functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb b))).transpose =
    vacantProjection (K:=K) b := by
  ext q p
  by_cases hp : p.Occupied b
  · rw [Matrix.mul_apply]
    have hz : (vacantProjection (K:=K) b) q p=0 := by
      by_cases he : q=p <;> simp [vacantProjection,he,hp]
    rw [hz]
    apply Finset.sum_eq_zero
    intro r _
    have hne : r.map (Fin.succAboveOrderEmb b) ≠ p := fun he =>
      r.map_not_occupied_omit b (he.symm ▸ hp)
    simp [Matrix.transpose_apply,functionMatrix,optionMatrix,hne]
  · have he := Pairing.mapRestrict_omit b p hp
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (p.restrict (Fin.succAboveOrderEmb b))]
    · by_cases hqp : q=p
      · subst q
        simp [Matrix.transpose_apply,functionMatrix,optionMatrix,he,vacantProjection,hp]
      · simp [Matrix.transpose_apply,functionMatrix,optionMatrix,he,vacantProjection,hqp,Ne.symm hqp]
    · intro r _ hr
      have hn : r.map (Fin.succAboveOrderEmb b) ≠ p := by
        intro h
        exact hr ((Pairing.map_injective _).eq_iff.mp (h.trans he.symm))
      simp [Matrix.transpose_apply,functionMatrix,optionMatrix,hn]
    · simp



lemma C_ne_zero : C≠0 := by
  rw [←sin_three_lambda_eq_C]
  exact ne_of_gt sin_three_lambda_pos

lemma torusL_phase_two (n : ℕ) : torusL (constF n phase ^ 2)=constF n C := by
  rw [torusL,←pow_add,←pow_add]
  norm_num only [Nat.reduceAdd]
  rw [torusSin_phase_pow,torusSin_phase_pow]
  simp only [Nat.cast_ofNat,sin_four_lambda_eq_one,sin_five_lambda_eq,sin_three_lambda_eq_C]
  simp only [Complex.ofReal_one,constF,map_one,one_mul]






lemma functionMatrix_vacantProjection {K : Type*} [CommRing K] {n m : ℕ}
    (f : Fin n ↪o Fin m) (i : Fin n) :
    functionMatrix (K:=K) (Pairing.map f) * vacantProjection (K:=K) i =
      vacantProjection (K:=K) (f i) * functionMatrix (K:=K) (Pairing.map f) := by
  ext q p
  simp only [vacantProjection,Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases h : p.map f=q
  · subst q
    simp only [Pairing.map_occupied]
    ring
  · simp [functionMatrix,optionMatrix,h]


lemma twoVacancyInsertion_mul_transpose {K : Type*} [CommRing K] {n : ℕ}
    (r : ℕ) (hr : r+2≤n+2) :
    twoVacancyInsertion (K:=K) r hr * (twoVacancyInsertion (K:=K) r hr).transpose =
      vacantProjection (K:=K) (PartialColumn.rowPosition r hr).left *
        vacantProjection (K:=K) (PartialColumn.rowPosition r hr).right := by
  let b : Fin (n+2) := ⟨r+1,by omega⟩
  let a : Fin (n+1) := ⟨r,by omega⟩
  have hab : b.succAbove a = (PartialColumn.rowPosition r hr).left := by
    rw [Fin.succAbove_of_castSucc_lt]
    · rfl
    · change r < r+1; omega
  unfold twoVacancyInsertion
  let B := functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb b))
  let A := functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb a))
  calc
    _ = (B*A) * (A.transpose*B.transpose) :=
      congrArg (fun M => (B*A)*M) (Matrix.transpose_mul B A)
    _ = B * (A * (A.transpose * B.transpose)) := Matrix.mul_assoc _ _ _
    _ = B * ((A * A.transpose) * B.transpose) :=
      congrArg (fun M => B*M) (Matrix.mul_assoc A A.transpose B.transpose).symm
    _ = (B * (A * A.transpose)) * B.transpose := (Matrix.mul_assoc _ _ _).symm
    _ = (B * vacantProjection (K:=K) a) * B.transpose :=
      congrArg (fun M => (B*M)*B.transpose) (functionMatrix_mul_transpose_omit a)
    _ = (vacantProjection (K:=K) (b.succAbove a) * B) * B.transpose :=
      congrArg (fun M => M*B.transpose) (functionMatrix_vacantProjection (Fin.succAboveOrderEmb b) a)
    _ = vacantProjection (K:=K) (b.succAbove a) * (B*B.transpose) := Matrix.mul_assoc _ _ _
    _ = vacantProjection (K:=K) (b.succAbove a) * vacantProjection (K:=K) b :=
      congrArg (fun M => vacantProjection (K:=K) (b.succAbove a)*M) (functionMatrix_mul_transpose_omit b)
    _ = _ := by rw [hab]; rfl

 

lemma localR_factor_deletion {K : Type*} [CommRing K] {n : ℕ} (a : Position n) :
    localR a (deletionWeights : Weights K) * vacantProjection (K:=K) a.left *
      vacantProjection (K:=K) a.right * localR a (deletionWeights : Weights K) =
    localR a (deletionWeights : Weights K) := by
  ext q p
  rw [mul_localR_apply,localR_apply]
  simp only [sum_tiles,deletionWeights,Weights.tile]
  by_cases ha : p.Occupied a.left
  · by_cases hb : p.Occupied a.right
    · by_cases hn : p.Adj a.left a.right
      · simp [Pairing.tileStep,ha,hb,hn]
      · let s := p.capRemove a.left a.right a.adjacent ha hb hn
        have hsa : ¬s.Occupied a.left := (p.capRemove_vacant _ _ _ ha hb hn).1
        have hsb : ¬s.Occupied a.right := (p.capRemove_vacant _ _ _ ha hb hn).2
        simp only [Pairing.tileStep,ha,hb,hn,not_true_eq_false,and_false,
          and_true,ite_true,ite_false,dite_true,dite_false,Option.elim_none,
          Option.elim_some,zero_mul,mul_zero,add_zero,zero_add,one_mul]
        change ((localR a (⟨0,0,1,0,1⟩ : Weights K) * vacantProjection (K:=K) a.left *
          vacantProjection (K:=K) a.right) q s) +
          ((localR a (⟨0,0,1,0,1⟩ : Weights K) * vacantProjection (K:=K) a.left *
          vacantProjection (K:=K) a.right) q (s.insertCup a.left a.right a.adjacent hsa hsb)) = _
        simp only [mul_vacantProjection_apply,hsb,hsa,Pairing.insertCup_occupied,
          or_true,true_or,ite_true,ite_false,add_zero]
        rw [localR_apply]
        simp only [sum_tiles,Weights.tile,Pairing.tileStep,hsa,hsb,not_false_eq_true,
          and_self,and_false,false_and,ite_true,ite_false,dite_true,dite_false,Option.elim_none,
          Option.elim_some,mul_zero,add_zero,one_mul]
        rfl
    · simp [Pairing.tileStep,ha,hb]
  · by_cases hb : p.Occupied a.right
    · simp [Pairing.tileStep,ha,hb]
    · simp only [Pairing.tileStep,ha,hb,not_false_eq_true,and_self,and_false,false_and,
        ite_true,ite_false,dite_true,dite_false,Option.elim_none,Option.elim_some,
        mul_zero,add_zero,one_mul]
      simp only [mul_vacantProjection_apply,Pairing.insertCup_occupied,ha,hb,
        or_true,true_or,ite_true,ite_false,add_zero]
      rw [localR_apply]
      simp only [sum_tiles,Weights.tile,Pairing.tileStep,ha,hb,not_false_eq_true,
        and_self,and_false,false_and,ite_true,ite_false,dite_true,dite_false,
        Option.elim_none,Option.elim_some,mul_zero,add_zero,one_mul]


theorem deletionMap_mul_projection {n m : ℕ} (r : ℕ) (hr : r+2≤n+2) :
    deletionMap (m:=m) r hr * deletionProjection r hr =
      localR (PartialColumn.rowPosition r hr) (torusWeights (constF m phase^3)) := by
  let E := twoVacancyInsertion (K:=SpectralField m) r hr
  let S := localR (PartialColumn.rowPosition r hr) (deletionWeights : Weights (SpectralField m))
  change (S*E) * (E.transpose*S) = _
  calc
    _ = S * (E * (E.transpose * S)) := Matrix.mul_assoc _ _ _
    _ = S * ((E * E.transpose) * S) :=
      congrArg (fun M => S*M) (Matrix.mul_assoc E E.transpose S).symm
    _ = (S * (E * E.transpose)) * S := (Matrix.mul_assoc _ _ _).symm
    _ = (S * (vacantProjection (K:=SpectralField m) (PartialColumn.rowPosition r hr).left *
        vacantProjection (K:=SpectralField m) (PartialColumn.rowPosition r hr).right)) * S :=
      congrArg (fun M => (S*M)*S) (twoVacancyInsertion_mul_transpose r hr)
    _ = ((S * vacantProjection (K:=SpectralField m) (PartialColumn.rowPosition r hr).left) *
        vacantProjection (K:=SpectralField m) (PartialColumn.rowPosition r hr).right) * S :=
      congrArg (fun M => M*S) (Matrix.mul_assoc _ _ _).symm
    _ = _ := by
      dsimp only [S]
      rw [localR_factor_deletion,torusWeights_phase_three]

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ProjectionInjection
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

 

lemma twoVacancyInsertion_transpose_deletion {n m : ℕ} (r : ℕ) (hr : r+2≤n+2) :
    (twoVacancyInsertion (K:=SpectralField m) r hr).transpose * deletionMap (m:=m) r hr = 1 := by
  let b : Fin (n+2) := ⟨r+1,by omega⟩
  let a : Fin (n+1) := ⟨r,by omega⟩
  let f := Fin.succAboveOrderEmb b
  let g := Fin.succAboveOrderEmb a
  have hab : f a = (PartialColumn.rowPosition r hr).left := by
    change b.succAbove a = _
    rw [Fin.succAbove_of_castSucc_lt _ _ (by change r < r+1; omega)]
    rfl
  have hf (p : Pairing n) : ¬((p.map g).map f).Occupied
      (PartialColumn.rowPosition r hr).right := (p.map g).map_not_occupied_omit b
  have hg (p : Pairing n) : ¬((p.map g).map f).Occupied
      (PartialColumn.rowPosition r hr).left := by
    rw [←hab, Pairing.map_occupied]
    exact p.map_not_occupied_omit a
  unfold twoVacancyInsertion deletionMap
  let F := functionMatrix (K:=SpectralField m) (Pairing.map f)
  let G := functionMatrix (K:=SpectralField m) (Pairing.map g)
  let E := functionMatrix (K:=SpectralField m) (Pairing.map f ∘ Pairing.map g)
  let L := localR (PartialColumn.rowPosition r hr) (deletionWeights : Weights (SpectralField m))
  have hfg : F*G=E := functionMatrix_mul _ _
  calc
    _ = E.transpose * (L*E) := congrArg (fun M => M.transpose*(L*M)) hfg
    _ = (E.transpose*L)*E := (Matrix.mul_assoc _ _ _).symm
    _ = 1 := by
      ext p q
      refine (mul_functionMatrix _ _ p q).trans ?_
      refine (transpose_functionMatrix_mul_apply _ _ p _).trans ?_
      change localR (PartialColumn.rowPosition r hr) deletionWeights ((p.map g).map f) ((q.map g).map f) =
        (if p=q then (1:SpectralField m) else 0)
      rw [localR_vacant_right _ _ _ _ (hf q) (hf p)]
      simp only [hg q,ite_false,
        (Pairing.map_injective f).eq_iff,(Pairing.map_injective g).eq_iff,eq_comm]

lemma deletionMap_injective {n m : ℕ} (r : ℕ) (hr : r+2≤n+2) :
    Function.Injective (deletionMap (m:=m) r hr).mulVec := by
  intro v w hvw
  have h := congrArg (twoVacancyInsertion (K:=SpectralField m) r hr).transpose.mulVec hvw
  rwa [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,
    twoVacancyInsertion_transpose_deletion,Matrix.one_mulVec,Matrix.one_mulVec] at h


lemma LastMatrix.mulVec_extendSource {K : Type*} [CommRing K] {n m : ℕ}
    {M : Matrix (Pairing (m+1)) (Pairing (n+1)) K} (hM : LastMatrix M)
    (v : SourcePairing n → K) :
    M.mulVec (extendSource v)=extendSource ((sourceBlock M).mulVec v) := by
  funext p
  by_cases hp : p.Occupied (Fin.last m)
  · rw [hM.source_mulVec _ ⟨p,hp⟩]
    simp only [extendSource_apply]
    rw [extendSource,dite_eq_left hp]
  · rw [extendSource,dite_eq_right hp]
    apply Finset.sum_eq_zero
    intro q _
    change M p q * extendSource v q=0
    by_cases hq : q.Occupied (Fin.last n)
    · rw [hM p q (by simp [hp,hq]),zero_mul]
    · simp [extendSource,hq]

lemma LastMatrix.source_injective {K : Type*} [CommRing K] {n m : ℕ}
    {M : Matrix (Pairing (m+1)) (Pairing (n+1)) K} (hM : LastMatrix M)
    (h : Function.Injective M.mulVec) : Function.Injective (sourceBlock M).mulVec := by
  intro v w hvw
  have he := congrArg extendSource hvw
  rw [←hM.mulVec_extendSource,←hM.mulVec_extendSource] at he
  have hh := h he
  funext p
  simpa only [extendSource_apply] using congrFun hh p.val

lemma sourceBlock_deletion_injective {n m : ℕ} (r : ℕ) (hr : r+2≤n+2) :
    Function.Injective (sourceBlock (deletionMap (m:=m) r (show r+2≤n+3 by omega))).mulVec :=
  (deletionMap_last r hr).source_injective (deletionMap_injective r _)

lemma twoVacancyInsertion_last {n m : ℕ} (r : ℕ) (hr : r+2≤n+2) :
    LastMatrix (twoVacancyInsertion (K:=SpectralField m) r (show r+2≤n+3 by omega)) := by
  let b : Fin (n+2) := ⟨r+1,by omega⟩
  let a : Fin (n+1) := ⟨r,by omega⟩
  exact (LastMatrix.omit b).mul (LastMatrix.omit a)

lemma deletionProjection_last {n m : ℕ} (r : ℕ) (hr : r+2≤n+2) :
    LastMatrix (deletionProjection (m:=m) r (show r+2≤n+3 by omega)) := by
  exact (twoVacancyInsertion_last r hr).transpose.mul
    (LastMatrix.local (PartialColumn.rowPosition r hr) _)

lemma sourceBlock_deletion_factor {n m : ℕ} (r : ℕ) (hr : r+2≤n+2) :
    sourceBlock (deletionMap (m:=m) r (show r+2≤n+3 by omega)) * sourceBlock (deletionProjection r (show r+2≤n+3 by omega)) =
      sourceBlock (localR (PartialColumn.rowPosition r hr).padTop (torusWeights (constF m phase^3))) := by
  refine ((deletionMap_last r hr).source_mul _).symm.trans ?_
  exact congrArg sourceBlock (deletionMap_mul_projection r _)






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






lemma pairReflection_pairPoint (n s : ℕ) (i : Fin (n+2)) :
    pairReflection n s (pairPoint n s i) =
      constF (n+1) phase^3 / pairPoint n s ((Equiv.swap 0 1) i) := by
  have hq := constF_phase_ne_zero (n+1)
  have hz := variableF_ne_zero (0:Fin (n+1))
  have hs : constF (n+1) phase ^ (3-(s:ℤ)) = constF (n+1) phase^3 / constF (n+1) phase^s := by
    rw [zpow_sub₀ hq]
    simp
  induction i using Fin.cases with
  | zero =>
    simp only [pairPoint,Fin.cons_zero,pairReflection_variable_zero,
      Equiv.swap_apply_left,Fin.cons_one,Fin.cons_zero]
    rw [hs]; field_simp
  | succ i => induction i using Fin.cases with
    | zero =>
      simp only [Fin.succ_zero_eq_one,pairPoint,Fin.cons_one,Fin.cons_zero,map_mul,map_pow,
        pairReflection_const,pairReflection_variable_zero,Equiv.swap_apply_right]
      rw [hs]; field_simp
    | succ i =>
      have h0 : i.succ.succ ≠ (0:Fin (n+2)) := Fin.succ_ne_zero _
      have h1 : i.succ.succ ≠ (1:Fin (n+2)) := by
        intro he
        have := congrArg Fin.val he
        simp only [Fin.val_succ,Fin.val_one] at this
        omega
      rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
      simp only [pairPoint,Fin.cons_succ,pairReflection_variable_succ]

lemma pairEvaluation_swap_reflect {n : ℕ} (s : ℕ) (f : Laurent (n+2)) :
    pairEvaluation n s (permLaurent (Equiv.swap 0 1) (reflectLaurent (n+2) f)) =
      pairReflection n s (pairEvaluation n s f) := by
  unfold pairEvaluation
  rw [torusEvaluation_permLaurent,torusEvaluation_reflect,
    torusEvaluation_fieldMap (pairReflection n s) (pairReflection_const n s)]
  congr 2
  funext i
  exact (pairReflection_pairPoint n s i).symm

lemma pairReflection_deleteEvaluation {n : ℕ} (f : Laurent n) :
    pairReflection n 3 (deleteEvaluation n f) = deleteEvaluation n (reflectLaurent n f) := by
  unfold deleteEvaluation
  refine (torusEvaluation_fieldMap (pairReflection n 3) (pairReflection_const n 3)
    (deletePoint n) (fun i => show deletePoint n i ≠ 0 from variableF_ne_zero i.succ) f).trans ?_
  refine Eq.trans ?_ (torusEvaluation_reflect (deletePoint n)
    (fun i => show deletePoint n i ≠ 0 from variableF_ne_zero i.succ) f).symm
  congr 2
  funext i
  exact pairReflection_variable_succ n 3 i

lemma twistedReflectSpectral_torusCos {n : ℕ} (k : Fin n → ℤ) (z : SpectralField n) :
    twistedReflectSpectral k (torusCos z) = torusCos (twistedReflectSpectral k z) := by
  simp [torusCos,map_div₀,map_inv₀,map_ofNat]

lemma twistedReflectSpectral_fcos {n : ℕ} (k : Fin n → ℤ) (i : Fin n) (r : ℤ) :
    twistedReflectSpectral k (fcos i r) = fcos i (-r-2*k i) := by
  rw [fcos_eq,twistedReflectSpectral_torusCos]
  simp only [map_mul,map_pow,twistedReflectSpectral_const,
    twistedReflectSpectral_variable]
  have hc (j:ℤ) : constF n (phase^j) = constF n phase^j := by simp [constF]
  have hq := constF_phase_ne_zero n
  have hp : constF n phase^(-r-2*k i) =
      (constF n phase^r * (constF n phase^k i)^2)⁻¹ := by
    rw [sub_eq_add_neg,zpow_add₀ hq,zpow_neg,zpow_neg,mul_comm (2:ℤ),zpow_mul]
    simp only [zpow_ofNat,mul_inv_rev]
    ring
  rw [fcos_eq]
  simp only [hc]
  calc
    torusCos (constF n phase^r * (constF n phase^k i / variableF i)^2) =
        torusCos ((constF n phase^(-r-2*k i)*variableF i^2)⁻¹) := by
      congr 1
      rw [hp]
      field_simp
    _ = _ := torusCos_inv _

lemma pairReflection_fcos_zero (n s : ℕ) (r : ℤ) :
    pairReflection n s (fcos 0 r) = fcos 0 (-r-2*(3-(s:ℤ))) := by
  exact twistedReflectSpectral_fcos _ _ _

lemma pairReflection_fcos_succ (n s : ℕ) (i : Fin n) (r : ℤ) :
    pairReflection n s (fcos i.succ r) = fcos i.succ (-r-6) := by
  exact twistedReflectSpectral_fcos _ _ _

lemma pairReflection_deleteScalar (n : ℕ) :
    pairReflection n 3 (deletePairScalar n) = deletePairScalar n := by
  unfold deletePairScalar
  simp only [map_mul,map_add,map_sub,map_prod,pairReflection_fcos_zero,pairReflection_fcos_succ,
    pairReflection_const]
  norm_num only
  have hp : (∏ j:Fin n, (fcos j.succ (-3)-fcos 0 9)*(fcos j.succ (-3)-fcos 0 (-9))) =
      ∏ j:Fin n, (fcos j.succ (-3)-fcos 0 (-9))*(fcos j.succ (-3)-fcos 0 9) := by
    apply Finset.prod_congr rfl
    intro j _
    ring
  rw [hp]
  ring

 

 


lemma constF_C_ne_zero (n : ℕ) : constF n C≠0 := by
  simpa only [constF,map_ne_zero,Complex.ofReal_ne_zero] using C_ne_zero

lemma torusL_split_nonzero (n s : ℕ) (hs : s=2 ∨ s=3) :
    torusL (constF n phase^s) ≠ 0 := by
  rcases hs with rfl | rfl
  · rw [torusL_phase_two]; exact constF_C_ne_zero n
  · rw [torusL_phase_three]
    simpa only [←torusL_one] using torusL_one_ne_zero n

 

lemma polynomialNorthSource_reflected_pair (n s : ℕ) (hs : s=2 ∨ s=3) :
    (fun p : SourcePairing (n+2) => pairReflection n s
      (pairEvaluation n s (polynomialNorthSource (n+2) p))) =
    (sourceBlock (localR (PartialColumn.rowPosition 0 (show 2≤n+2 by omega)).padTop
      (torusWeights (constF (n+1) phase^s)))).mulVec
      (fun p => pairEvaluation n s (reflectLaurent (n+2) (polynomialNorthSource (n+2) p))) := by
  let φ := pairEvaluation n s
  let a := (PartialColumn.rowPosition 0 (show 2≤n+2 by omega)).padTop
  let x := variableF (1:Fin (n+2)) / variableF 0
  let y := constF (n+1) phase^s
  have hx : RationalAt φ.toRingHom x y := by
    have hh := (rationalAt_pair_variable (n:=n) s (1:Fin (n+2))).div
      (rationalAt_pair_variable s 0) (variableF_ne_zero 0)
    simpa only [pairPoint,Fin.cons_one,Fin.cons_zero,mul_div_cancel_right₀ _ (variableF_ne_zero 0)] using hh
  have hy : y≠0 := pow_ne_zero _ (constF_phase_ne_zero _)
  have hw : ∀ t, RationalAt φ.toRingHom ((torusWeights x).tile t) ((torusWeights y).tile t) :=
    rationalAt_torusWeights φ hx hy (torusL_split_nonzero (n+1) s hs)
  have hv (p : SourcePairing (n+2)) : RationalAt φ.toRingHom
      (reflectSpectral (n+2) (evalLaurent (polynomialNorthSource (n+2) p)))
      (pairEvaluation n s (reflectLaurent (n+2) (polynomialNorthSource (n+2) p))) := by
    rw [reflectSpectral_evalLaurent]
    exact RationalAt.algebraMap _
  funext p
  have hright := RationalAt.mulVec (φ:=φ.toRingHom)
    (sourceBlock (localR a (torusWeights x))) (sourceBlock (localR a (torusWeights y)))
    (fun q => reflectSpectral (n+2) (evalLaurent (polynomialNorthSource (n+2) q)))
    (fun q => pairEvaluation n s (reflectLaurent (n+2) (polynomialNorthSource (n+2) q)))
    (fun q q' => rationalAt_localR φ a (torusWeights x) (torusWeights y) hw q.val q'.val) hv p
  have he := congrFun (polynomialNorthSource_reflected_covariance 0 (show 2≤n+2 by omega)) p
  change permSpectral (Equiv.swap 0 1) (reflectSpectral (n+2)
    (evalLaurent (polynomialNorthSource (n+2) p))) =
    (sourceBlock (localR a (torusWeights x))).mulVec _ p at he
  rw [←he,reflectSpectral_evalLaurent,permSpectral_evalLaurent] at hright
  have hleft := RationalAt.algebraMap (φ:=φ.toRingHom) (F:=SpectralField (n+2))
    (permLaurent (Equiv.swap 0 1) (reflectLaurent (n+2) (polynomialNorthSource (n+2) p)))
  have hh := hleft.unique hright
  change pairEvaluation n s _ = _ at hh
  rw [pairEvaluation_swap_reflect] at hh
  exact hh


theorem polynomialNorthSource_reflected_delete (n : ℕ) :
    (sourceBlock (deletionProjection (m:=n+1) 0 (show 2≤n+3 by omega))).mulVec
      (fun p => pairEvaluation n 3 (reflectLaurent (n+2) (polynomialNorthSource (n+2) p))) =
      deletePairScalar n •
        (fun q => deleteEvaluation n (reflectLaurent n (polynomialNorthSource n q))) := by
  have ht : (fun p : SourcePairing (n+2) => pairReflection n 3
      (pairEvaluation n 3 (polynomialNorthSource (n+2) p))) =
      deletePairScalar n •
        (sourceBlock (deletionMap (m:=n+1) 0 (show 2≤n+3 by omega))).mulVec
          (fun q => deleteEvaluation n (reflectLaurent n (polynomialNorthSource n q))) := by
    funext p
    rw [polynomialNorthSource_delete,map_mul,pairReflection_deleteScalar,
      RingHom.map_mulVec,sourceBlock_map,deletionMap_map]
    simp only [Pi.smul_apply,smul_eq_mul]
    congr 2
    funext q
    exact pairReflection_deleteEvaluation _
  have hc := polynomialNorthSource_reflected_pair n 3 (Or.inr rfl)
  apply sourceBlock_deletion_injective (n:=n) (m:=n+1) 0 (show 2≤n+2 by omega)
  rw [Matrix.mulVec_mulVec]
  refine (congrArg (fun M => M.mulVec (fun p =>
    pairEvaluation n 3 (reflectLaurent (n+2) (polynomialNorthSource (n+2) p))))
      (sourceBlock_deletion_factor (m:=n+1) 0 (show 2≤n+2 by omega))).trans ?_
  rw [←hc,ht,Matrix.mulVec_smul]

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

lemma functionMatrix_omit_glue_adjoint {K : Type*} [CommRing K] {n : ℕ}
    (r : Fin (n+1)) :
    (glueMatrix (Fin.last (n+1)) : Matrix _ _ K) *
        functionMatrix (Pairing.map (Fin.succAboveOrderEmb r.castSucc)) =
      functionMatrix (Pairing.map (Fin.succAboveOrderEmb r.castSucc)) *
        glueMatrix (Fin.last n) := by
  simpa only [Pairing.omit_last] using
    functionMatrix_glue_adjoint (K:=K) (Fin.succAboveOrderEmb r.castSucc) (Fin.last n)

lemma position_padTop_root_ne {n : ℕ} (a : Position n) :
    Fin.last n ≠ a.padTop.left ∧ Fin.last n ≠ a.padTop.right := by
  constructor
  · intro he
    have hv := congrArg Fin.val he
    have := a.left.isLt
    simp only [Position.padTop,Fin.val_last,Fin.val_castSucc] at hv
    omega
  · intro he
    have hv := congrArg Fin.val he
    have := a.right.isLt
    simp only [Position.padTop,Fin.val_last,Fin.val_castSucc] at hv
    omega

lemma twoVacancyInsertion_glue_adjoint {K : Type*} [CommRing K] {n : ℕ}
    (r : ℕ) (hr : r+2≤n+2) :
    (glueMatrix (Fin.last (n+2)) : Matrix _ _ K) *
        twoVacancyInsertion r (show r+2≤n+3 by omega) =
      twoVacancyInsertion r (show r+2≤n+3 by omega) * glueMatrix (Fin.last n) := by
  let b : Fin (n+2) := ⟨r+1,by omega⟩
  let a : Fin (n+1) := ⟨r,by omega⟩
  let B := functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb b.castSucc))
  let A := functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb a.castSucc))
  calc
    _ = (glueMatrix (Fin.last (n+2))*B)*A := (Matrix.mul_assoc _ _ _).symm
    _ = (B*glueMatrix (Fin.last (n+1)))*A :=
      congrArg (fun M => M*A) (functionMatrix_omit_glue_adjoint b)
    _ = B*(glueMatrix (Fin.last (n+1))*A) := Matrix.mul_assoc _ _ _
    _ = B*(A*glueMatrix (Fin.last n)) :=
      congrArg (fun M => B*M) (functionMatrix_omit_glue_adjoint a)
    _ = (B*A)*glueMatrix (Fin.last n) := (Matrix.mul_assoc _ _ _).symm

lemma deletionMap_glue_adjoint {n m : ℕ} (r : ℕ) (hr : r+2≤n+2) :
    (glueMatrix (Fin.last (n+2)) : Matrix _ _ (SpectralField m)) *
        deletionMap r (show r+2≤n+3 by omega) =
      (deletionProjection r (show r+2≤n+3 by omega)).transpose * glueMatrix (Fin.last n) := by
  have adjoint {ι κ : Type} [Fintype ι] [Fintype κ]
      (G L : Matrix ι ι (SpectralField m)) (E : Matrix ι κ (SpectralField m))
      (H : Matrix κ κ (SpectralField m)) (hL : G*L=L.transpose*G) (hE : G*E=E*H) :
      G*(L*E) = (E.transpose*L).transpose*H := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
      hL, Matrix.mul_assoc, hE, ← Matrix.mul_assoc]
  let a := PartialColumn.rowPosition r hr
  let L := localR a.padTop (deletionWeights : Weights (SpectralField m))
  let E := twoVacancyInsertion (K:=SpectralField m) (n:=n+1) r (show r+2≤(n+1)+2 by omega)
  let G := glueMatrix (K:=SpectralField m) (Fin.last (n+2))
  let H := glueMatrix (K:=SpectralField m) (Fin.last n)
  have hL : G*L=L.transpose*G := localR_glue_adjoint a.padTop (Fin.last (n+2))
    (position_padTop_root_ne a).1 (position_padTop_root_ne a).2 deletionWeights
  have hE : G*E=E*H := twoVacancyInsertion_glue_adjoint r hr
  have h := adjoint G L E H hL hE
  simp only [deletionProjection] at h ⊢
  dsimp +instances only [G, L, E, H, a, deletionMap, twoVacancyInsertion,
    CStarMatrix, CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid, CStarMatrix.ofMatrix,
    Equiv.refl, Equiv.symm] at h ⊢
  simpa only [Equiv.coe_fn_mk, id_eq, PartialColumn.rowPosition, Position.padTop,
    Fin.castSucc_mk] using h



theorem sourceGlue_delete {n m : ℕ} (r : ℕ) (hr : r+2≤n+2)
    (v : SourcePairing (n+2) → SpectralField m) (w : SourcePairing n → SpectralField m) :
    sourceGlue (n+2) v ((sourceBlock (deletionMap r (show r+2≤n+3 by omega))).mulVec w) =
      sourceGlue n ((sourceBlock (deletionProjection r (show r+2≤n+3 by omega))).mulVec v) w := by
  have h : sourceBlock (glueMatrix (K:=SpectralField m) (Fin.last (n+2))) *
      sourceBlock (deletionMap (m:=m) r (show r+2≤n+3 by omega)) =
      (sourceBlock (deletionProjection (m:=m) r (show r+2≤n+3 by omega))).transpose *
      sourceBlock (glueMatrix (K:=SpectralField m) (Fin.last n)) :=
    ((glueMatrix_last (n+2)).source_mul _).symm.trans
      ((congrArg sourceBlock (deletionMap_glue_adjoint (m:=m) r hr)).trans
        ((deletionProjection_last r hr).transpose.source_mul _))
  unfold sourceGlue
  rw [Matrix.mulVec_mulVec,h,←Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]

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



theorem polynomialNorthGluing_delete_oai (n : ℕ) :
    pairEvaluation n 3 (polynomialNorthGluing (n+2)) =
      deletePairScalar n ^ 2 * deleteEvaluation n (polynomialNorthGluing n) := by
  unfold polynomialNorthGluing
  rw [sourceGlue_algMap (pairEvaluation n 3)]
  have h : ((pairEvaluation n 3) ∘ polynomialNorthSource (n+2)) =
      deletePairScalar n •
        (sourceBlock (deletionMap (m:=n+1) 0 (show 2≤n+3 by omega))).mulVec
          (fun q => deleteEvaluation n (polynomialNorthSource n q)) := by
    funext p
    exact polynomialNorthSource_delete n p
  rw [h,sourceGlue_smul_right,sourceGlue_delete 0 (show 2≤n+2 by omega)]
  simp only [Function.comp_def]
  rw [polynomialNorthSource_reflected_delete n,sourceGlue_smul_left]
  rw [sourceGlue_algMap (deleteEvaluation n)]
  simp only [pow_two,mul_assoc]
  rfl






end
end CriticalStrip.Diagram

end OAI
end

theorem solution : type_of% @OAI.CriticalStrip.Diagram.polynomialNorthGluing_delete_oai := @OAI.CriticalStrip.Diagram.polynomialNorthGluing_delete_oai
