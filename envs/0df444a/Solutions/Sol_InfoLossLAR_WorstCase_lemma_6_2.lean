-- Prove2me | solution 1 for InfoLossLAR.WorstCase.lemma_6_2
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T23:20:18.029209+00:00
-- url     : https://prove2.me/submissions/ea230928-b416-4125-b733-cbe9d2449de7

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_FixedT

set_option autoImplicit false
open InfoLossLAR.WorstCase
open scoped BigOperators
namespace TreeIncidence
variable (R : Type*) [CommRing R]

private def Z (d : ℕ) : Submodule R (Fin d → R) where
  carrier := {x | ∑ i, x i = 0}
  add_mem' := by intro a b ha hb; change ∑ i, (a i+b i)=0; rw [Finset.sum_add_distrib, show ∑ i, a i=0 from ha,show ∑ i,b i=0 from hb,add_zero]
  zero_mem' := by change ∑ _ : Fin d, (0:R)=0; simp
  smul_mem' := by intro r a ha; change ∑ i,r*a i=0; rw [← Finset.mul_sum,show ∑ i,a i=0 from ha,mul_zero]

private def tailEquiv (n : ℕ) : Z R (n+1) ≃ₗ[R] (Fin n → R) where
  toFun x := fun i => x.val i.succ
  invFun y := ⟨Fin.cons (-(∑ i, y i)) y, by change ∑ i, (Fin.cons _ y) i=0; simp [Fin.sum_univ_succ]⟩
  left_inv := by
    intro x
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    have h := x.property
    change ∑ i,x.val i=0 at h
    rw [Fin.sum_univ_succ] at h
    simp only [Fin.cons_zero]
    exact (eq_neg_of_add_eq_zero_left h).symm
  right_inv := by intro x; rfl
  map_add' := by intro x y; rfl
  map_smul' := by intro r x; rfl

private def col {d : ℕ} (t : OrientedTree d) (e : t.G.edgeSet) : Fin d → R :=
  Pi.single (t.tail e) 1 - Pi.single (t.head e) 1

private theorem span_col {d : ℕ} (t : OrientedTree d) :
    Submodule.span R (Set.range (col R t)) = Z R d := by
  classical
  let S := Submodule.span R (Set.range (col R t))
  have adjacent {u v : Fin d} (h : t.G.Adj u v) :
      Pi.single u (1:R) - Pi.single v 1 ∈ S := by
    let e : t.G.edgeSet := ⟨s(u,v),t.G.mem_edgeSet.mpr h⟩
    have he : col R t e ∈ S := Submodule.subset_span ⟨e,rfl⟩
    rcases Sym2.eq_iff.mp (t.orient e) with ⟨h₁,h₂⟩|⟨h₁,h₂⟩
    · simpa [col,h₁,h₂] using he
    · simpa [col,h₁,h₂] using S.neg_mem he
  have path {u v : Fin d} (p : t.G.Walk u v) :
      Pi.single u (1:R) - Pi.single v 1 ∈ S := by
    induction p with
    | nil => simp
    | cons adj _ ih =>
      simpa only [sub_add_sub_cancel] using S.add_mem (adjacent adj) ih
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨e,rfl⟩
    change ∑ i, col R t e i = 0
    simp [col,Finset.sum_sub_distrib,Pi.single_apply]
  · intro x hx
    have hz : ∑ i,x i=0 := hx
    obtain ⟨v⟩ := t.isTree.connected.nonempty
    have hm : ∑ i, x i • (Pi.single i (1:R) - Pi.single v 1) ∈ S :=
      S.sum_mem fun i _ => S.smul_mem _ (path (t.isTree.connected.preconnected i v).some)
    convert hm using 1
    funext j
    simp [Finset.sum_apply,Pi.single_apply,mul_sub,mul_ite,Finset.sum_sub_distrib,hz,smul_eq_mul]

private theorem column_cast {d : ℕ} (t : OrientedTree d) (e : t.G.edgeSet) (v : Fin d) :
    (t.incidence v e : R) = col R t e v := by
  have hne : t.tail e ≠ t.head e := by
    have h := e.property
    rw [← t.orient e] at h
    exact (t.G.mem_edgeSet.mp h).ne
  simp only [OrientedTree.incidence,col,Pi.sub_apply,Pi.single_apply]
  split_ifs <;> simp_all

end TreeIncidence

open TreeIncidence in
theorem solution (d : ℕ) (𝒯 : OrientedTree d) :
    Fintype.card 𝒯.G.edgeSet = d - 1 ∧
    LinearIndependent ℤ (fun e : 𝒯.G.edgeSet => fun i : Fin d => 𝒯.incidence i e) ∧
    Submodule.span ℤ (Set.range fun e : 𝒯.G.edgeSet => fun i : Fin d => 𝒯.incidence i e) =
      zeroSumLattice d ∧
    LinearMap.range (Matrix.mulVecLin 𝒯.incidence) = zeroSumLattice d ∧
    (𝒯.incidence.map (Int.cast : ℤ → ℝ)).rank = d - 1 := by
  classical
  cases d with
  | zero => exact Fin.elim0 𝒯.isTree.connected.nonempty.some
  | succ n =>
    have hcard := 𝒯.isTree.card_edgeFinset
    rw [SimpleGraph.edgeFinset_card,Fintype.card_fin] at hcard
    have hz : 𝒯.incidence.col = col ℤ 𝒯 := by
      funext e i
      simpa using column_cast ℤ 𝒯 e i
    have hr : (𝒯.incidence.map (Int.cast : ℤ → ℝ)).col = col ℝ 𝒯 := by
      funext e i; exact column_cast ℝ 𝒯 e i
    have hspan : Submodule.span ℤ (Set.range 𝒯.incidence.col) = zeroSumLattice (n+1) := by
      rw [hz,span_col]; rfl
    refine ⟨by omega,?_,hspan,(Matrix.range_mulVecLin _).trans hspan,?_⟩
    · rw [linearIndependent_iff_card_eq_finrank_span,Set.finrank]
      change Fintype.card 𝒯.G.edgeSet = Module.finrank ℤ (Submodule.span ℤ (Set.range 𝒯.incidence.col))
      rw [hz,span_col,(tailEquiv ℤ n).finrank_eq,Module.finrank_fin_fun]
      omega
    · rw [Matrix.rank_eq_finrank_span_cols,hr,span_col,(tailEquiv ℝ n).finrank_eq,Module.finrank_fin_fun]
      omega
