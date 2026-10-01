-- Prove2me | solution 1 for LovaszSchrijver.Defect.defect_deletion_contraction_lt
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T16:51:36.258116+00:00
-- url     : https://prove2.me/submissions/9842e40f-d212-4dec-baf2-e442e0c68494

import Definitions.Def_LovaszSchrijver_Defect_Index
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
namespace LSDProof
open Finset Matrix LovaszSchrijver.Defect
variable {V : Type} [Fintype V] [DecidableEq V]

lemma frac_bounds (G:SimpleGraph V) (hG:∀v,∃w,G.Adj v w) {x:V→ℝ} (hx:x∈FRAC G) :
    ∀i,0≤x i ∧ x i≤1 := by
  intro i
  obtain ⟨j,hj⟩ := hG i
  exact ⟨hx.1 i,by linarith [hx.1 j,hx.2 i j hj]⟩

lemma frac_compact (G:SimpleGraph V) (hG:∀v,∃w,G.Adj v w) : IsCompact (FRAC G) := by
  have hc : IsClosed (FRAC G) := by
    simp only [FRAC,Set.setOf_and,Set.setOf_forall]
    apply IsClosed.inter
    · exact isClosed_iInter (fun i=>isClosed_le continuous_const (continuous_apply i))
    · exact isClosed_iInter (fun i=>isClosed_iInter (fun j=>
        isClosed_iInter (fun _=>isClosed_le ((continuous_apply i).add (continuous_apply j)) continuous_const)))
  apply (isCompact_Icc : IsCompact (Set.Icc (0:V→ℝ) 1)).of_isClosed_subset hc
  intro x hx
  exact ⟨fun i=>(frac_bounds G hG hx i).1,fun i=>(frac_bounds G hG hx i).2⟩

lemma frac_max (G:SimpleGraph V) (hG:∀v,∃w,G.Adj v w) (a:V→ℝ) : ∃x,IsFRACMaximizer G a x := by
  have hne : (FRAC G).Nonempty := ⟨0,fun _=>le_rfl,fun i j hij=>by norm_num⟩
  have hc : Continuous (fun x:V→ℝ=>a ⬝ᵥ x) := by unfold dotProduct;fun_prop
  obtain ⟨x,hx,hm⟩ := (frac_compact G hG).exists_isMaxOn hne hc.continuousOn
  exact ⟨x,hx,hm⟩

lemma defect_strict (G:SimpleGraph V) (hG:∀v,∃w,G.Adj v w)
    (a d:V→ℝ) (b b' r:ℝ) (hr:IsDefect G a b r) (i:V)
    (hi:∀y,IsFRACMaximizer G a y → y i=1/2)
    (T:(V→ℝ)→V→ℝ) (hT:∀x∈FRAC G,T x∈FRAC G)
    (he:∀x∈FRAC G,a ⬝ᵥ T x-b=d ⬝ᵥ x-b') (hne:∀x∈FRAC G,T x i≠1/2) :
    ∃r':ℝ,IsDefect G d b' r' ∧ r'<r := by
  obtain ⟨x,hx,hm⟩ := frac_max G hG d
  let r' := 2*(d ⬝ᵥ x-b')
  have hr' : IsDefect G d b' r' := by
    refine ⟨⟨x,hx,rfl⟩,?_⟩
    rintro z ⟨y,hy,rfl⟩
    have hh := hm y hy
    dsimp [r'];linarith
  have hle : r'≤r := by
    have hh := hr.2 ⟨T x,hT x hx,rfl⟩
    rw [he x hx] at hh
    exact hh
  refine ⟨r',hr',lt_of_le_of_ne hle ?_⟩
  intro hh
  have hmax : IsFRACMaximizer G a (T x) := by
    refine ⟨hT x hx,?_⟩
    intro y hy
    have hb := hr.2 ⟨y,hy,rfl⟩
    have ht := he x hx
    dsimp [r'] at hh
    linarith
  exact hne x hx (hi _ hmax)

lemma defect_deletion (G:SimpleGraph V) (hG:∀v,∃w,G.Adj v w)
    (a:V→ℝ) (b r:ℝ) (hr:IsDefect G a b r) (i:V)
    (hi:∀y,IsFRACMaximizer G a y → y i=1/2) :
    ∃r':ℝ,IsDefect G (deletion a i) b r' ∧ r'<r := by
  classical
  let T : (V→ℝ)→V→ℝ := fun x=>Function.update x i 0
  apply defect_strict G hG a (deletion a i) b b r hr i hi T
  · intro x hx
    have hn : ∀j,0≤T x j := by intro j;by_cases hj:j=i <;> simp [T,hj,hx.1 j]
    have hl : ∀j,T x j≤x j := by
      intro j
      by_cases hj:j=i
      · subst j;simp [T,hx.1 i]
      · simp [T,hj]
    exact ⟨hn,fun j k hjk=>by linarith [hl j,hl k,hx.2 j k hjk]⟩
  · intro x hx
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj:j=i <;> simp [T,deletion,hj]
  · intro x hx
    norm_num [T]

lemma defect_contraction (G:SimpleGraph V) [DecidableRel G.Adj] (hG:∀v,∃w,G.Adj v w)
    (a:V→ℝ) (b r:ℝ) (hr:IsDefect G a b r) (i:V)
    (hi:∀y,IsFRACMaximizer G a y → y i=1/2) :
    ∃r':ℝ,IsDefect G (contraction G a i) (b-a i) r' ∧ r'<r := by
  classical
  let T : (V→ℝ)→V→ℝ := fun x j=>if j=i then 1 else if G.Adj i j then 0 else x j
  apply defect_strict G hG a (contraction G a i) b (b-a i) r hr i hi T
  · intro x hx
    have hn : ∀j,0≤T x j := by intro j;dsimp [T];split_ifs <;> first | exact zero_le_one | exact le_rfl | exact hx.1 j
    have hl : ∀j,j≠i → T x j≤x j := by intro j hj;simp only [T,if_neg hj];split_ifs <;> first | exact hx.1 j | exact le_rfl
    refine ⟨hn,?_⟩
    intro j k hjk
    by_cases hj:j=i
    · subst j
      have hk:k≠i := hjk.ne.symm
      simp [T,hk,hjk]
    · by_cases hk:k=i
      · subst k
        have hj' : G.Adj i j := hjk.symm
        simp [T,hj,hj']
      · linarith [hl j hj,hl k hk,hx.2 j k hjk]
  · intro x hx
    have hpt (j:V) : a j*T x j=(contraction G a i) j*x j+(if j=i then a i else 0) := by
      by_cases hj:j=i
      · subst j;simp [T,contraction]
      · by_cases hn:G.Adj i j <;> simp [T,contraction,hj,hn]
    have hd : a ⬝ᵥ T x=(contraction G a i) ⬝ᵥ x+a i := by
      simp only [dotProduct]
      rw [Finset.sum_congr rfl (fun j _=>hpt j),Finset.sum_add_distrib]
      simp
    rw [hd];ring
  · intro x hx
    norm_num [T]

end LSDProof

namespace LovaszSchrijver.Defect

theorem _root_.solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (a : V → ℕ) (b : ℕ) (hvalid : Valid (STAB G) (fun j => (a j : ℝ)) b)
    (r : ℝ) (hr : IsDefect G (fun j => (a j : ℝ)) b r) (hr0 : 0 < r)
    (i : V) (hi : ∀ y : V → ℝ, IsFRACMaximizer G (fun j => (a j : ℝ)) y → y i = 1 / 2) :
    (∃ r₁ : ℝ, IsDefect G (deletion (fun j => (a j : ℝ)) i) b r₁ ∧ r₁ < r) ∧
    (∃ r₂ : ℝ, IsDefect G (contraction G (fun j => (a j : ℝ)) i) ((b : ℝ) - (a i : ℝ)) r₂ ∧
      r₂ < r) := by
  exact ⟨LSDProof.defect_deletion G hG _ b r hr i hi,LSDProof.defect_contraction G hG _ b r hr i hi⟩

end LovaszSchrijver.Defect
