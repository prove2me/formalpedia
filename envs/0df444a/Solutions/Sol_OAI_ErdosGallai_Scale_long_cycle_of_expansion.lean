-- Prove2me | solution 1 for OAI.ErdosGallai.Scale.long_cycle_of_expansion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T02:06:09.107225+00:00
-- url     : https://prove2.me/submissions/a6f27810-b039-4ed2-8736-1036496b42a4

import Mathlib
import Definitions.Def_OAIQWEGC000
import Theorems.Thm_OAI_ErdosGallai_Scale_exists_long_path_of_vertex_expansion

section
-- module Solutions.OAIQW_ErdosGallai.DepthFirstSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai.Scale
open Finset SimpleGraph
variable {V : Type cycleUniverse2} [Fintype V] [DecidableEq V]

theorem exists_long_stack (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : ℝ) (hα : α ≤ 1) (hexp : VertexExpansion G α) :
    ∃ L : List V, L.Nodup ∧ L.IsChain G.Adj ∧ α * Fintype.card V / 3 ≤ (L.length : ℝ) :=
  exists_long_path_of_vertex_expansion G α hα hexp

end ErdosGallai.Scale
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.ExpansionBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Scale
open Finset SimpleGraph
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]

lemma chain_reachable {V : Type cycleUniverse2} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {H : SimpleGraph V} {L : List V} (hL : L.IsChain H.Adj)
    {x y : V} (hx : x ∈ L) (hy : y ∈ L) : H.Reachable x y := by
  let : Trans H.Reachable H.Reachable H.Reachable := ⟨fun h₁ h₂ => h₁.trans h₂⟩
  cases L with
  | nil => simp at hx
  | cons a L =>
    have hC : (a::L).IsChain H.Reachable := hL.imp (fun _ _ h => h.reachable)
    have ha : ∀ b ∈ a::L, H.Reachable a b := by
      intro b hb
      rcases List.mem_cons.mp hb with rfl|hb
      · exact .refl _
      · exact hC.rel_cons hb
    exact (ha x hx).symm.trans (ha y hy)

theorem connector_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (α m : ℝ) (hα : 0 ≤ α) (hexp : VertexExpansion G α)
    (X Z J : Finset V) (hX : X.Nonempty) (hZ : Z.Nonempty)
    (hXJ : Disjoint X J) (hZJ : Disjoint Z J)
    (hconnX : ∀ x ∈ X, ∀ y ∈ X, (avoidGraph G J).Reachable x y)
    (_hconnZ : ∀ x ∈ Z, ∀ y ∈ Z, (avoidGraph G J).Reachable x y)
    (hmX : m ≤ (X.card : ℝ)) (hmZ : m ≤ (Z.card : ℝ))
    (hJ : (J.card : ℝ) < α*m) :
    ∃ x ∈ X, ∃ z ∈ Z, (avoidGraph G J).Reachable x z := by
  classical
  by_contra hn
  obtain ⟨x,hx⟩ := hX
  obtain ⟨z,hz⟩ := hZ
  let H := avoidGraph G J
  let A : Finset V := univ.filter (fun v => v ∉ J ∧ H.Reachable x v)
  let B : Finset V := univ \ (J ∪ A)
  have hXA : X ⊆ A := by
    intro y hy
    exact mem_filter.mpr ⟨mem_univ _,
      (Finset.disjoint_left.mp hXJ hy), hconnX x hx y hy⟩
  have hZA : ∀ y ∈ Z, ¬ H.Reachable x y := by
    intro y hy hr
    exact hn ⟨x,hx,y,hy,hr⟩
  have hZB : Z ⊆ B := by
    intro y hy
    simp only [B, Finset.mem_sdiff, mem_univ, true_and, mem_union, not_or]
    refine ⟨Finset.disjoint_left.mp hZJ hy, ?_⟩
    intro ha
    exact hZA y hy (mem_filter.mp ha).2.2
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro y ha hb
    exact (mem_sdiff.mp hb).2 (mem_union_right J ha)
  have hc : A.card + B.card ≤ Fintype.card V := by
    rw [← card_union_of_disjoint hAB]
    exact card_le_univ _
  have hboundaryA : externalNeighbors G A ⊆ J := by
    intro v hv
    obtain ⟨_,hva,u,hu,hadj⟩ := mem_filter.mp hv
    by_contra hvj
    obtain ⟨_,huj,hru⟩ := mem_filter.mp hu
    have hadjH : H.Adj u v := ⟨hadj,huj,hvj⟩
    exact hva (mem_filter.mpr ⟨mem_univ _,hvj,hru.trans hadjH.reachable⟩)
  have hboundaryB : externalNeighbors G B ⊆ J := by
    intro v hv
    obtain ⟨_,hvb,u,hu,hadj⟩ := mem_filter.mp hv
    by_contra hvj
    have hva : v ∈ A := by
      by_contra hna
      exact hvb (mem_sdiff.mpr ⟨mem_univ _, by simpa using And.intro hvj hna⟩)
    obtain ⟨_,_,hrv⟩ := mem_filter.mp hva
    have huj : u ∉ J := fun h => (mem_sdiff.mp hu).2 (mem_union_left A h)
    have hadjH : H.Adj v u := ⟨hadj.symm,hvj,huj⟩
    have hua : u ∈ A := mem_filter.mpr ⟨mem_univ _,huj,hrv.trans hadjH.reachable⟩
    exact (mem_sdiff.mp hu).2 (mem_union_right J hua)
  have hcontr (Q : Finset V) (hne : Q.Nonempty) (hsmall : 2*Q.card ≤ Fintype.card V)
      (hm : m ≤ (Q.card : ℝ)) (hb : externalNeighbors G Q ⊆ J) : False := by
    have he := hexp Q hne hsmall
    have hc : ((externalNeighbors G Q).card : ℝ) ≤ J.card := by
      exact_mod_cast card_le_card hb
    have hh := mul_le_mul_of_nonneg_left hm hα
    linarith
  by_cases hsmall : 2*A.card ≤ Fintype.card V
  · exact hcontr A ⟨x,hXA hx⟩ hsmall
      (hmX.trans (by exact_mod_cast card_le_card hXA)) hboundaryA
  · exact hcontr B ⟨z,hZB hz⟩ (by omega)
      (hmZ.trans (by exact_mod_cast card_le_card hZB)) hboundaryB

lemma avoid_support {V : Type cycleUniverse3} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (J : Finset V) {x z : V}
    (p : (avoidGraph G J).Walk x z) (hx : x ∉ J) :
    ∀ w ∈ p.support, w ∉ J := by
  induction p with
  | nil => simpa using hx
  | @cons u v z hadj p ih =>
    intro w hw
    rcases List.mem_cons.mp hw with rfl|hw
    · exact hx
    · exact ih hadj.2.2 w hw

theorem shortest_set_connector (G : SimpleGraph V) (X Z J : Finset V)
    (hXJ : Disjoint X J)
    (hr : ∃ x ∈ X, ∃ z ∈ Z, (avoidGraph G J).Reachable x z) :
    ∃ x ∈ X, ∃ z ∈ Z, ∃ p : G.Walk x z,
      p.IsPath ∧ ∀ w ∈ p.support, w ∉ J ∧ (w ∈ X → w = x) ∧ (w ∈ Z → w = z) := by
  classical
  let H := avoidGraph G J
  let P : ℕ → Prop := fun k => ∃ x ∈ X, ∃ z ∈ Z, ∃ p : H.Walk x z,
    p.IsPath ∧ p.length = k
  have hP : ∃ k, P k := by
    obtain ⟨x,hx,z,hz,hr⟩ := hr
    obtain ⟨p,hp⟩ := hr.exists_isPath
    exact ⟨p.length,x,hx,z,hz,p,hp,rfl⟩
  obtain ⟨x,hx,z,hz,p,hp,hplen⟩ := Nat.find_spec hP
  have hmin : ∀ a ∈ X, ∀ b ∈ Z, ∀ q : H.Walk a b, q.IsPath → p.length ≤ q.length := by
    intro a ha b hb q hq
    rw [hplen]
    exact Nat.find_min' hP ⟨a,ha,b,hb,q,hq,rfl⟩
  have hsub : H ≤ G := fun _ _ h => h.1
  refine ⟨x,hx,z,hz,p.mapLe hsub,(hp.mapLe hsub),?_⟩
  intro w hw
  rw [Walk.support_mapLe_eq_support] at hw
  refine ⟨avoid_support G J p (Finset.disjoint_left.mp hXJ hx) w hw,?_,?_⟩
  · intro hwX
    by_contra hne
    have hlt := Walk.length_dropUntil_lt_length hw hne
    have hle := hmin w hwX z hz (p.dropUntil w hw) (hp.dropUntil hw)
    omega
  · intro hwZ
    by_contra hne
    have hlt := Walk.length_takeUntil_lt_length hw hne
    have hle := hmin x hx w hwZ (p.takeUntil w hw) (hp.takeUntil hw)
    omega

lemma path_cons_append {V : Type cycleUniverse4} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) (x z : V) (B : List V)
    (hC : (x :: (B ++ [z])).IsChain G.Adj) :
    ∃ p : G.Walk x z, p.support = x :: (B ++ [z]) := by
  let L := x :: (B ++ [z])
  have hn : L ≠ [] := by simp [L]
  let p := Walk.ofSupport L hn hC
  have hx : L.head hn = x := rfl
  have hz : L.getLast hn = z := by simp [L]
  exact ⟨p.copy hx hz, by
    change ((Walk.ofSupport L hn hC).copy hx hz).support = L
    rw [Walk.support_copy, Walk.support_ofSupport]⟩

theorem cycle_across_middle (G : SimpleGraph V) (X J Z : List V)
    (hnd : (X ++ J ++ Z).Nodup) (hC : (X ++ J ++ Z).IsChain G.Adj)
    (hj : 1 ≤ J.length)
    (hc : ∃ x ∈ X, ∃ z ∈ Z, ∃ q : G.Walk x z,
      q.IsPath ∧ ∀ w ∈ q.support, w ∉ J ∧ (w ∈ X → w = x) ∧ (w ∈ Z → w = z)) :
    ∃ a : V, ∃ c : G.Walk a a, c.IsCycle ∧ J.length + 2 ≤ c.length := by
  obtain ⟨x,hx,z,hz,q,hq,havoid⟩ := hc
  obtain ⟨A,B,hX⟩ := List.mem_iff_append.mp hx
  obtain ⟨C,D,hZ⟩ := List.mem_iff_append.mp hz
  let M := x :: ((B ++ J ++ C) ++ [z])
  have heq : X ++ J ++ Z = A ++ (M ++ D) := by
    simp [hX,hZ,M,List.append_assoc]
  have hMC : M.IsChain G.Adj := by
    rw [heq] at hC
    exact hC.right_of_append.left_of_append
  have hMN : M.Nodup := by
    rw [heq] at hnd
    exact (List.nodup_append.mp (List.nodup_append.mp hnd).2.1).1
  obtain ⟨p,hpS⟩ := path_cons_append G x z (B ++ J ++ C) hMC
  have hp : p.IsPath := by
    rw [Walk.isPath_def,hpS]
    exact hMN
  have hlen : J.length + 1 ≤ p.length := by
    have ht := p.length_support
    rw [hpS] at ht
    simp only [List.length_cons,List.length_append] at ht
    omega
  have hxs : x ∉ p.support.tail := by
    have hn := hp.support_nodup
    rw [← p.cons_tail_support] at hn
    exact (List.nodup_cons.mp hn).1
  have hzs : z ∉ q.reverse.support.tail := by
    have hn := hq.reverse.support_nodup
    rw [← q.reverse.cons_tail_support] at hn
    exact (List.nodup_cons.mp hn).1
  have hdis : p.support.tail.Disjoint q.reverse.support.tail := by
    apply List.disjoint_left.mpr
    intro w hwP hwQ
    have hwq : w ∈ q.support := by
      simpa using List.mem_of_mem_tail hwQ
    obtain ⟨hwJ,hwX,hwZ⟩ := havoid w hwq
    have hwp : w ∈ X ++ J ++ Z := by
      rw [heq]
      have : w ∈ M := by
        change w ∈ x :: ((B ++ J ++ C) ++ [z])
        rw [← hpS]
        exact List.mem_of_mem_tail hwP
      simp only [List.mem_append]
      exact Or.inr (Or.inl this)
    simp only [List.mem_append] at hwp
    rcases hwp with (hw|hw)|hw
    · exact hxs (hwX hw ▸ hwP)
    · exact hwJ hw
    · exact hzs (hwZ hw ▸ hwQ)
  have hxz : x ≠ z := by
    intro he
    have hz : z ∈ p.support.tail := by simp [hpS]
    exact hxs (he ▸ hz)
  have hqlen : 1 ≤ q.length := by
    by_contra hh
    have : q.length = 0 := by omega
    exact hxz (Walk.eq_of_length_eq_zero this)
  refine ⟨x,p.append q.reverse,hp.isCycle_append hq.reverse hdis (Or.inl (by omega)),?_⟩
  simp only [Walk.length_append,Walk.length_reverse]
  omega

theorem long_cycle_of_expansion_oai (G : SimpleGraph V) [DecidableRel G.Adj]
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hexp : ∀ U : Finset V, U.Nonempty → 2 * U.card ≤ Fintype.card V →
      α * U.card ≤ ((Finset.univ.filter (fun v => v ∉ U ∧ ∃ u ∈ U, G.Adj u v)).card : ℝ))
    (hq : 1 ≤ α^2 * Fintype.card V / 100) :
    ∃ a : V, ∃ c : G.Walk a a, c.IsCycle ∧
      α^2 * Fintype.card V / 100 < (c.length : ℝ) := by
  classical
  replace hexp : VertexExpansion G α := hexp
  obtain ⟨L,hnd,hchain,hL⟩ := exists_long_stack G α hα1 hexp
  let q := α^2 * Fintype.card V / 100
  let j := ⌊q⌋₊
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hjle : (j : ℝ) ≤ q := Nat.floor_le hq0
  have hjlt : q < (j : ℝ)+1 := Nat.lt_floor_add_one q
  have hj1 : 1 ≤ j := by exact (Nat.le_floor_iff hq0).mpr (by simpa [q] using hq)
  have hL0 : (0 : ℝ) ≤ L.length := Nat.cast_nonneg _
  have hu0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have haa : α^2 ≤ α := by nlinarith
  have hqq : 2*q ≤ α * Fintype.card V / 6 := by
    have hh := mul_le_mul_of_nonneg_right haa hu0
    dsimp [q]
    nlinarith [mul_nonneg (le_of_lt hα) hu0]
  have hround : 2*(j+1) ≤ L.length := by
    have hroundR : 2*((j:ℝ)+1) ≤ (L.length:ℝ) := by
      have hq1 : 1 ≤ q := hq
      linarith
    exact_mod_cast hroundR
  let k := (L.length-j)/2
  let X := L.take k
  let J := (L.drop k).take j
  let Z := (L.drop k).drop j
  have heq : L = X ++ J ++ Z := by
    dsimp [X,J,Z]
    rw [List.append_assoc,List.take_append_drop,List.take_append_drop]
  have hk : k ≤ L.length := by dsimp [k]; omega
  have hjdrop : j ≤ (L.drop k).length := by simp only [List.length_drop]; dsimp [k]; omega
  have hXlen : X.length = k := by simp [X,List.length_take, min_eq_left hk]
  have hJlen : J.length = j := by dsimp [J]; rw [List.length_take, min_eq_left hjdrop]
  have hZlen : Z.length = L.length-k-j := by simp only [Z,List.length_drop]
  have houterX : L.length ≤ 4*X.length := by rw [hXlen]; dsimp [k]; omega
  have houterZ : L.length ≤ 4*Z.length := by rw [hZlen]; dsimp [k]; omega
  rw [heq] at hnd hchain
  have hnX : X.Nodup := (List.nodup_append.mp (List.nodup_append.mp hnd).1).1
  have hnJ : J.Nodup := (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.1
  have hnZ : Z.Nodup := (List.nodup_append.mp hnd).2.1
  have hXJ : X.Disjoint J := (List.nodup_append.mp hnd).1.disjoint
  have hZJ : Z.Disjoint J := by
    have hd := hnd.disjoint
    exact List.disjoint_left.mpr (fun w hwz hwj =>
      List.disjoint_left.mp hd (List.mem_append_right X hwj) hwz)
  have hXJf : Disjoint X.toFinset J.toFinset := by
    apply Finset.disjoint_left.mpr
    intro w hw hJw
    exact List.disjoint_left.mp hXJ (List.mem_toFinset.mp hw) (List.mem_toFinset.mp hJw)
  have hZJf : Disjoint Z.toFinset J.toFinset := by
    apply Finset.disjoint_left.mpr
    intro w hw hJw
    exact List.disjoint_left.mp hZJ (List.mem_toFinset.mp hw) (List.mem_toFinset.mp hJw)
  have hconnX : ∀ x ∈ X.toFinset, ∀ y ∈ X.toFinset,
      (avoidGraph G J.toFinset).Reachable x y := by
    intro x hx y hy
    apply chain_reachable (L := X) _ (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy)
    apply hchain.left_of_append.left_of_append.imp_of_mem_imp
    intro a b ha hb hab
    exact ⟨hab,fun hj => List.disjoint_left.mp hXJ ha (List.mem_toFinset.mp hj),
      fun hj => List.disjoint_left.mp hXJ hb (List.mem_toFinset.mp hj)⟩
  have hconnZ : ∀ x ∈ Z.toFinset, ∀ y ∈ Z.toFinset,
      (avoidGraph G J.toFinset).Reachable x y := by
    intro x hx y hy
    apply chain_reachable (L := Z) _ (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy)
    apply hchain.right_of_append.imp_of_mem_imp
    intro a b ha hb hab
    exact ⟨hab,fun hj => List.disjoint_left.mp hZJ ha (List.mem_toFinset.mp hj),
      fun hj => List.disjoint_left.mp hZJ hb (List.mem_toFinset.mp hj)⟩
  have hXne : X.toFinset.Nonempty := by
    rw [← Finset.card_pos,List.toFinset_card_of_nodup hnX]
    omega
  have hZne : Z.toFinset.Nonempty := by
    rw [← Finset.card_pos,List.toFinset_card_of_nodup hnZ]
    omega
  have hmX : (L.length : ℝ)/4 ≤ X.toFinset.card := by
    rw [List.toFinset_card_of_nodup hnX]
    have : (L.length : ℝ) ≤ 4*(X.length:ℝ) := by exact_mod_cast houterX
    linarith
  have hmZ : (L.length : ℝ)/4 ≤ Z.toFinset.card := by
    rw [List.toFinset_card_of_nodup hnZ]
    have : (L.length : ℝ) ≤ 4*(Z.length:ℝ) := by exact_mod_cast houterZ
    linarith
  have hsmallJ : (J.toFinset.card : ℝ) < α*((L.length:ℝ)/4) := by
    rw [List.toFinset_card_of_nodup hnJ,hJlen]
    have hmul := mul_le_mul_of_nonneg_left hL (le_of_lt hα)
    dsimp [q] at hjle
    nlinarith
  obtain ⟨x,hx,z,hz,p,hp,hpavoid⟩ := shortest_set_connector G X.toFinset Z.toFinset J.toFinset hXJf
    (connector_exists G α ((L.length:ℝ)/4) (le_of_lt hα) hexp
      X.toFinset Z.toFinset J.toFinset hXne hZne hXJf hZJf hconnX hconnZ hmX hmZ hsmallJ)
  obtain ⟨a,c,hc,hlen⟩ := cycle_across_middle G X J Z hnd hchain (by omega)
    ⟨x,List.mem_toFinset.mp hx,z,List.mem_toFinset.mp hz,p,hp,by simpa using hpavoid⟩
  refine ⟨a,c,hc,?_⟩
  rw [hJlen] at hlen
  have hlR : (j:ℝ)+2 ≤ c.length := by exact_mod_cast hlen
  change q < (c.length:ℝ)
  linarith

end ErdosGallai.Scale

end
end
end

end OAI
end

theorem solution.{cycleUniverse1} : type_of% @OAI.ErdosGallai.Scale.long_cycle_of_expansion_oai.{cycleUniverse1} := @OAI.ErdosGallai.Scale.long_cycle_of_expansion_oai.{cycleUniverse1}
