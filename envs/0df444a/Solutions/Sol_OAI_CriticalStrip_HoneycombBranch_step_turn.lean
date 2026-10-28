-- Prove2me | solution 1 for OAI.CriticalStrip.HoneycombBranch.step_turn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T01:59:45.042392+00:00
-- url     : https://prove2.me/submissions/57b6312f-465c-4c3a-97ee-a91b073f437a

import Mathlib
import Definitions.Def_CriticalStripMass
import Definitions.Def_OAIQ042S012

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



lemma terminal_append (next : S → Bool → S) (s : S) (l m : List Bool) :
    terminal next s (l++m) = terminal next (terminal next s l) m := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih => exact ih _

omit [DecidableEq V] in
lemma visited_append (vertex : S → V) (next : S → Bool → S) (s : S) (l m : List Bool) :
    visited vertex next s (l++m) =
      visited vertex next s l ++ visited vertex next (terminal next s l) m := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih => simp only [List.cons_append,visited,ih,terminal]

end
end CriticalStrip.FiniteBranchTree

 

 

 

namespace CriticalStrip.HoneycombBranch
noncomputable section
open scoped BigOperators Classical
open FiniteBranchTree

lemma turn_append (l m : List Bool) : turn (l++m)=turn l+turn m := by
  induction l with
  | nil => simp [turn]
  | cons b l ih => simp only [List.cons_append,turn,ih,add_assoc]

end
end CriticalStrip.HoneycombBranch

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_CollisionLeaf
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/







namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace Pairing

lemma turnOrder_reverse {n : ℕ} (i j : Fin n) : turnOrder j i= -turnOrder i j := by
  unfold turnOrder
  split_ifs <;> omega

lemma arcTurn_reverse {n : ℕ} (g : Fin n → ℤ) (i j : Fin n) :
    arcTurn g j i= -arcTurn g i j := by
  unfold arcTurn
  rw [turnOrder_reverse i j]
  ring


lemma turnPotential_of_adj {n : ℕ} {p : Pairing n} (g : Fin n → ℤ)
    {i j : Fin n} (h : p.Adj i j) :
    p.turnPotential g j-p.turnPotential g i=arcTurn g i j := by
  have hi : p.Occupied i := ⟨j,h⟩
  have hj : p.Occupied j := ⟨i,h.symm⟩
  have hpi := (p.adj_partnerOrSelf i j).mp h
  have hpj := (p.adj_partnerOrSelf j i).mp h.symm
  have hn : i≠j := fun he=>p.adj_irrefl _ (he ▸ h)
  simp only [turnPotential,hi,hj,true_and,←hpi.2,←hpj.2,arcTurn,turnOrder]
  split_ifs <;> omega

 

lemma cap_partner_orders {n : ℕ} {p : Pairing n} {a b x y : Fin n}
    (hab : a.val+1=b.val) (hx : p.Adj a x) (hy : p.Adj b y)
    (hn : ¬p.Adj a b) :
    (x<a ∧ b<y) ∨ (b<y ∧ y<x) ∨ (y<x ∧ x<a) := by
  have he:=adjacent_partners hab hx hy hn
  have hc:=not_cross hx hy
  simp only [Cross] at hc
  simp only [Fin.lt_def,Fin.ne_iff_vne] at he ⊢
  omega

lemma cap_turn_order {n : ℕ} {p : Pairing n} {a b x y : Fin n}
    (hab : a.val+1=b.val) (hx : p.Adj a x) (hy : p.Adj b y)
    (hn : ¬p.Adj a b) :
    turnOrder x a + turnOrder b y - 1 = turnOrder x y := by
  have ho:=cap_partner_orders hab hx hy hn
  simp only [turnOrder]
  split_ifs <;> rcases ho with ⟨_,_⟩|⟨_,_⟩|⟨_,_⟩ <;> omega



end Pairing

 

 

 


namespace Graph

variable {V : Type*} {n : ℕ} {r : V → V → Prop} [Std.Symm r]
  {b : Fin n → V} {p : Pairing n}

lemma boundaryConstant_eq (h : GraphRealizes r b p) (f : Fin n → ℤ)
    (hf : ∀ i j, p.Adj i j → f i=f j) {v : V} {i : Fin n}
    (hi : Relation.ReflTransGen r v (b i)) : boundaryConstant b r f v=f i := by
  have he : ∃ j,Relation.ReflTransGen r v (b j) := ⟨i,hi⟩
  rw [boundaryConstant,dite_eq_left he]
  have hj := Classical.choose_spec he
  have hc := (h.reach (Classical.choose he) i).mp ((symm hj).trans hi)
  exact hc.elim (fun hh=>congrArg f hh) (hf _ _)

lemma boundaryConstant_boundary (h : GraphRealizes r b p) (f : Fin n → ℤ)
    (hf : ∀ i j,p.Adj i j → f i=f j) (i : Fin n) :
    boundaryConstant b r f (b i)=f i :=
  boundaryConstant_eq h f hf .refl

lemma boundaryConstant_edge (h : GraphRealizes r b p) (f : Fin n → ℤ)
    (hf : ∀ i j,p.Adj i j → f i=f j) {v w : V} (hv : r v w) :
    boundaryConstant b r f v=boundaryConstant b r f w := by
  obtain ⟨i,_,hi⟩ := h.no_loop v w hv
  rw [boundaryConstant_eq h f hf hi,
    boundaryConstant_eq h f hf ((Relation.ReflTransGen.single (symm hv)).trans hi)]

 

lemma renormalize_potential (h : GraphRealizes r b p) (P : V → ℤ)
    (f : Fin n → ℤ)
    (hf : ∀ i j,p.Adj i j → f j-f i=P (b j)-P (b i)) :
    ∃ Q : V → ℤ, (∀ i,Q (b i)=f i) ∧
      ∀ v w,r v w → Q w-Q v=P w-P v := by
  let d : Fin n → ℤ := fun i=>f i-P (b i)
  have hd : ∀ i j,p.Adj i j → d i=d j := by
    intro i j hij
    have hh := hf i j hij
    dsimp only [d]
    omega
  refine ⟨fun v=>P v+boundaryConstant b r d v,?_,?_⟩
  · intro i
    dsimp only
    rw [boundaryConstant_boundary h d hd]
    simp [d]
  · intro v w hvw
    dsimp only
    rw [boundaryConstant_edge h d hd hvw]
    omega

end Graph
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TurnGate
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace Pairing



lemma cap_arcTurn_general {n : ℕ} {p : Pairing n} {a b x y : Fin n}
    (g : Fin n → ℤ) (hab : a.val+1=b.val)
    (hx : p.Adj a x) (hy : p.Adj b y) (hn : ¬p.Adj a b) :
    arcTurn g x a+(g b-g a+3)+arcTurn g b y=arcTurn g x y := by
  have hc:=cap_turn_order hab hx hy hn
  simp only [arcTurn]
  omega

lemma arcTurn_congr {n : ℕ} {g h : Fin n → ℤ} {i j : Fin n}
    (hi : g i=h i) (hj : g j=h j) : arcTurn g i j=arcTurn h i j := by
  simp only [arcTurn,hi,hj]

lemma turnOrder_embedding {n m : ℕ} (f : Fin n → Fin m) {i j : Fin n}
    (hij : f i < f j ↔ i < j) (hji : f j < f i ↔ j < i) :
    turnOrder (f i) (f j)=turnOrder i j := by simp only [turnOrder,hij,hji]


lemma gateBoundary_other {n : ℕ} (a b : Fin n) (F : Fin n → ℤ) (x y : ℤ)
    (i : Fin n) (ha : i≠a) (hb : i≠b) : gateBoundary a b F x y i=F i := by
  simp [gateBoundary,ha,hb]

lemma gatePotentials_vacant {n : ℕ} (p : Pairing n) (a b : Fin n)
    (_hab : a.val+1=b.val) (g h : Fin n → ℤ)
    (hg : ∀ i,i≠a → i≠b → h i=g i)
    (ha : ¬p.Occupied a) (hb : ¬p.Occupied b) :
    ∃ B T,GatePotentials p p a b .vacant g h B T := by
  refine ⟨p.turnPotential h,![p.turnPotential h a,p.turnPotential h b,
    p.turnPotential h a,p.turnPotential h b],?_,?_,?_,?_,?_,?_,?_⟩
  · intro i j hij
    rw [turnPotential_of_adj h hij]
    apply arcTurn_congr
    · exact hg i (fun he=>ha (he ▸ ⟨j,hij⟩)) (fun he=>hb (he ▸ ⟨j,hij⟩))
    · exact hg j (fun he=>ha (he ▸ ⟨i,hij.symm⟩)) (fun he=>hb (he ▸ ⟨i,hij.symm⟩))
  · intro i j hij
    exact (Tile.vacant_not_occupied i ⟨j,hij⟩).elim
  all_goals simp

lemma gatePotentials_through {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (g h : Fin n → ℤ)
    (hg : ∀ i,i≠a → i≠b → h i=g i) (t : Tile)
    (ht : t=.vertical₀ ∨ t=.vertical₁ ∨ t=.verticalPair)
    (hc : (t.Occupied 0 ↔ p.Occupied a) ∧ (t.Occupied 1 ↔ p.Occupied b)) :
    ∃ B T,GatePotentials p p a b t g h B T := by
  let F := p.turnPotential h
  let x := F a-(h a-g a)
  let y := F b-(h b-g b)
  let B := gateBoundary a b F x y
  have hab' : a≠b := by omega
  have he (i : Fin n) : B i=p.turnPotential g i := by
    by_cases hia : i=a
    · subst i; simp only [B,gateBoundary_left,x,F,turnPotential]; omega
    · by_cases hib : i=b
      · subst i; simp only [B,gateBoundary_right _ _ hab',y,F,turnPotential]; omega
      · simp only [B,gateBoundary_other _ _ _ _ _ _ hia hib,F,turnPotential,hg i hia hib]
  refine ⟨B,![x,y,F a,F b],⟨?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro i j hij
    rw [he i,he j]
    exact turnPotential_of_adj g hij
  · intro i j hij
    rcases ht with rfl|rfl|rfl <;> fin_cases i <;> fin_cases j <;>
      simp_all [Tile.Adj,Tile.edges,gateTurn,x,y]
  · simp [B]
  · simp [B,gateBoundary,hab'.symm]
  · rfl
  · rfl
  · exact fun i hi hj=>gateBoundary_other a b F x y i hi hj

lemma gatePotentials_cup {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (g h : Fin n → ℤ)
    (hg : ∀ i,i≠a → i≠b → h i=g i)
    (ha : ¬p.Occupied a) (hb : ¬p.Occupied b) :
    ∃ B T,GatePotentials p (p.insertCup a b hab ha hb) a b .cup g h B T := by
  let q := p.insertCup a b hab ha hb
  let F := q.turnPotential h
  have hab' : a<b := by omega
  have hq : q.Adj a b := by simp [q,Adj,insertCup]
  have hF : F b-F a=h b-h a-3 := by
    have he := turnPotential_of_adj h hq
    simpa only [F,arcTurn,turnOrder,hab',ite_true,mul_one] using he
  refine ⟨F,![F a,F b,F a,F b],⟨?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro i j hij
    have hqij : q.Adj i j := by
      rcases hij with hij | hij
      · exact Or.inl (Finset.mem_insert_of_mem hij)
      · exact Or.inr (Finset.mem_insert_of_mem hij)
    rw [show F j-F i=arcTurn h i j from turnPotential_of_adj h hqij]
    apply arcTurn_congr
    · exact hg i (fun he=>ha (he ▸ ⟨j,hij⟩)) (fun he=>hb (he ▸ ⟨j,hij⟩))
    · exact hg j (fun he=>ha (he ▸ ⟨i,hij.symm⟩)) (fun he=>hb (he ▸ ⟨i,hij.symm⟩))
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Tile.Adj,Tile.edges,gateTurn]
    omega
  all_goals simp [F,q]

lemma gatePotentials_swap {n : ℕ} (p : Pairing n) (a b : Fin n)
    (_hab : a.val+1=b.val) (g h : Fin n → ℤ)
    (hg : ∀ i,i≠a → i≠b → h i=g i) (t : Tile)
    (ht : t=.diagonal₀ ∨ t=.diagonal₁)
    (hf : ∀ i j,p.Occupied i → p.Occupied j →
      (Equiv.swap a b i < Equiv.swap a b j ↔ i<j)) :
    ∃ B T,GatePotentials p (p.mapOccupied (Equiv.swap a b).toEmbedding hf) a b t g h B T := by
  let q := p.mapOccupied (Equiv.swap a b).toEmbedding hf
  let F := q.turnPotential h
  let f := Equiv.swap a b
  let B : Fin n → ℤ := fun i=>F (f i)+g i-h (f i)
  have hBa : B a=F b+g a-h b := by simp [B,f]
  have hBb : B b=F a+g b-h a := by simp [B,f]
  refine ⟨B,![B a,B b,F a,F b],⟨?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro i j hij
    have hi : p.Occupied i := ⟨j,hij⟩
    have hj : p.Occupied j := ⟨i,hij.symm⟩
    have hq : q.Adj (f i) (f j) :=
      (mapOccupied_adj p (Equiv.swap a b).toEmbedding hf i j).mpr hij
    have hF : F (f j)-F (f i)=arcTurn h (f i) (f j) := turnPotential_of_adj h hq
    have ho : turnOrder (f i) (f j)=turnOrder i j :=
      turnOrder_embedding f (hf i j hi hj) (hf j i hj hi)
    dsimp only [B]
    simp only [arcTurn,ho] at hF ⊢
    omega
  · intro i j hij
    rcases ht with rfl|rfl <;> fin_cases i <;> fin_cases j <;>
      simp_all [Tile.Adj,Tile.edges,gateTurn] <;> omega
  · rfl
  · rfl
  · rfl
  · rfl
  · intro i hi hj
    simp [B,f,Equiv.swap_apply_of_ne_of_ne hi hj,hg i hi hj,F,q]

lemma gatePotentials_cap_general {n : ℕ} (p q : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (g h : Fin n → ℤ)
    (hg : ∀ i,i≠a → i≠b → h i=g i) (x y : Fin n)
    (hx : p.Adj a x) (hy : p.Adj b y) (hn : ¬p.Adj a b)
    (hqxy : q.Adj x y)
    (hout : ∀ i j,(p.omitTwo a b).Adj i j → q.Adj i j)
    (t : Tile) (ht : t=.cap ∨ t=.capCup)
    (hcup : t=.capCup → q.Adj a b) :
    ∃ B T,GatePotentials p q a b t g h B T := by
  let F := q.turnPotential h
  let u := F x+arcTurn g x a
  let v := u+(g b-g a+3)
  let B := gateBoundary a b F u v
  have hab' : a≠b := by omega
  obtain ⟨hxa,hxb,hya,hyb,hxy⟩ := adjacent_partners hab hx hy hn
  have hFxy : F y-F x=arcTurn g x y :=
    (turnPotential_of_adj h hqxy).trans (arcTurn_congr (hg x hxa hxb) (hg y hya hyb))
  have hcap := cap_arcTurn_general g hab hx hy hn
  have hBa : B a=u := gateBoundary_left _ _ _ _ _
  have hBb : B b=v := gateBoundary_right _ _ hab' _ _ _
  have hBx : B x=F x := gateBoundary_other _ _ _ _ _ _ hxa hxb
  have hBy : B y=F y := gateBoundary_other _ _ _ _ _ _ hya hyb
  have hax : F x-u=arcTurn g a x := by rw [arcTurn_reverse g x a]; dsimp [u]; omega
  have hby : F y-v=arcTurn g b y := by dsimp [v,u]; omega
  refine ⟨B,![u,v,F a,F b],⟨?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro i j hij
    by_cases hia : i=a
    · subst i
      have hj : j=x := adj_unique hij hx
      subst j
      rw [hBa,hBx]
      exact hax
    · by_cases hja : j=a
      · subst j
        have hi : i=x := adj_unique hij.symm hx
        subst i
        rw [hBa,hBx,arcTurn_reverse g a x]
        omega
      · by_cases hib : i=b
        · subst i
          have hj : j=y := adj_unique hij hy
          subst j
          rw [hBb,hBy]
          exact hby
        · by_cases hjb : j=b
          · subst j
            have hi : i=y := adj_unique hij.symm hy
            subst i
            rw [hBb,hBy,arcTurn_reverse g b y]
            omega
          · rw [show B i=F i from gateBoundary_other _ _ _ _ _ _ hia hib,
              show B j=F j from gateBoundary_other _ _ _ _ _ _ hja hjb]
            exact (turnPotential_of_adj h (hout i j ((omitTwo_adj _ _ _ _ _).mpr
              ⟨hij,hia,hib,hja,hjb⟩))).trans
              (arcTurn_congr (hg i hia hib) (hg j hja hjb))
  · intro i j hij
    have hablt : a<b := by omega
    have hFab : t=.capCup → F b-F a=h b-h a-3 := by
      intro ht'
      have he:=turnPotential_of_adj h (hcup ht')
      simpa only [F,arcTurn,turnOrder,hablt,ite_true,mul_one] using he
    rcases ht with rfl|rfl <;> fin_cases i <;> fin_cases j <;>
      simp_all [Tile.Adj,Tile.edges,gateTurn,v] <;> omega
  · exact hBa
  · exact hBb
  · rfl
  · rfl
  · exact fun i hi hj=>gateBoundary_other _ _ _ _ _ _ hi hj

 

theorem gatePotentials_of_step {n : ℕ} (p q : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (g h : Fin n → ℤ)
    (hg : ∀ i,i≠a → i≠b → h i=g i) (t : Tile)
    (hq : p.tileStep a b hab t=some q) :
    ∃ B T,GatePotentials p q a b t g h B T := by
  cases t with
  | vacant =>
    simp only [tileStep] at hq
    split_ifs at hq with hc
    · cases hq
      exact gatePotentials_vacant p a b hab g h hg hc.1 hc.2
  | vertical₀ =>
    simp only [tileStep] at hq
    split_ifs at hq with hc
    · cases hq
      exact gatePotentials_through p a b hab g h hg .vertical₀ (Or.inl rfl)
        (by simp [hc.1,hc.2,Tile.Occupied,Tile.Adj,Tile.edges])
  | vertical₁ =>
    simp only [tileStep] at hq
    split_ifs at hq with hc
    · cases hq
      exact gatePotentials_through p a b hab g h hg .vertical₁ (Or.inr (Or.inl rfl))
        (by simp [hc.1,hc.2,Tile.Occupied,Tile.Adj,Tile.edges])
  | verticalPair =>
    simp only [tileStep] at hq
    split_ifs at hq with hc
    · cases hq
      exact gatePotentials_through p a b hab g h hg .verticalPair (Or.inr (Or.inr rfl))
        (by simp [hc.1,hc.2,Tile.Occupied,Tile.Adj,Tile.edges])
  | diagonal₀ =>
    simp only [tileStep] at hq
    split_ifs at hq with hc
    · cases hq
      exact gatePotentials_swap p a b hab g h hg .diagonal₀ (Or.inl rfl)
        (fun _ _ hi hj=>swap_adjacent_order hab (fun he=>hc.2 (he ▸ hi))
          (fun he=>hc.2 (he ▸ hj)))
  | diagonal₁ =>
    simp only [tileStep] at hq
    split_ifs at hq with hc
    · cases hq
      exact gatePotentials_swap p a b hab g h hg .diagonal₁ (Or.inr rfl)
        (fun _ _ hi hj=>swap_adjacent_order_lower hab (fun he=>hc.1 (he ▸ hi))
          (fun he=>hc.1 (he ▸ hj)))
  | cup =>
    simp only [tileStep] at hq
    split_ifs at hq with hc
    · cases hq
      exact gatePotentials_cup p a b hab g h hg hc.1 hc.2
  | cap =>
    simp only [tileStep] at hq
    split_ifs at hq with ha hb hn; try cases hq
    apply gatePotentials_cap_general p _ a b hab g h hg (p.partner a ha) (p.partner b hb)
      (p.partner_adj a ha) (p.partner_adj b hb) hn
    · simp [capRemove]
    · intro i j hij
      simp only [capRemove,capSplice_adj]
      exact Or.inr (Or.inr hij)
    · exact Or.inl rfl
    · intro h; cases h
  | capCup =>
    simp only [tileStep] at hq
    split_ifs at hq with ha hb hn; try cases hq
    apply gatePotentials_cap_general p _ a b hab g h hg (p.partner a ha) (p.partner b hb)
      (p.partner_adj a ha) (p.partner_adj b hb) hn
    · simp [capRemove]
    · intro i j hij
      simp only [insertCup_adj,capRemove,capSplice_adj]
      exact Or.inr (Or.inr (Or.inr (Or.inr hij)))
    · exact Or.inr rfl
    · intro _
      simp

end Pairing

 

 


namespace CompactGate
variable {V : Type*} {n : ℕ} {r : V → V → Prop} [Std.Symm r]
  {old : Fin n → V} {p q : Pairing n}

 

theorem transport_potential (hp : GraphRealizes r old p) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (g h : Fin n → ℤ)
    (hg : ∀ i,i≠a → i≠b → h i=g i)
    (hq : p.tileStep a b hab t=some q) (P : V → ℤ)
    (hP : ∀ i j,p.Adj i j → P (old j)-P (old i)=Pairing.arcTurn g i j) :
    ∃ Q : Sum V (Fin 4) → ℤ,
      (∀ i,Q (boundary old a b i)=q.turnPotential h i) ∧
      (∀ v w,r v w → Q (.inl w)-Q (.inl v)=P w-P v) ∧
      (∀ i j,t.Adj i j → Q (.inr j)-Q (.inr i)=
        Pairing.gateTurn (g a) (g b) (h a) (h b) i j) ∧
      Q (.inl (old a))=Q (.inr 0) ∧ Q (.inl (old b))=Q (.inr 1) := by
  obtain ⟨B,T,hB⟩ := Pairing.gatePotentials_of_step p q a b hab g h hg t hq
  obtain ⟨P',hP',hE⟩ := Graph.renormalize_potential hp P B
    (fun i j hij=>(hB.old_arc i j hij).trans (hP i j hij).symm)
  refine ⟨Sum.elim P' T,?_,hE,hB.tile_arc,?_,?_⟩
  · intro i
    by_cases hia : i=a
    · subst i
      simpa only [boundary_left,Sum.elim_inr] using hB.output_left
    · by_cases hib : i=b
      · subst i
        simpa only [boundary,ite_eq_right hia,ite_true,Sum.elim_inr] using hB.output_right
      · simpa only [boundary,ite_eq_right hia,ite_eq_right hib,Sum.elim_inl,hP'] using hB.outside i hia hib
  · simpa only [Sum.elim_inl,Sum.elim_inr,hP'] using hB.input_left
  · simpa only [Sum.elim_inl,Sum.elim_inr,hP'] using hB.input_right

end CompactGate

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TurnDisk
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace BoundaryInsert
variable {n m : ℕ}

lemma pairing_adj (k : ℕ) (hk : k≤n) (p : Pairing n) (t : Pairing m)
    (u v : Fin (n+m)) :
    (pairing k hk p t).Adj u v ↔ (p.map (old k hk)).Adj u v ∨
      (t.map (fresh k hk)).Adj u v := by
  simp only [Pairing.Adj,pairing,Finset.mem_union]
  tauto

@[simp] lemma pairing_old_adj (k : ℕ) (hk : k≤n) (p : Pairing n) (t : Pairing m)
    (i j : Fin n) : (pairing k hk p t).Adj (old k hk i) (old k hk j) ↔ p.Adj i j := by
  rw [pairing_adj,Pairing.map_adj_image]
  constructor
  · rintro (h|h)
    · exact h
    · obtain ⟨a,b,_,ha,_⟩ := (Pairing.map_adj _ _ _ _).mp h
      exact (disjoint k hk i a ha.symm).elim
  · exact Or.inl

@[simp] lemma pairing_fresh_adj (k : ℕ) (hk : k≤n) (p : Pairing n) (t : Pairing m)
    (i j : Fin m) : (pairing k hk p t).Adj (fresh k hk i) (fresh k hk j) ↔ t.Adj i j := by
  rw [pairing_adj,Pairing.map_adj_image]
  constructor
  · rintro (h|h)
    · obtain ⟨a,b,_,ha,_⟩ := (Pairing.map_adj _ _ _ _).mp h
      exact (disjoint k hk a i ha).elim
    · exact h
  · exact Or.inr

@[simp] lemma pairing_cross_adj (k : ℕ) (hk : k≤n) (p : Pairing n) (t : Pairing m)
    (i : Fin n) (j : Fin m) : ¬(pairing k hk p t).Adj (old k hk i) (fresh k hk j) := by
  rw [pairing_adj]
  rintro (h|h)
  · obtain ⟨a,b,_,_,hb⟩ := (Pairing.map_adj _ _ _ _).mp h
    exact disjoint k hk b j hb
  · obtain ⟨a,b,_,ha,_⟩ := (Pairing.map_adj _ _ _ _).mp h
    exact disjoint k hk i a ha.symm

@[simp] lemma pairing_old_occupied (k : ℕ) (hk : k≤n) (p : Pairing n) (t : Pairing m)
    (i : Fin n) : (pairing k hk p t).Occupied (old k hk i) ↔ p.Occupied i := by
  constructor
  · rintro ⟨j,hj⟩
    obtain ⟨j,rfl⟩|⟨j,rfl⟩ := cover k hk j
    · exact ⟨j,(pairing_old_adj k hk p t i j).mp hj⟩
    · exact (pairing_cross_adj k hk p t i j hj).elim
  · rintro ⟨j,hj⟩
    exact ⟨old k hk j,(pairing_old_adj k hk p t i j).mpr hj⟩

@[simp] lemma pairing_fresh_occupied (k : ℕ) (hk : k≤n) (p : Pairing n) (t : Pairing m)
    (i : Fin m) : (pairing k hk p t).Occupied (fresh k hk i) ↔ t.Occupied i := by
  constructor
  · rintro ⟨j,hj⟩
    obtain ⟨j,rfl⟩|⟨j,rfl⟩ := cover k hk j
    · exact (pairing_cross_adj k hk p t j i hj.symm).elim
    · exact ⟨j,(pairing_fresh_adj k hk p t i j).mp hj⟩
  · rintro ⟨j,hj⟩
    exact ⟨fresh k hk j,(pairing_fresh_adj k hk p t i j).mpr hj⟩


lemma reach_left {V W : Type*} (r : V → V → Prop) (s : W → W → Prop)
    {v : V} {w : V ⊕ W} (h : Relation.ReflTransGen (unionGraph r s) (.inl v) w) :
    ∃ u, w=.inl u ∧ Relation.ReflTransGen r v u := by
  induction h with
  | refl => exact ⟨v,rfl,.refl⟩
  | @tail y z h he ih =>
    obtain ⟨u,rfl,hu⟩:=ih
    cases z with
    | inl z => exact ⟨z,rfl,hu.tail he⟩
    | inr z => exact he.elim

lemma reach_right {V W : Type*} (r : V → V → Prop) (s : W → W → Prop)
    {v : W} {w : V ⊕ W} (h : Relation.ReflTransGen (unionGraph r s) (.inr v) w) :
    ∃ u, w=.inr u ∧ Relation.ReflTransGen s v u := by
  induction h with
  | refl => exact ⟨v,rfl,.refl⟩
  | @tail y z h he ih =>
    obtain ⟨u,rfl,hu⟩:=ih
    cases z with
    | inl z => exact he.elim
    | inr z => exact ⟨z,rfl,hu.tail he⟩

lemma boundary_injective {V W : Type*} (k : ℕ) (hk : k≤n)
    (a : Fin n → V) (b : Fin m → W) (ha : Function.Injective a) (hb : Function.Injective b) :
    Function.Injective (boundary k hk a b) := by
  intro i j hij
  obtain ⟨i,rfl⟩|⟨i,rfl⟩:=cover k hk i <;>
    obtain ⟨j,rfl⟩|⟨j,rfl⟩:=cover k hk j <;>
    simp only [boundary_old,boundary_fresh,Sum.inl.injEq,Sum.inr.injEq] at hij
  · exact congrArg _ (ha hij)
  · cases hij
  · cases hij
  · exact congrArg _ (hb hij)

lemma realizes {V W : Type*} (k : ℕ) (hk : k≤n)
    {r : V → V → Prop} {s : W → W → Prop} {a : Fin n → V} {b : Fin m → W}
    {p : Pairing n} {t : Pairing m} (hp : GraphRealizes r a p) (ht : GraphRealizes s b t) :
    GraphRealizes (unionGraph r s) (boundary k hk a b) (pairing k hk p t) := by
  constructor
  · rintro (v|v) (w|w) h
    · obtain ⟨i,hi,hr⟩:=hp.no_loop v w h
      refine ⟨old k hk i,(pairing_old_occupied k hk p t i).mpr hi,?_⟩
      rw [boundary_old]
      exact Graph.map_reach Sum.inl (fun _ _ h=>.single h) hr
    · exact h.elim
    · exact h.elim
    · obtain ⟨i,hi,hr⟩:=ht.no_loop v w h
      refine ⟨fresh k hk i,(pairing_fresh_occupied k hk p t i).mpr hi,?_⟩
      rw [boundary_fresh]
      exact Graph.map_reach Sum.inr (fun _ _ h=>.single h) hr
  · intro i j
    obtain ⟨i,rfl⟩|⟨i,rfl⟩:=cover k hk i <;>
      obtain ⟨j,rfl⟩|⟨j,rfl⟩:=cover k hk j <;>
      simp only [boundary_old,boundary_fresh]
    · rw [pairing_old_adj,(old k hk).injective.eq_iff]
      constructor
      · intro h
        obtain ⟨u,he,hu⟩:=reach_left r s h
        cases he
        exact (hp.reach i j).mp hu
      · intro h
        exact Graph.map_reach Sum.inl (fun _ _ h=>.single h) ((hp.reach i j).mpr h)
    · simp only [disjoint k hk i j,pairing_cross_adj,false_or,iff_false]
      intro h
      obtain ⟨u,he,_⟩:=reach_left r s h
      cases he
    · have hne : fresh k hk i≠old k hk j := (disjoint k hk j i).symm
      have hn : ¬(pairing k hk p t).Adj (fresh k hk i) (old k hk j) :=
        fun h=>pairing_cross_adj k hk p t j i h.symm
      simp only [hne,hn,false_or,iff_false]
      intro h
      obtain ⟨u,he,_⟩:=reach_right r s h
      cases he
    · rw [pairing_fresh_adj,(fresh k hk).injective.eq_iff]
      constructor
      · intro h
        obtain ⟨u,he,hu⟩:=reach_right r s h
        cases he
        exact (ht.reach i j).mp hu
      · intro h
        exact Graph.map_reach Sum.inr (fun _ _ h=>.single h) ((ht.reach i j).mpr h)

lemma potential {V W : Type*} (k : ℕ) (hk : k≤n)
    (a : Fin n → V) (b : Fin m → W) (p : Pairing n) (t : Pairing m)
    (g : Fin n → ℤ) (h : Fin m → ℤ) (P : V → ℤ) (Q : W → ℤ)
    (hP : ∀ i j,p.Adj i j → P (a j)-P (a i)=Pairing.arcTurn g i j)
    (hQ : ∀ i j,t.Adj i j → Q (b j)-Q (b i)=Pairing.arcTurn h i j) :
    ∀ i j,(pairing k hk p t).Adj i j →
      Sum.elim P Q (boundary k hk a b j)-Sum.elim P Q (boundary k hk a b i)=
        Pairing.arcTurn (gauge k hk g h) i j := by
  intro i j hij
  obtain ⟨i,rfl⟩|⟨i,rfl⟩:=cover k hk i <;>
    obtain ⟨j,rfl⟩|⟨j,rfl⟩:=cover k hk j
  · simp only [pairing_old_adj] at hij
    simpa only [boundary_old,Sum.elim_inl,Pairing.arcTurn,gauge_old,Pairing.turnOrder,
      (old k hk).lt_iff_lt] using hP i j hij
  · exact (pairing_cross_adj k hk p t i j hij).elim
  · exact (pairing_cross_adj k hk p t j i hij.symm).elim
  · simp only [pairing_fresh_adj] at hij
    simpa only [boundary_fresh,Sum.elim_inr,Pairing.arcTurn,gauge_fresh,Pairing.turnOrder,
      (fresh k hk).lt_iff_lt] using hQ i j hij

end BoundaryInsert

 

 


namespace GraphRealizes
variable {V : Type*} {n m : ℕ} {r : V → V → Prop} {b : Fin n → V} {p : Pairing n}

lemma restrict_boundary (hp : GraphRealizes r b p) (f : Fin m ↪o Fin n)
    (hf : ∀ i,p.Occupied i → ∃ j,f j=i) :
    GraphRealizes r (b ∘ f) (p.restrict f) := by
  constructor
  · intro v w hvw
    obtain ⟨i,hi,hr⟩:=hp.no_loop v w hvw
    obtain ⟨j,rfl⟩:=hf i hi
    obtain ⟨i,hi⟩:=hi
    obtain ⟨k,rfl⟩:=hf i ⟨f j,hi.symm⟩
    exact ⟨j,⟨k,(Pairing.restrict_adj _ _ _ _).mpr hi⟩,hr⟩
  · intro i j
    rw [Function.comp_apply,Function.comp_apply,hp.reach,Pairing.restrict_adj,f.injective.eq_iff]

end GraphRealizes

namespace BoundaryErase
variable {n : ℕ}

lemma distinct (k : ℕ) (hk : k≤n) : left k hk≠right k hk := by
  intro h
  have hh:=congrArg Fin.val h
  have he:=adjacent k hk
  omega

lemma cover (k : ℕ) (hk : k≤n) (i : Fin (n+2)) :
    (∃ j,keep k hk j=i) ∨ i=left k hk ∨ i=right k hk := by
  obtain h|⟨j,rfl⟩:=BoundaryInsert.cover (m:=2) k hk i
  · exact Or.inl h
  · fin_cases j
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

lemma occupied_cover (k : ℕ) (hk : k≤n) (p : Pairing (n+2))
    (hl : ¬p.Occupied (left k hk)) (hr : ¬p.Occupied (right k hk))
    (i : Fin (n+2)) (hi : p.Occupied i) : ∃ j,keep k hk j=i := by
  obtain h|h|h:=cover k hk i
  · exact h
  · exact (hl (h ▸ hi)).elim
  · exact (hr (h ▸ hi)).elim

lemma restrict_realizes {V : Type*} {r : V → V → Prop} {b : Fin (n+2) → V}
    (k : ℕ) (hk : k≤n) (p : Pairing (n+2)) (hp : GraphRealizes r b p)
    (hl : ¬p.Occupied (left k hk)) (hr : ¬p.Occupied (right k hk)) :
    GraphRealizes r (b ∘ keep k hk) (p.restrict (keep k hk)) :=
  hp.restrict_boundary (keep k hk) (occupied_cover k hk p hl hr)

lemma potential {V : Type*} (k : ℕ) (hk : k≤n) (b : Fin (n+2) → V)
    (p : Pairing (n+2)) (g : Fin (n+2) → ℤ) (P : V → ℤ)
    (hP : ∀ i j,p.Adj i j → P (b j)-P (b i)=Pairing.arcTurn g i j) :
    ∀ i j,(p.restrict (keep k hk)).Adj i j →
      P (b (keep k hk j))-P (b (keep k hk i))=Pairing.arcTurn (g ∘ keep k hk) i j := by
  intro i j hij
  have h:=hP (keep k hk i) (keep k hk j) ((Pairing.restrict_adj _ _ _ _).mp hij)
  simpa only [Pairing.arcTurn,Pairing.turnOrder,(keep k hk).lt_iff_lt,Function.comp_apply] using h

end BoundaryErase

namespace BoundarySew
section Wiring
variable {V : Type*} {n : ℕ} {r : V → V → Prop} [Std.Symm r]
  {old : Fin (n+2) → V}



lemma tile_no_outputs (active : Prop) : ¬(tile active).Occupied 2 ∧ ¬(tile active).Occupied 3 := by
  by_cases ha : active <;> simp [tile,ha,Tile.Occupied,Tile.Adj,Tile.edges]

lemma tile_inputs (active : Prop) : ((tile active).Occupied 0 ↔ active) ∧
    ((tile active).Occupied 1 ↔ active) := by
  by_cases ha : active <;> simp [tile,ha,Tile.Occupied,Tile.Adj,Tile.edges]

lemma output_vacant (p q : Pairing (n+2)) (k : ℕ) (hk : k≤n)
    (hq : p.tileStep (BoundaryErase.left k hk) (BoundaryErase.right k hk)
      (BoundaryErase.adjacent k hk) (tile (p.Occupied (BoundaryErase.left k hk)))=some q) :
    ¬q.Occupied (BoundaryErase.left k hk) ∧ ¬q.Occupied (BoundaryErase.right k hk) := by
  have hs := p.tileStep_support (BoundaryErase.left k hk) (BoundaryErase.right k hk)
    (BoundaryErase.adjacent k hk) (tile (p.Occupied (BoundaryErase.left k hk))) q hq
  have ht := tile_no_outputs (p.Occupied (BoundaryErase.left k hk))
  constructor
  · rw [hs]
    simpa only [Pairing.stepSupport,ite_true] using ht.1
  · rw [hs]
    simpa only [Pairing.stepSupport,ite_eq_right (BoundaryErase.distinct k hk).symm,ite_true] using ht.2

 

theorem transport (p : Pairing (n+2)) (k : ℕ) (hk : k≤n)
    (hp : GraphRealizes r old p) (hinj : Function.Injective old)
    (hc : p.Occupied (BoundaryErase.left k hk) ↔ p.Occupied (BoundaryErase.right k hk))
    (g : Fin (n+2) → ℤ) (hg : g (BoundaryErase.right k hk)=g (BoundaryErase.left k hk)-3)
    (P : V → ℤ)
    (hP : ∀ i j,p.Adj i j → P (old j)-P (old i)=Pairing.arcTurn g i j)
    (hd : Graph.DrainsBoundary
      (CompactGate.wiring r old p.Occupied (BoundaryErase.left k hk) (BoundaryErase.right k hk)
        (tile (p.Occupied (BoundaryErase.left k hk))))
      ((CompactGate.boundary old (BoundaryErase.left k hk) (BoundaryErase.right k hk)) ∘
        BoundaryErase.keep k hk)) :
    ∃ (q : Pairing n) (Q : V ⊕ Fin 4 → ℤ),
      GraphRealizes
        (CompactGate.wiring r old p.Occupied (BoundaryErase.left k hk) (BoundaryErase.right k hk)
          (tile (p.Occupied (BoundaryErase.left k hk))))
        ((CompactGate.boundary old (BoundaryErase.left k hk) (BoundaryErase.right k hk)) ∘
          BoundaryErase.keep k hk) q ∧
      (∀ i j,q.Adj i j →
        Q (.inl (old (BoundaryErase.keep k hk j)))-Q (.inl (old (BoundaryErase.keep k hk i)))=
          Pairing.arcTurn (g ∘ BoundaryErase.keep k hk) i j) ∧
      (∀ v w,r v w → Q (.inl w)-Q (.inl v)=P w-P v) ∧
      Q (.inl (old (BoundaryErase.left k hk)))=Q (.inr 0) ∧
      Q (.inl (old (BoundaryErase.right k hk)))=Q (.inr 1) ∧
      (p.Occupied (BoundaryErase.left k hk) → Q (.inr 1)=Q (.inr 0)) := by
  let a:=BoundaryErase.left k hk
  let b:=BoundaryErase.right k hk
  let t:=tile (p.Occupied a)
  have hab : a.val+1=b.val := BoundaryErase.adjacent k hk
  have hne : a≠b := BoundaryErase.distinct k hk
  have ht : CutPatch.Compatible (p.cutShape a b) t := by
    rw [p.cutShape_compatible]
    exact ⟨(tile_inputs _).1.symm,hc.symm.trans (tile_inputs _).2.symm⟩
  have hd' : Graph.DrainsBoundary (CompactGate.wiring r old p.Occupied a b t)
      (CompactGate.boundary old a b) := by
    intro v w hvw
    obtain ⟨i,hi⟩:=hd v w hvw
    exact ⟨BoundaryErase.keep k hk i,hi⟩
  obtain ⟨q,hq⟩:=graph_gate_step_exists hp a b hab t ht
    ((CompactGate.contraction hp hinj a b hne t).drains_inv hd')
  have hr : GraphRealizes (CompactGate.wiring r old p.Occupied a b t)
      (CompactGate.boundary old a b) q :=
    (CompactGate.realizes_iff hp hinj a b hne t q).mp ((graph_gate_step_iff hp a b hab t q).mpr hq).2
  obtain ⟨Q,hQ,hOld,hTile,hA,hB⟩:=CompactGate.transport_potential hp a b hab t g g
    (fun _ _ _=>rfl) hq P hP
  obtain ⟨hqa,hqb⟩:=output_vacant p q k hk hq
  refine ⟨q.restrict (BoundaryErase.keep k hk),Q,
    BoundaryErase.restrict_realizes k hk q hr hqa hqb,?_,hOld,hA,hB,?_⟩
  · intro i j hij
    have hqp : ∀ i j,q.Adj i j →
        Q (CompactGate.boundary old a b j)-Q (CompactGate.boundary old a b i)=Pairing.arcTurn g i j := by
      intro i j hij
      rw [hQ,hQ]
      exact Pairing.turnPotential_of_adj g hij
    have hh:=BoundaryErase.potential k hk (CompactGate.boundary old a b) q g Q hqp i j hij
    simpa only [CompactGate.boundary,a,b,ite_eq_right (BoundaryErase.keep_ne_left k hk i),
      ite_eq_right (BoundaryErase.keep_ne_right k hk i),ite_eq_right (BoundaryErase.keep_ne_left k hk j),
      ite_eq_right (BoundaryErase.keep_ne_right k hk j)] using hh
  · intro ha
    have habt : t.Adj 0 1 := by simp [t,a,tile,ha,Tile.Adj,Tile.edges]
    have hh:=hTile 0 1 habt
    change Q (.inr 1)-Q (.inr 0)=g b-g a+3 at hh
    change g b=g a-3 at hg
    omega

end Wiring

 

 


variable {V : Type*} {n : ℕ}


variable {r : V → V → Prop} [Std.Symm r] {old : Fin (n+2) → V} {p : Pairing (n+2)}


theorem transport_direct (p : Pairing (n+2)) (k : ℕ) (hk : k≤n)
    (hp : GraphRealizes r old p) (hinj : Function.Injective old)
    (hc : p.Occupied (BoundaryErase.left k hk) ↔ p.Occupied (BoundaryErase.right k hk))
    (g : Fin (n+2) → ℤ) (hg : g (BoundaryErase.right k hk)=g (BoundaryErase.left k hk)-3)
    (P : V → ℤ)
    (hP : ∀ i j,p.Adj i j → P (old j)-P (old i)=Pairing.arcTurn g i j)
    (hd : Graph.DrainsBoundary
      (graph r (old (BoundaryErase.left k hk)) (old (BoundaryErase.right k hk))
        (p.Occupied (BoundaryErase.left k hk))) (old ∘ BoundaryErase.keep k hk)) :
    ∃ (q : Pairing n) (Q : V → ℤ),
      GraphRealizes
        (graph r (old (BoundaryErase.left k hk)) (old (BoundaryErase.right k hk))
          (p.Occupied (BoundaryErase.left k hk))) (old ∘ BoundaryErase.keep k hk) q ∧
      (∀ i j,q.Adj i j → Q (old (BoundaryErase.keep k hk j))-Q (old (BoundaryErase.keep k hk i))=
        Pairing.arcTurn (g ∘ BoundaryErase.keep k hk) i j) ∧
      (∀ v w,r v w → Q w-Q v=P w-P v) ∧
      (p.Occupied (BoundaryErase.left k hk) → Q (old (BoundaryErase.right k hk))=Q (old (BoundaryErase.left k hk))) := by
  let e:=equivalence k hk hp hinj hc
  obtain ⟨q,Q,hq,hArc,hOld,ha,hb,hab⟩:=transport p k hk hp hinj hc g hg P hP (e.symm.drains hd)
  refine ⟨q,Q ∘ Sum.inl,e.realizes hq,hArc,hOld,?_⟩
  intro hi
  change Q (.inl (old (BoundaryErase.right k hk)))=Q (.inl (old (BoundaryErase.left k hk)))
  rw [ha,hb,hab hi]

end BoundarySew
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TurnShelling
attribute [-instance] _root_.OAI.CriticalStrip.Diagram.TurnNetwork.instSymmNodeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace Graph

 
lemma reach_before_sewing {V I : Type*} {r s : V → V → Prop} (b : I → V)
    (hs : ∀ v w,s v w → r v w ∨ ∃ i,v=b i) {v w : V}
    (h : Relation.ReflTransGen s v w) :
    (∃ i,Relation.ReflTransGen r v (b i)) ∨ Relation.ReflTransGen r v w := by
  induction h with
  | refl => exact Or.inr .refl
  | @tail y z h e ih =>
    rcases ih with h|h
    · exact Or.inl h
    · rcases hs _ _ e with he|⟨i,rfl⟩
      · exact Or.inr (h.tail he)
      · exact Or.inl ⟨i,h⟩

lemma drains_before_sewing {V I J : Type*} {r s : V → V → Prop}
    (b : I → V) (c : J → V)
    (hrs : ∀ v w,r v w → s v w)
    (hs : ∀ v w,s v w → r v w ∨ ∃ i,v=b i)
    (hc : ∀ j,∃ i,c j=b i) (hd : DrainsBoundary s c) : DrainsBoundary r b := by
  intro v w hvw
  obtain ⟨j,hj⟩:=hd v w (hrs _ _ hvw)
  rcases reach_before_sewing b hs hj with h|h
  · exact h
  · obtain ⟨i,hi⟩:=hc j
    exact ⟨i,hi ▸ h⟩

end Graph

namespace BoundaryInsert
lemma drains_old {V W : Type*} {n m : ℕ} {r : V → V → Prop} {s : W → W → Prop}
    (a : Fin n → V) (b : Fin m → W) (k : ℕ) (hk : k≤n)
    (hd : Graph.DrainsBoundary (unionGraph r s) (boundary k hk a b)) :
    Graph.DrainsBoundary r a := by
  intro v w hvw
  obtain ⟨i,hi⟩:=hd (.inl v) (.inl w) hvw
  obtain ⟨j,rfl⟩|⟨j,rfl⟩:=cover k hk i
  · rw [boundary_old] at hi
    obtain ⟨x,hx,h⟩:=reach_left r s hi
    cases hx
    exact ⟨j,h⟩
  · rw [boundary_fresh] at hi
    obtain ⟨x,hx,_⟩:=reach_left r s hi
    cases hx
lemma drains_fresh {V W : Type*} {n m : ℕ} {r : V → V → Prop} {s : W → W → Prop}
    (a : Fin n → V) (b : Fin m → W) (k : ℕ) (hk : k≤n)
    (hd : Graph.DrainsBoundary (unionGraph r s) (boundary k hk a b)) :
    Graph.DrainsBoundary s b := by
  intro v w hvw
  obtain ⟨i,hi⟩:=hd (.inr v) (.inr w) hvw
  obtain ⟨j,rfl⟩|⟨j,rfl⟩:=cover k hk i
  · rw [boundary_old] at hi
    obtain ⟨x,hx,_⟩:=reach_right r s hi
    cases hx
  · rw [boundary_fresh] at hi
    obtain ⟨x,hx,h⟩:=reach_right r s hi
    cases hx
    exact ⟨j,h⟩

end BoundaryInsert



namespace TurnDisk

variable {boundarySize : ℕ}

lemma boundary_injective (D : TurnDisk boundarySize) : Function.Injective D.boundary := by
  induction D with
  | atom p g => exact Function.injective_id
  | insert D k hk p g ih => exact BoundaryInsert.boundary_injective k hk _ _ ih Function.injective_id
  | attach D E k hk ih ihE => exact BoundaryInsert.boundary_injective k hk _ _ ih ihE
  | sew D k hk ih => exact ih.comp (BoundaryErase.keep k hk).injective

 

theorem potential (D : TurnDisk boundarySize) (hc : D.Compatible)
    (hd : Graph.DrainsBoundary D.wiring D.boundary) :
    ∃ (p : Pairing boundarySize) (P : D.Vertex → ℤ),
      GraphRealizes D.wiring D.boundary p ∧
      (∀ i j,p.Adj i j → P (D.boundary j)-P (D.boundary i)=Pairing.arcTurn D.gauge i j) ∧
      ∀ v w,D.wiring v w → P w-P v=D.edgeTurn v w := by
  induction D with
  | atom p g => exact ⟨p,p.turnPotential g,p.graphRealizes,
      fun _ _ h=>Pairing.turnPotential_of_adj g h,fun _ _ h=>Pairing.turnPotential_of_adj g h⟩
  | @insert n m D k hk t g ih =>
    obtain ⟨p,P,hp,ha,he⟩:=ih hc
      (BoundaryInsert.drains_old D.boundary id k hk hd)
    refine ⟨BoundaryInsert.pairing k hk p t,Sum.elim P (t.turnPotential g),
      BoundaryInsert.realizes k hk hp t.graphRealizes,
      BoundaryInsert.potential k hk _ _ p t D.gauge g P (t.turnPotential g) ha
        (fun _ _ h=>Pairing.turnPotential_of_adj g h),?_⟩
    rintro (v|v) (w|w) hvw
    · exact he _ _ hvw
    · exact hvw.elim
    · exact hvw.elim
    · exact Pairing.turnPotential_of_adj g hvw
  | @attach n m D E k hk ih ihE =>
    obtain ⟨p,P,hp,ha,he⟩:=ih hc.1
      (BoundaryInsert.drains_old D.boundary E.boundary k hk hd)
    obtain ⟨t,Q,ht,hb,hf⟩:=ihE hc.2
      (BoundaryInsert.drains_fresh D.boundary E.boundary k hk hd)
    refine ⟨BoundaryInsert.pairing k hk p t,Sum.elim P Q,
      BoundaryInsert.realizes k hk hp ht,
      BoundaryInsert.potential k hk _ _ p t D.gauge E.gauge P Q ha hb,?_⟩
    rintro (v|v) (w|w) hvw
    · exact he _ _ hvw
    · exact hvw.elim
    · exact hvw.elim
    · exact hf _ _ hvw
  | @sew n D k hk ih =>
    obtain ⟨hc,hmatch,hg⟩:=hc
    have hdold : Graph.DrainsBoundary D.wiring D.boundary := by
      apply Graph.drains_before_sewing D.boundary _ (s:=(D.sew k hk).wiring)
        (fun _ _ h=>Or.inl h) ?_ (fun j=>⟨BoundaryErase.keep k hk j,rfl⟩) hd
      intro v w hvw
      change D.wiring v w ∨ (_ ∧ _) at hvw
      rcases hvw with h|⟨_,h⟩
      · exact Or.inl h
      · rcases h with ⟨rfl,_⟩|⟨rfl,_⟩
        · exact Or.inr ⟨BoundaryErase.left k hk,rfl⟩
        · exact Or.inr ⟨BoundaryErase.right k hk,rfl⟩
    obtain ⟨p,P,hp,ha,he⟩:=ih hc hdold
    have hpused (i : Fin (n+2)) :
        p.Occupied i ↔ Graph.Used D.wiring (D.boundary i) :=
      (hp.boundary_used_iff D.boundary_injective i).symm
    have hm : p.Occupied (BoundaryErase.left k hk) ↔ p.Occupied (BoundaryErase.right k hk) :=
      (hpused _).trans (hmatch.trans (hpused _).symm)
    have hgraph : BoundarySew.graph D.wiring (D.boundary (BoundaryErase.left k hk))
        (D.boundary (BoundaryErase.right k hk)) (p.Occupied (BoundaryErase.left k hk))=
        (D.sew k hk).wiring := by
      simp only [wiring,hpused]
      rfl
    obtain ⟨q,Q,hq,hArc,hOld,hWire⟩:=BoundarySew.transport_direct p k hk hp D.boundary_injective
      hm D.gauge hg P ha (by rwa [hgraph])
    refine ⟨q,Q,by rwa [hgraph] at hq,hArc,?_⟩
    intro v w hvw
    change Q w-Q v=if D.wiring v w then D.edgeTurn v w else 0
    by_cases hv : D.wiring v w
    · rw [ite_eq_left hv,hOld v w hv,he v w hv]
    · rw [ite_eq_right hv]
      change D.wiring v w ∨ (_ ∧ _) at hvw
      obtain ⟨hu,hw⟩:=hvw.resolve_left hv
      have hh:=hWire ((hpused _).mpr hu)
      rcases hw with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> omega

end TurnDisk
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TurnWideGate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace BoundaryInsert
variable {n m : ℕ}

lemma boundary_before {V W : Type*} (k : ℕ) (hk : k≤n) (a : Fin n → V)
    (b : Fin m → W) (i : Fin (n+m)) (hi : i.val<k) :
    boundary k hk a b i=.inl (a ⟨i.val,by omega⟩) := by
  have he : old (m:=m) k hk ⟨i.val,by omega⟩=i := by
    apply Fin.ext
    change (if i.val<k then i.val else i.val+m)=i.val
    simp only [ite_eq_left hi]
  exact (congrArg (boundary k hk a b) he).symm.trans (boundary_old k hk a b _)

lemma boundary_between {V W : Type*} (k : ℕ) (hk : k≤n) (a : Fin n → V)
    (b : Fin m → W) (i : Fin (n+m)) (hl : k≤ i.val) (hr : i.val<k+m) :
    boundary k hk a b i=.inr (b ⟨i.val-k,by omega⟩) := by
  have he : fresh (n:=n) k hk ⟨i.val-k,by omega⟩=i := by
    apply Fin.ext
    change k+(i.val-k)=i.val
    omega
  exact (congrArg (boundary k hk a b) he).symm.trans (boundary_fresh k hk a b _)

lemma boundary_after {V W : Type*} (k : ℕ) (hk : k≤n) (a : Fin n → V)
    (b : Fin m → W) (i : Fin (n+m)) (hi : k+m≤ i.val) :
    boundary k hk a b i=.inl (a ⟨i.val-m,by omega⟩) := by
  have he : old (m:=m) k hk ⟨i.val-m,by omega⟩=i := by
    apply Fin.ext
    change (if i.val-m<k then i.val-m else i.val-m+m)=i.val
    rw [ite_eq_right (by omega)]
    omega
  exact (congrArg (boundary k hk a b) he).symm.trans (boundary_old k hk a b _)

lemma used_left {V W : Type*} (r : V → V → Prop) (s : W → W → Prop) (v : V) :
    Graph.Used (unionGraph r s) (.inl v) ↔ Graph.Used r v := by
  constructor
  · rintro ⟨w,hw⟩
    cases w with
    | inl w => exact ⟨w,hw⟩
    | inr w => exact hw.elim
  · rintro ⟨w,hw⟩
    exact ⟨.inl w,hw⟩

lemma used_right {V W : Type*} (r : V → V → Prop) (s : W → W → Prop) (v : W) :
    Graph.Used (unionGraph r s) (.inr v) ↔ Graph.Used s v := by
  constructor
  · rintro ⟨w,hw⟩
    cases w with
    | inl w => exact hw.elim
    | inr w => exact ⟨w,hw⟩
  · rintro ⟨w,hw⟩
    exact ⟨.inr w,hw⟩
end BoundaryInsert

namespace BoundarySew
lemma used_iff {V : Type*} (r : V → V → Prop) (a b : V) (active : Prop)
    (ha : active → Graph.Used r a) (hb : active → Graph.Used r b) (v : V) :
    Graph.Used (graph r a b active) v ↔ Graph.Used r v := by
  constructor
  · rintro ⟨w,hw|⟨ht,hw⟩⟩
    · exact ⟨w,hw⟩
    · rcases hw with ⟨rfl,_⟩|⟨rfl,_⟩
      · exact ha ht
      · exact hb ht
  · rintro ⟨w,hw⟩
    exact ⟨w,Or.inl hw⟩
end BoundarySew

namespace TurnDisk

lemma sew_used {n : ℕ} (D : TurnDisk (n+2)) (k : ℕ) (hk : k≤n)
    (hc : Graph.Used D.wiring (D.boundary (BoundaryErase.left k hk)) ↔
      Graph.Used D.wiring (D.boundary (BoundaryErase.right k hk))) (v : D.Vertex) :
    Graph.Used (D.sew k hk).wiring v ↔ Graph.Used D.wiring v :=
  BoundarySew.used_iff _ _ _ _ (fun h=>h) hc.mp v



namespace Gate4

lemma finite_four_or (A : Prop) (f : Fin 4 → Prop) :
    ((((A ∨ f 3) ∨ f 2) ∨ f 1) ∨ f 0) ↔ A ∨ ∃ i,f i := by
  constructor
  · rintro ((((h|h)|h)|h)|h)
    · exact Or.inl h
    · exact Or.inr ⟨3,h⟩
    · exact Or.inr ⟨2,h⟩
    · exact Or.inr ⟨1,h⟩
    · exact Or.inr ⟨0,h⟩
  · rintro (h|⟨i,h⟩)
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · fin_cases i
      · exact Or.inr h
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inl (Or.inl (Or.inr h)))

variable {n : ℕ} (D : TurnDisk n) (k : ℕ) (hk : k+4≤n) (E : TurnDisk 8)

lemma stage1_left : (stage0 D k hk E).boundary (BoundaryErase.left (k+3) (by omega))=
    .inl (D.boundary (slot k hk 3)) := by
  apply (BoundaryInsert.boundary_before _ _ _ _ _ (by change k+3+0<k+4; omega)).trans
  rfl

lemma stage1_right : (stage0 D k hk E).boundary (BoundaryErase.right (k+3) (by omega))=
    .inr (E.boundary (input 3)) := by
  rw [boundary,BoundaryInsert.boundary_between _ _ _ _ _ (by change k+4≤k+3+1; omega)
    (by change k+3+1<k+4+8; omega)]
  apply congrArg (Sum.inr ∘ E.boundary)
  apply Fin.ext
  change (k+3+1)-(k+4)=3-3
  omega

lemma stage2_left : (stage1 D k hk E).boundary (BoundaryErase.left (k+2) (by omega))=
    .inl (D.boundary (slot k hk 2)) := by
  have hi : BoundaryErase.keep (k+3) (by omega) (BoundaryErase.left (k+2) (by omega))=
      (⟨k+2,by omega⟩ : Fin (n+8)) := by
    apply Fin.ext
    change (if k+2+0<k+3 then k+2+0 else k+2+0+2)=k+2
    rw [ite_eq_left (by omega)]
  change (stage0 D k hk E).boundary (BoundaryErase.keep (k+3) _ _)=_
  rw [hi]
  apply (BoundaryInsert.boundary_before _ _ _ _ _ (by change k+2<k+4; omega)).trans
  rfl

lemma stage2_right : (stage1 D k hk E).boundary (BoundaryErase.right (k+2) (by omega))=
    .inr (E.boundary (input 2)) := by
  have hi : BoundaryErase.keep (k+3) (by omega) (BoundaryErase.right (k+2) (by omega))=
      (⟨k+5,by omega⟩ : Fin (n+8)) := by
    apply Fin.ext
    change (if k+2+1<k+3 then k+2+1 else k+2+1+2)=k+5
    rw [ite_eq_right (by omega)]
  change (stage0 D k hk E).boundary (BoundaryErase.keep (k+3) _ _)=_
  rw [hi,boundary,BoundaryInsert.boundary_between _ _ _ _ _ (by change k+4≤k+5; omega)
    (by change k+5<k+4+8; omega)]
  apply congrArg (Sum.inr ∘ E.boundary)
  apply Fin.ext
  change (k+5)-(k+4)=3-2
  omega

lemma stage3_left : (stage2 D k hk E).boundary (BoundaryErase.left (k+1) (by omega))=
    .inl (D.boundary (slot k hk 1)) := by
  have hi : BoundaryErase.keep (k+3) (by omega)
      (BoundaryErase.keep (k+2) (by omega) (BoundaryErase.left (k+1) (by omega)))=
      (⟨k+1,by omega⟩ : Fin (n+8)) := by
    apply Fin.ext
    change skip (k+3) (skip (k+2) (k+1))=k+1
    simp (disch := omega) only [skip,ite_eq_left]
  change (stage0 D k hk E).boundary (BoundaryErase.keep (k+3) _ (BoundaryErase.keep (k+2) _ _))=_
  rw [hi]
  apply (BoundaryInsert.boundary_before _ _ _ _ _ (by change k+1<k+4; omega)).trans
  rfl

lemma stage3_right : (stage2 D k hk E).boundary (BoundaryErase.right (k+1) (by omega))=
    .inr (E.boundary (input 1)) := by
  have hi : BoundaryErase.keep (k+3) (by omega)
      (BoundaryErase.keep (k+2) (by omega) (BoundaryErase.right (k+1) (by omega)))=
      (⟨k+6,by omega⟩ : Fin (n+8)) := by
    apply Fin.ext
    change skip (k+3) (skip (k+2) (k+2))=k+6
    simp (disch := omega) only [skip,ite_eq_left,ite_eq_right]
  change (stage0 D k hk E).boundary (BoundaryErase.keep (k+3) _ (BoundaryErase.keep (k+2) _ _))=_
  rw [hi,boundary,BoundaryInsert.boundary_between _ _ _ _ _ (by change k+4≤k+6; omega)
    (by change k+6<k+4+8; omega)]
  apply congrArg (Sum.inr ∘ E.boundary)
  apply Fin.ext
  change (k+6)-(k+4)=3-1
  omega

lemma stage4_left : (stage3 D k hk E).boundary (BoundaryErase.left k (by omega))=
    .inl (D.boundary (slot k hk 0)) := by
  have hi : BoundaryErase.keep (k+3) (by omega) (BoundaryErase.keep (k+2) (by omega)
      (BoundaryErase.keep (k+1) (by omega) (BoundaryErase.left k (by omega))))=
      (⟨k,by omega⟩ : Fin (n+8)) := by
    apply Fin.ext
    change skip (k+3) (skip (k+2) (skip (k+1) k))=k
    simp (disch := omega) only [skip,ite_eq_left]
  change (stage0 D k hk E).boundary
    (BoundaryErase.keep (k+3) _ (BoundaryErase.keep (k+2) _ (BoundaryErase.keep (k+1) _ _)))=_
  rw [hi]
  apply (BoundaryInsert.boundary_before _ _ _ _ _ (by change k<k+4; omega)).trans
  rfl

lemma stage4_right : (stage3 D k hk E).boundary (BoundaryErase.right k (by omega))=
    .inr (E.boundary (input 0)) := by
  have hi : BoundaryErase.keep (k+3) (by omega) (BoundaryErase.keep (k+2) (by omega)
      (BoundaryErase.keep (k+1) (by omega) (BoundaryErase.right k (by omega))))=
      (⟨k+7,by omega⟩ : Fin (n+8)) := by
    apply Fin.ext
    change skip (k+3) (skip (k+2) (skip (k+1) (k+1)))=k+7
    simp (disch := omega) only [skip,ite_eq_left,ite_eq_right]
  change (stage0 D k hk E).boundary
    (BoundaryErase.keep (k+3) _ (BoundaryErase.keep (k+2) _ (BoundaryErase.keep (k+1) _ _)))=_
  rw [hi,boundary,BoundaryInsert.boundary_between _ _ _ _ _ (by change k+4≤k+7; omega)
    (by change k+7<k+4+8; omega)]
  apply congrArg (Sum.inr ∘ E.boundary)
  apply Fin.ext
  change (k+7)-(k+4)=3-0
  omega

lemma boundary_slot (i : Fin 4) :
    (D.gate4 k hk E).boundary (slot k hk i)=.inr (E.boundary (output i)) := by
  have hi : BoundaryErase.keep (k+3) (by omega) (BoundaryErase.keep (k+2) (by omega)
      (BoundaryErase.keep (k+1) (by omega) (BoundaryErase.keep k (by omega) (slot k hk i))))=
      (⟨k+i.val+8,by omega⟩ : Fin (n+8)) := by
    apply Fin.ext
    change skip (k+3) (skip (k+2) (skip (k+1) (skip k (k+i.val))))=k+i.val+8
    simp (disch := omega) only [skip,ite_eq_right]
  change (stage0 D k hk E).boundary
    (BoundaryErase.keep (k+3) _ (BoundaryErase.keep (k+2) _
      (BoundaryErase.keep (k+1) _ (BoundaryErase.keep k _ _))))=_
  rw [hi,boundary,BoundaryInsert.boundary_between _ _ _ _ _ (by change k+4≤k+i.val+8; omega)
    (by change k+i.val+8<k+4+8; omega)]
  apply congrArg (Sum.inr ∘ E.boundary)
  apply Fin.ext
  change (k+i.val+8)-(k+4)=4+i.val
  omega

lemma boundary_outside (i : Fin n) (hi : i.val<k ∨ k+4≤ i.val) :
    (D.gate4 k hk E).boundary i=.inl (D.boundary i) := by
  rcases hi with hi|hi
  · have he : BoundaryErase.keep (k+3) (by omega) (BoundaryErase.keep (k+2) (by omega)
        (BoundaryErase.keep (k+1) (by omega) (BoundaryErase.keep k (by omega) i)))=
        (⟨i.val,by omega⟩ : Fin (n+8)) := by
      apply Fin.ext
      change skip (k+3) (skip (k+2) (skip (k+1) (skip k i.val)))=i.val
      simp (disch := omega) only [skip,ite_eq_left]
    change (stage0 D k hk E).boundary
      (BoundaryErase.keep (k+3) _ (BoundaryErase.keep (k+2) _
        (BoundaryErase.keep (k+1) _ (BoundaryErase.keep k _ _))))=_
    rw [he]
    exact BoundaryInsert.boundary_before _ _ _ _ _ (by change i.val<k+4; omega)
  · have he : BoundaryErase.keep (k+3) (by omega) (BoundaryErase.keep (k+2) (by omega)
        (BoundaryErase.keep (k+1) (by omega) (BoundaryErase.keep k (by omega) i)))=
        (⟨i.val+8,by omega⟩ : Fin (n+8)) := by
      apply Fin.ext
      change skip (k+3) (skip (k+2) (skip (k+1) (skip k i.val)))=i.val+8
      simp (disch := omega) only [skip,ite_eq_right]
    change (stage0 D k hk E).boundary
      (BoundaryErase.keep (k+3) _ (BoundaryErase.keep (k+2) _
        (BoundaryErase.keep (k+1) _ (BoundaryErase.keep k _ _))))=_
    rw [he,boundary,BoundaryInsert.boundary_after _ _ _ _ _ (by change k+4+8≤ i.val+8; omega)]
    rfl

lemma gauge_outside (i : Fin n) (hi : i.val<k ∨ k+4≤ i.val) :
    (D.gate4 k hk E).gauge i=D.gauge i := by
  rw [←vertexGauge_boundary,boundary_outside D k hk E i hi]
  exact vertexGauge_boundary D i

variable (hm : ∀ i : Fin 4, Graph.Used D.wiring (D.boundary (slot k hk i)) ↔ Graph.Used E.wiring (E.boundary (input i)))

include hm

lemma match1 : Graph.Used (stage0 D k hk E).wiring
      ((stage0 D k hk E).boundary (BoundaryErase.left (k+3) (by omega))) ↔
    Graph.Used (stage0 D k hk E).wiring
      ((stage0 D k hk E).boundary (BoundaryErase.right (k+3) (by omega))) := by
  rw [stage1_left,stage1_right]
  change Graph.Used (BoundaryInsert.unionGraph D.wiring E.wiring) (.inl _) ↔
    Graph.Used (BoundaryInsert.unionGraph D.wiring E.wiring) (.inr _)
  rw [BoundaryInsert.used_left,BoundaryInsert.used_right]
  exact hm 3

lemma stage1_used (v : D.Vertex ⊕ E.Vertex) :
    Graph.Used (stage1 D k hk E).wiring v ↔ Graph.Used (stage0 D k hk E).wiring v :=
  sew_used _ _ _ (match1 D k hk E hm) v

lemma match2 : Graph.Used (stage1 D k hk E).wiring
      ((stage1 D k hk E).boundary (BoundaryErase.left (k+2) (by omega))) ↔
    Graph.Used (stage1 D k hk E).wiring
      ((stage1 D k hk E).boundary (BoundaryErase.right (k+2) (by omega))) := by
  rw [stage2_left,stage2_right,stage1_used D k hk E hm,stage1_used D k hk E hm]
  change Graph.Used (BoundaryInsert.unionGraph D.wiring E.wiring) (.inl _) ↔
    Graph.Used (BoundaryInsert.unionGraph D.wiring E.wiring) (.inr _)
  rw [BoundaryInsert.used_left,BoundaryInsert.used_right]
  exact hm 2

lemma stage2_used (v : D.Vertex ⊕ E.Vertex) :
    Graph.Used (stage2 D k hk E).wiring v ↔ Graph.Used (stage0 D k hk E).wiring v :=
  (sew_used _ _ _ (match2 D k hk E hm) v).trans (stage1_used D k hk E hm v)

lemma match3 : Graph.Used (stage2 D k hk E).wiring
      ((stage2 D k hk E).boundary (BoundaryErase.left (k+1) (by omega))) ↔
    Graph.Used (stage2 D k hk E).wiring
      ((stage2 D k hk E).boundary (BoundaryErase.right (k+1) (by omega))) := by
  rw [stage3_left,stage3_right,stage2_used D k hk E hm,stage2_used D k hk E hm]
  change Graph.Used (BoundaryInsert.unionGraph D.wiring E.wiring) (.inl _) ↔
    Graph.Used (BoundaryInsert.unionGraph D.wiring E.wiring) (.inr _)
  rw [BoundaryInsert.used_left,BoundaryInsert.used_right]
  exact hm 1

lemma stage3_used (v : D.Vertex ⊕ E.Vertex) :
    Graph.Used (stage3 D k hk E).wiring v ↔ Graph.Used (stage0 D k hk E).wiring v :=
  (sew_used _ _ _ (match3 D k hk E hm) v).trans (stage2_used D k hk E hm v)

lemma match4 : Graph.Used (stage3 D k hk E).wiring
      ((stage3 D k hk E).boundary (BoundaryErase.left k (by omega))) ↔
    Graph.Used (stage3 D k hk E).wiring
      ((stage3 D k hk E).boundary (BoundaryErase.right k (by omega))) := by
  rw [stage4_left,stage4_right,stage3_used D k hk E hm,stage3_used D k hk E hm]
  change Graph.Used (BoundaryInsert.unionGraph D.wiring E.wiring) (.inl _) ↔
    Graph.Used (BoundaryInsert.unionGraph D.wiring E.wiring) (.inr _)
  rw [BoundaryInsert.used_left,BoundaryInsert.used_right]
  exact hm 0

lemma used (v : D.Vertex ⊕ E.Vertex) :
    Graph.Used (D.gate4 k hk E).wiring v ↔ Graph.Used (stage0 D k hk E).wiring v :=
  (sew_used _ _ _ (match4 D k hk E hm) v).trans (stage3_used D k hk E hm v)

lemma compatible (hc : D.Compatible) (hE : E.Compatible)
    (hg : ∀ i : Fin 4,E.gauge (input i)=D.gauge (slot k hk i)-3) :
    (D.gate4 k hk E).Compatible := by
  have hg1 : (stage0 D k hk E).gauge (BoundaryErase.right (k+3) (by omega))=
      (stage0 D k hk E).gauge (BoundaryErase.left (k+3) (by omega))-3 := by
    rw [←vertexGauge_boundary,←vertexGauge_boundary,stage1_right,stage1_left]
    change E.vertexGauge (E.boundary (input 3))=D.vertexGauge (D.boundary (slot k hk 3))-3
    rw [vertexGauge_boundary,vertexGauge_boundary]
    exact hg 3
  have hg2 : (stage1 D k hk E).gauge (BoundaryErase.right (k+2) (by omega))=
      (stage1 D k hk E).gauge (BoundaryErase.left (k+2) (by omega))-3 := by
    rw [←vertexGauge_boundary,←vertexGauge_boundary,stage2_right,stage2_left]
    change E.vertexGauge (E.boundary (input 2))=D.vertexGauge (D.boundary (slot k hk 2))-3
    rw [vertexGauge_boundary,vertexGauge_boundary]
    exact hg 2
  have hg3 : (stage2 D k hk E).gauge (BoundaryErase.right (k+1) (by omega))=
      (stage2 D k hk E).gauge (BoundaryErase.left (k+1) (by omega))-3 := by
    rw [←vertexGauge_boundary,←vertexGauge_boundary,stage3_right,stage3_left]
    change E.vertexGauge (E.boundary (input 1))=D.vertexGauge (D.boundary (slot k hk 1))-3
    rw [vertexGauge_boundary,vertexGauge_boundary]
    exact hg 1
  have hg4 : (stage3 D k hk E).gauge (BoundaryErase.right k (by omega))=
      (stage3 D k hk E).gauge (BoundaryErase.left k (by omega))-3 := by
    rw [←vertexGauge_boundary,←vertexGauge_boundary,stage4_right,stage4_left]
    change E.vertexGauge (E.boundary (input 0))=D.vertexGauge (D.boundary (slot k hk 0))-3
    rw [vertexGauge_boundary,vertexGauge_boundary]
    exact hg 0
  exact ⟨⟨⟨⟨⟨hc,hE⟩,match1 D k hk E hm,hg1⟩,match2 D k hk E hm,hg2⟩,
    match3 D k hk E hm,hg3⟩,match4 D k hk E hm,hg4⟩


lemma wiring (v w : D.Vertex ⊕ E.Vertex) :
    (D.gate4 k hk E).wiring v w ↔
      BoundaryInsert.unionGraph D.wiring E.wiring v w ∨ wire D k hk E v w := by
  have h1 : Graph.Used (stage0 D k hk E).wiring (.inl (D.boundary (slot k hk 3))) ↔
      Graph.Used E.wiring (E.boundary (input 3)) := (BoundaryInsert.used_left _ _ _).trans (hm 3)
  have h2 : Graph.Used (stage1 D k hk E).wiring (.inl (D.boundary (slot k hk 2))) ↔
      Graph.Used E.wiring (E.boundary (input 2)) := (stage1_used D k hk E hm _).trans
        ((BoundaryInsert.used_left _ _ _).trans (hm 2))
  have h3 : Graph.Used (stage2 D k hk E).wiring (.inl (D.boundary (slot k hk 1))) ↔
      Graph.Used E.wiring (E.boundary (input 1)) := (stage2_used D k hk E hm _).trans
        ((BoundaryInsert.used_left _ _ _).trans (hm 1))
  have h4 : Graph.Used (stage3 D k hk E).wiring (.inl (D.boundary (slot k hk 0))) ↔
      Graph.Used E.wiring (E.boundary (input 0)) := (stage3_used D k hk E hm _).trans
        ((BoundaryInsert.used_left _ _ _).trans (hm 0))
  change BoundarySew.graph (stage3 D k hk E).wiring _ _ _ v w ↔ _
  simp only [BoundarySew.graph]
  rw [stage4_left,stage4_right,h4]
  change (BoundarySew.graph (stage2 D k hk E).wiring _ _ _ v w ∨ _) ↔ _
  simp only [BoundarySew.graph]
  rw [stage3_left,stage3_right,h3]
  change ((BoundarySew.graph (stage1 D k hk E).wiring _ _ _ v w ∨ _) ∨ _) ↔ _
  simp only [BoundarySew.graph]
  rw [stage2_left,stage2_right,h2]
  change (((BoundarySew.graph (stage0 D k hk E).wiring _ _ _ v w ∨ _) ∨ _) ∨ _) ↔ _
  simp only [BoundarySew.graph]
  rw [stage1_left,stage1_right,h1]
  exact finite_four_or (BoundaryInsert.unionGraph D.wiring E.wiring v w) (fun i=>
    Graph.Used E.wiring (E.boundary (input i)) ∧ ((v=.inl (D.boundary (slot k hk i)) ∧ w=.inr (E.boundary (input i))) ∨
      (v=.inr (E.boundary (input i)) ∧ w=.inl (D.boundary (slot k hk i)))))

end Gate4
end TurnDisk
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TurnRhombus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace TurnDisk
lemma sew_edgeTurn {n : ℕ} (D : TurnDisk (n+2)) (k : ℕ) (hk : k≤n)
    {v w : D.Vertex} (h : D.wiring v w) : (D.sew k hk).edgeTurn v w=D.edgeTurn v w := by
  change (if D.wiring v w then _ else _)=_
  rw [ite_eq_left h]
lemma sew_zeroTurn {n : ℕ} (D : TurnDisk (n+2)) (k : ℕ) (hk : k≤n)
    {v w : D.Vertex} (h : D.edgeTurn v w=0) : (D.sew k hk).edgeTurn v w=0 := by
  change (if D.wiring v w then _ else _)=_
  split_ifs <;> first | exact h | rfl

namespace Gate4
variable {n : ℕ} (D : TurnDisk n) (k : ℕ) (hk : k+4≤n) (E : TurnDisk 8)
lemma old_edge {v w : D.Vertex} (h : D.wiring v w) :
    (D.gate4 k hk E).wiring (.inl v) (.inl w) :=
  Or.inl (Or.inl (Or.inl (Or.inl h)))
lemma new_edge {v w : E.Vertex} (h : E.wiring v w) :
    (D.gate4 k hk E).wiring (.inr v) (.inr w) :=
  Or.inl (Or.inl (Or.inl (Or.inl h)))
lemma old_edgeTurn {v w : D.Vertex} (h : D.wiring v w) :
    (D.gate4 k hk E).edgeTurn (.inl v) (.inl w)=D.edgeTurn v w := by
  change (((stage0 D k hk E).sew _ _).sew _ _ |>.sew _ _ |>.sew _ _).edgeTurn _ _=_
  rw [sew_edgeTurn (stage3 D k hk E) k (by omega) (v:=Sum.inl v) (w:=Sum.inl w) (Or.inl (Or.inl (Or.inl h))),
    sew_edgeTurn (stage2 D k hk E) (k+1) (by omega) (v:=Sum.inl v) (w:=Sum.inl w) (Or.inl (Or.inl h)),
    sew_edgeTurn (stage1 D k hk E) (k+2) (by omega) (v:=Sum.inl v) (w:=Sum.inl w) (Or.inl h),
    sew_edgeTurn (stage0 D k hk E) (k+3) (by omega) (v:=Sum.inl v) (w:=Sum.inl w) h]
  rfl
lemma new_edgeTurn {v w : E.Vertex} (h : E.wiring v w) :
    (D.gate4 k hk E).edgeTurn (.inr v) (.inr w)=E.edgeTurn v w := by
  change (((stage0 D k hk E).sew _ _).sew _ _ |>.sew _ _ |>.sew _ _).edgeTurn _ _=_
  rw [sew_edgeTurn (stage3 D k hk E) k (by omega) (v:=Sum.inr v) (w:=Sum.inr w) (Or.inl (Or.inl (Or.inl h))),
    sew_edgeTurn (stage2 D k hk E) (k+1) (by omega) (v:=Sum.inr v) (w:=Sum.inr w) (Or.inl (Or.inl h)),
    sew_edgeTurn (stage1 D k hk E) (k+2) (by omega) (v:=Sum.inr v) (w:=Sum.inr w) (Or.inl h),
    sew_edgeTurn (stage0 D k hk E) (k+3) (by omega) (v:=Sum.inr v) (w:=Sum.inr w) h]
  rfl
lemma cross_edgeTurn (v : D.Vertex) (w : E.Vertex) :
    (D.gate4 k hk E).edgeTurn (.inl v) (.inr w)=0 :=
  sew_zeroTurn _ _ _ (sew_zeroTurn _ _ _ (sew_zeroTurn _ _ _ (sew_zeroTurn _ _ _ rfl)))
end Gate4

 

namespace Rhombus

variable (p q : Pairing 6)

lemma boundary_left (i : Fin 4) : (disk p q).boundary ⟨i.val,by omega⟩=
    .inl ⟨i.val,by omega⟩ := by
  change BoundaryInsert.boundary (n:=6) (m:=6) 6 (by omega) id id
    (BoundaryErase.keep 5 (by omega) (BoundaryErase.keep 4 (by omega) ⟨i.val,by omega⟩))=_
  have he : BoundaryErase.keep 5 (by omega) (BoundaryErase.keep 4 (by omega)
      (⟨i.val,by omega⟩:Fin 8))=(⟨i.val,by omega⟩:Fin 12) := by
    apply Fin.ext
    change Gate4.skip 5 (Gate4.skip 4 i.val)=i.val
    simp (disch := omega) only [Gate4.skip,ite_eq_left]
  rw [he]
  exact BoundaryInsert.boundary_before 6 (by omega) id id _ (by change i.val<6; omega)

lemma boundary_right (i : Fin 4) : (disk p q).boundary ⟨4+i.val,by omega⟩=
    .inr ⟨2+i.val,by omega⟩ := by
  change BoundaryInsert.boundary (n:=6) (m:=6) 6 (by omega) id id
    (BoundaryErase.keep 5 (by omega) (BoundaryErase.keep 4 (by omega) ⟨4+i.val,by omega⟩))=_
  have he : BoundaryErase.keep 5 (by omega) (BoundaryErase.keep 4 (by omega)
      (⟨4+i.val,by omega⟩:Fin 8))=(⟨8+i.val,by omega⟩:Fin 12) := by
    apply Fin.ext
    change Gate4.skip 5 (Gate4.skip 4 (4+i.val))=8+i.val
    simp (disch := omega) only [Gate4.skip,ite_eq_right]
    omega
  rw [he,BoundaryInsert.boundary_between 6 (by omega) id id _
    (by change 6≤8+i.val; omega) (by change 8+i.val<6+6; omega)]
  apply congrArg Sum.inr
  apply Fin.ext
  change (8+i.val)-6=2+i.val
  omega

lemma input_boundary (i : Fin 4) : (disk p q).boundary (Gate4.input i)=
    .inl ⟨3-i.val,by omega⟩ := boundary_left p q ⟨3-i.val,by omega⟩
lemma output_boundary (i : Fin 4) : (disk p q).boundary (Gate4.output i)=
    .inr ⟨2+i.val,by omega⟩ := boundary_right p q i

lemma gauge_input (i : Fin 4) : (disk p q).gauge (Gate4.input i)=
    (if i.val<2 then -3 else -5) := by
  rw [←vertexGauge_boundary,input_boundary]
  change upGauge ⟨3-i.val,_⟩=_
  fin_cases i <;> decide
lemma first_left : (stage p q).boundary (BoundaryErase.left 5 (by omega))=.inl (5:Fin 6) := by
  exact BoundaryInsert.boundary_before (n:=6) (m:=6) 6 (by omega) id id _ (by decide)
lemma first_right : (stage p q).boundary (BoundaryErase.right 5 (by omega))=.inr (0:Fin 6) := by
  exact BoundaryInsert.boundary_between (n:=6) (m:=6) 6 (by omega) id id _ (by decide) (by decide)
lemma second_left : (joined p q).boundary
    (BoundaryErase.left 4 (by omega))=.inl (4:Fin 6) := by
  change BoundaryInsert.boundary (n:=6) (m:=6) 6 (by omega) id id (4:Fin 12)=_
  exact BoundaryInsert.boundary_before (n:=6) (m:=6) 6 (by omega) id id _ (by decide)
lemma second_right : (joined p q).boundary
    (BoundaryErase.right 4 (by omega))=.inr (1:Fin 6) := by
  change BoundaryInsert.boundary (n:=6) (m:=6) 6 (by omega) id id (7:Fin 12)=_
  exact BoundaryInsert.boundary_between (n:=6) (m:=6) 6 (by omega) id id _ (by decide) (by decide)

variable (hm : ∀ i : Fin 2,p.Occupied ⟨4+i.val,by omega⟩ ↔ q.Occupied ⟨1-i.val,by omega⟩)
include hm
lemma match1 : Graph.Used (stage p q).wiring ((stage p q).boundary (BoundaryErase.left 5 (by omega))) ↔
    Graph.Used (stage p q).wiring ((stage p q).boundary (BoundaryErase.right 5 (by omega))) := by
  rw [first_left,first_right]
  change Graph.Used (BoundaryInsert.unionGraph p.Adj q.Adj) (.inl 5) ↔
    Graph.Used (BoundaryInsert.unionGraph p.Adj q.Adj) (.inr 0)
  rw [BoundaryInsert.used_left,BoundaryInsert.used_right]
  exact hm 1
lemma stage_used (v : Fin 6⊕Fin 6) :
    Graph.Used (joined p q).wiring v ↔ Graph.Used (stage p q).wiring v :=
  sew_used _ _ _ (match1 p q hm) v
lemma match2 : Graph.Used (joined p q).wiring
    ((joined p q).boundary (BoundaryErase.left 4 (by omega))) ↔
    Graph.Used (joined p q).wiring
    ((joined p q).boundary (BoundaryErase.right 4 (by omega))) := by
  erw [second_left,second_right,stage_used p q hm,stage_used p q hm]
  change Graph.Used (BoundaryInsert.unionGraph p.Adj q.Adj) (.inl 4) ↔
    Graph.Used (BoundaryInsert.unionGraph p.Adj q.Adj) (.inr 1)
  rw [BoundaryInsert.used_left,BoundaryInsert.used_right]
  exact hm 0
lemma used (v : Fin 6⊕Fin 6) : Graph.Used (disk p q).wiring v ↔
    Graph.Used (stage p q).wiring v :=
  (sew_used _ _ _ (match2 p q hm) v).trans (stage_used p q hm v)
lemma compatible : (disk p q).Compatible := by
  refine ⟨⟨True.intro,match1 p q hm,?_⟩,match2 p q hm,?_⟩
  · rw [←vertexGauge_boundary,←vertexGauge_boundary,first_right,first_left]
    change downGauge 0=upGauge 5-3
    decide
  · rw [←vertexGauge_boundary,←vertexGauge_boundary,second_right,second_left]
    change downGauge 1=upGauge 4-3
    decide

lemma wiring (v w : Fin 6⊕Fin 6) : (disk p q).wiring v w ↔
    BoundaryInsert.unionGraph p.Adj q.Adj v w ∨ ∃ i : Fin 2,p.Occupied ⟨4+i.val,by omega⟩ ∧
      ((v=.inl ⟨4+i.val,by omega⟩ ∧ w=.inr ⟨1-i.val,by omega⟩) ∨
        (w=.inl ⟨4+i.val,by omega⟩ ∧ v=.inr ⟨1-i.val,by omega⟩)) := by
  change BoundarySew.graph (joined p q).wiring _ _ _ v w ↔ _
  simp only [BoundarySew.graph]
  erw [second_left,second_right,stage_used p q hm]
  change (BoundarySew.graph (stage p q).wiring _ _ _ v w ∨ _) ↔ _
  simp only [BoundarySew.graph]
  rw [first_left,first_right]
  change ((_ ∨ (Graph.Used (BoundaryInsert.unionGraph p.Adj q.Adj) (.inl 5) ∧ _)) ∨
    (Graph.Used (BoundaryInsert.unionGraph p.Adj q.Adj) (.inl 4) ∧ _)) ↔ _
  rw [BoundaryInsert.used_left,BoundaryInsert.used_left]
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false]
  change ((BoundaryInsert.unionGraph p.Adj q.Adj v w ∨ (p.Occupied 5 ∧ _)) ∨ (p.Occupied 4 ∧ _)) ↔ _
  tauto

omit hm
lemma up_edge {v w : Fin 6} (h : p.Adj v w) : (disk p q).wiring (.inl v) (.inl w) :=
  Or.inl (Or.inl h)
lemma down_edge {v w : Fin 6} (h : q.Adj v w) : (disk p q).wiring (.inr v) (.inr w) :=
  Or.inl (Or.inl h)
lemma up_turn {v w : Fin 6} (h : p.Adj v w) :
    (disk p q).edgeTurn (.inl v) (.inl w)=Pairing.arcTurn upGauge v w := by
  change ((joined p q).sew 4 (by omega)).edgeTurn _ _=_
  rw [sew_edgeTurn (joined p q) 4 (by omega) (v:=Sum.inl v) (w:=Sum.inl w) (Or.inl h),
    sew_edgeTurn (stage p q) 5 (by omega) (v:=Sum.inl v) (w:=Sum.inl w) h]
  rfl
lemma down_turn {v w : Fin 6} (h : q.Adj v w) :
    (disk p q).edgeTurn (.inr v) (.inr w)=Pairing.arcTurn downGauge v w := by
  change ((joined p q).sew 4 (by omega)).edgeTurn _ _=_
  rw [sew_edgeTurn (joined p q) 4 (by omega) (v:=Sum.inr v) (w:=Sum.inr w) (Or.inl h),
    sew_edgeTurn (stage p q) 5 (by omega) (v:=Sum.inr v) (w:=Sum.inr w) h]
  rfl
lemma cross_turn (v w : Fin 6) : (disk p q).edgeTurn (.inl v) (.inr w)=0 :=
  sew_zeroTurn _ _ _ (sew_zeroTurn _ _ _ rfl)
end Rhombus
end TurnDisk

 

 


namespace TurnNetwork
open TurnDisk

variable {n : ℕ} (p₀ : Pairing n) (g₀ : Fin n → ℤ)
  (p q : ℕ → Pairing 6) (k : ℕ → ℕ) (hk : ∀ t,k t+4≤n)

lemma names_old (t : ℕ) (v : (disk p₀ g₀ p q k hk t).Vertex) :
    names p₀ g₀ p q k hk (t+1) (.inl v)=old (names p₀ g₀ p q k hk t v) := rfl
lemma names_fresh (t : ℕ) (v : Local) :
    names p₀ g₀ p q k hk (t+1) (.inr v)=fresh v := rfl
lemma inv_old (t : ℕ) (v : Node n t) :
    (names p₀ g₀ p q k hk (t+1)).symm (old v)=.inl ((names p₀ g₀ p q k hk t).symm v) := by
  apply (names p₀ g₀ p q k hk (t+1)).injective
  rw [Equiv.apply_symm_apply,names_old,Equiv.apply_symm_apply]
lemma inv_fresh (t : ℕ) (v : Local) :
    (names p₀ g₀ p q k hk (t+1)).symm (fresh v)=.inr v := by
  apply (names p₀ g₀ p q k hk (t+1)).injective
  rw [Equiv.apply_symm_apply,names_fresh]

lemma boundary_slot (t : ℕ) (i : Fin 4) :
    boundary p₀ g₀ p q k hk (t+1) (Gate4.slot (k t) (hk t) i)=
      fresh (.inr ⟨2+i.val,by omega⟩) := by
  unfold boundary
  change names p₀ g₀ p q k hk (t+1)
    (((disk p₀ g₀ p q k hk t).gate4 (k t) (hk t) (Rhombus.disk (p t) (q t))).boundary _) = _
  erw [Gate4.boundary_slot,Rhombus.output_boundary]
  rfl
lemma boundary_outside (t : ℕ) (i : Fin n) (hi : i.val<k t ∨ k t+4 ≤ i.val) :
    boundary p₀ g₀ p q k hk (t+1) i=old (boundary p₀ g₀ p q k hk t i) := by
  unfold boundary
  change names p₀ g₀ p q k hk (t+1)
    (((disk p₀ g₀ p q k hk t).gate4 (k t) (hk t) (Rhombus.disk (p t) (q t))).boundary _) = _
  erw [Gate4.boundary_outside _ _ _ _ i hi]
  rfl

lemma old_edge (t : ℕ) {v w : Node n t} (h : graph p₀ g₀ p q k hk t v w) :
    graph p₀ g₀ p q k hk (t+1) (old v) (old w) := by
  unfold graph
  rw [inv_old,inv_old]
  exact Gate4.old_edge _ _ _ _ h
lemma old_turn (t : ℕ) {v w : Node n t} (h : graph p₀ g₀ p q k hk t v w) :
    edgeTurn p₀ g₀ p q k hk (t+1) (old v) (old w)=edgeTurn p₀ g₀ p q k hk t v w := by
  unfold edgeTurn
  rw [inv_old,inv_old]
  exact Gate4.old_edgeTurn _ _ _ _ h
lemma fresh_edge (t : ℕ) {v w : Local} (h : (Rhombus.disk (p t) (q t)).wiring v w) :
    graph p₀ g₀ p q k hk (t+1) (fresh v) (fresh w) := by
  unfold graph
  rw [inv_fresh,inv_fresh]
  exact Gate4.new_edge _ _ _ _ h
lemma fresh_turn (t : ℕ) {v w : Local} (h : (Rhombus.disk (p t) (q t)).wiring v w) :
    edgeTurn p₀ g₀ p q k hk (t+1) (fresh v) (fresh w)=(Rhombus.disk (p t) (q t)).edgeTurn v w := by
  unfold edgeTurn
  rw [inv_fresh,inv_fresh]
  exact Gate4.new_edgeTurn _ _ _ _ h
lemma wire_turn (t : ℕ) (v : Node n t) (w : Local) :
    edgeTurn p₀ g₀ p q k hk (t+1) (old v) (fresh w)=0 := by
  unfold edgeTurn
  rw [inv_old,inv_fresh]
  exact Gate4.cross_edgeTurn _ _ _ _ _ _

omit g₀ k hk
lemma occupied_old (t : ℕ) (v : Node n t) : Occupied p₀ p q (t+1) (old v) ↔ Occupied p₀ p q t v := by
  cases v with
  | inl i=>rfl
  | inr x=>obtain ⟨i,(v|v)⟩:=x <;> rfl
lemma occupied_fresh (t : ℕ) (v : Local) :
    Occupied p₀ p q (t+1) (fresh v) ↔ match v with
      | .inl i=>(p t).Occupied i
      | .inr i=>(q t).Occupied i := by cases v <;> rfl

include g₀ k hk
lemma used_equiv (t : ℕ) (v : Node n t) :
    Graph.Used (graph p₀ g₀ p q k hk t) v ↔
      Graph.Used (disk p₀ g₀ p q k hk t).wiring ((names p₀ g₀ p q k hk t).symm v) := by
  constructor
  · rintro ⟨w,hw⟩
    exact ⟨(names p₀ g₀ p q k hk t).symm w,hw⟩
  · rintro ⟨w,hw⟩
    exact ⟨names p₀ g₀ p q k hk t w,by simpa only [graph,Equiv.symm_apply_apply] using hw⟩

 

theorem potential (t : ℕ) (hc : (disk p₀ g₀ p q k hk t).Compatible)
    (hd : Graph.DrainsBoundary (graph p₀ g₀ p q k hk t) (boundary p₀ g₀ p q k hk t)) :
    ∃ (a : Pairing n) (P : Node n t → ℤ),
      (∀ i j,Relation.ReflTransGen (graph p₀ g₀ p q k hk t)
        (boundary p₀ g₀ p q k hk t i) (boundary p₀ g₀ p q k hk t j) ↔ i=j ∨ a.Adj i j) ∧
      (∀ i j,a.Adj i j → P (boundary p₀ g₀ p q k hk t j)-P (boundary p₀ g₀ p q k hk t i)=
        Pairing.arcTurn (disk p₀ g₀ p q k hk t).gauge i j) ∧
      ∀ v w,graph p₀ g₀ p q k hk t v w → P w-P v=edgeTurn p₀ g₀ p q k hk t v w := by
  have hd' : Graph.DrainsBoundary (disk p₀ g₀ p q k hk t).wiring (disk p₀ g₀ p q k hk t).boundary := by
    intro v w hvw
    have he : graph p₀ g₀ p q k hk t (names p₀ g₀ p q k hk t v) (names p₀ g₀ p q k hk t w) := by
      simpa only [graph,Equiv.symm_apply_apply] using hvw
    obtain ⟨i,hi⟩:=hd _ _ he
    refine ⟨i,?_⟩
    have h:=Graph.map_reach (names p₀ g₀ p q k hk t).symm (fun _ _ h=>.single h) hi
    simpa only [boundary,Equiv.symm_apply_apply] using h
  obtain ⟨a,P,hr,ha,he⟩:=(disk p₀ g₀ p q k hk t).potential hc hd'
  refine ⟨a,P ∘ (names p₀ g₀ p q k hk t).symm,?_,?_,fun v w h=>he _ _ h⟩
  · intro i j
    rw [←hr.reach]
    constructor
    · intro h
      have hh:=Graph.map_reach (names p₀ g₀ p q k hk t).symm (fun _ _ h=>.single h) h
      simpa only [boundary,Equiv.symm_apply_apply] using hh
    · intro h
      exact Graph.map_reach (names p₀ g₀ p q k hk t) (fun _ _ h=>by
        apply Relation.ReflTransGen.single
        simpa only [graph,Equiv.symm_apply_apply] using h) h
  · intro i j hij
    simpa only [Function.comp_apply,boundary,Equiv.symm_apply_apply] using ha i j hij

end TurnNetwork
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TurnEvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace TurnNetwork
open TurnDisk


lemma lift_refl {n t : ℕ} (v : Node n t) : lift (le_refl t) v=v := by
  rcases v with i|⟨i,v⟩ <;> rfl
lemma lift_trans {n r s t : ℕ} (hrs : r ≤ s) (hst : s ≤ t) (v : Node n r) :
    lift hst (lift hrs v)=lift (hrs.trans hst) v := by
  rcases v with i|⟨i,v⟩ <;> rfl
lemma lift_old {n s t : ℕ} (h : s ≤ t) (v : Node n s) :
    old (lift h v)=lift (h.trans (Nat.le_succ t)) v := by
  rcases v with i|⟨i,v⟩ <;> rfl
lemma old_eq_lift {n t : ℕ} (v : Node n t) : old v=lift (Nat.le_succ t) v := by
  rcases v with i|⟨i,v⟩ <;> rfl

variable {n : ℕ} (p₀ : Pairing n) (g₀ : Fin n → ℤ)
  (p q : ℕ → Pairing 6) (k : ℕ → ℕ) (hk : ∀ t,k t+4 ≤ n)

lemma lift_edge {s t : ℕ} (hst : s ≤ t) {v w : Node n s}
    (h : graph p₀ g₀ p q k hk s v w) :
    graph p₀ g₀ p q k hk t (lift hst v) (lift hst w) := by
  induction t,hst using Nat.le_induction with
  | base => simpa only [lift_refl] using h
  | succ t hst ih => simpa only [lift_old] using old_edge p₀ g₀ p q k hk t ih

lemma lift_turn {s t : ℕ} (hst : s ≤ t) {v w : Node n s}
    (h : graph p₀ g₀ p q k hk s v w) :
    edgeTurn p₀ g₀ p q k hk t (lift hst v) (lift hst w)=
      edgeTurn p₀ g₀ p q k hk s v w := by
  induction t,hst using Nat.le_induction with
  | base => simp only [lift_refl]
  | succ t hst ih =>
    simpa only [lift_old] using (old_turn p₀ g₀ p q k hk t (lift_edge p₀ g₀ p q k hk hst h)).trans ih

lemma boundary_untouched {s t : ℕ} (hst : s ≤ t) (i : Fin n)
    (hi : ∀ u,s ≤ u → u<t → i.val<k u ∨ k u+4  ≤  i.val) :
    boundary p₀ g₀ p q k hk t i=lift hst (boundary p₀ g₀ p q k hk s i) := by
  induction t,hst using Nat.le_induction with
  | base => exact (lift_refl _).symm
  | succ t hst ih =>
    rw [boundary_outside p₀ g₀ p q k hk t i (hi t hst (by omega)),
      ih (fun u hu hut=>hi u hu (by omega)),lift_old]

lemma boundary_last {s t : ℕ} (hst : s<t) (i : Fin 4)
    (hi : ∀ u,s+1 ≤ u → u<t → (Gate4.slot (k s) (hk s) i).val<k u ∨
      k u+4 ≤ (Gate4.slot (k s) (hk s) i).val) :
    boundary p₀ g₀ p q k hk t (Gate4.slot (k s) (hk s) i)=
      .inr (⟨s,hst⟩,.inr ⟨2+i.val,by omega⟩) := by
  rw [boundary_untouched p₀ g₀ p q k hk (by omega : s+1 ≤ t) _ hi,
    boundary_slot]
  rfl

lemma gauge_untouched {s t : ℕ} (hst : s ≤ t) (i : Fin n)
    (hi : ∀ u,s ≤ u → u<t → i.val<k u ∨ k u+4  ≤  i.val) :
    (disk p₀ g₀ p q k hk t).gauge i=(disk p₀ g₀ p q k hk s).gauge i := by
  induction t,hst using Nat.le_induction with
  | base => rfl
  | succ t hst ih =>
    change ((disk p₀ g₀ p q k hk t).gate4 _ _ _).gauge i=_
    rw [Gate4.gauge_outside _ _ _ _ i (hi t hst (by omega))]
    exact ih (fun u hu hut=>hi u hu (by omega))

lemma namedGauge_old (t : ℕ) (v : Node n t) : namedGauge g₀ (t+1) (old v)=namedGauge g₀ t v := by
  rcases v with i|⟨i,(v|v)⟩ <;> rfl
lemma namedGauge_vertex (t : ℕ) (v : Node n t) :
    (disk p₀ g₀ p q k hk t).vertexGauge ((names p₀ g₀ p q k hk t).symm v)=namedGauge g₀ t v := by
  induction t with
  | zero => rcases v with i|⟨i,v⟩; rfl; exact Fin.elim0 i
  | succ t ih =>
    obtain ⟨v,rfl⟩|⟨v,rfl⟩:=cover v
    · rw [inv_old,namedGauge_old]
      exact ih v
    · rw [inv_fresh]
      cases v <;> rfl
lemma namedGauge_boundary (t : ℕ) (i : Fin n) :
    namedGauge g₀ t (boundary p₀ g₀ p q k hk t i)=(disk p₀ g₀ p q k hk t).gauge i := by
  rw [←namedGauge_vertex p₀ g₀ p q k hk]
  simp only [boundary,Equiv.symm_apply_apply,vertexGauge_boundary]


lemma Matches.mono {s t : ℕ} (h : Matches p₀ g₀ p q k hk t) (hst : s ≤ t) :
    Matches p₀ g₀ p q k hk s :=
  ⟨fun u hu=>h.1 u (hu.trans_le hst),fun u hu=>h.2 u (hu.trans_le hst)⟩

lemma occupied_iff_used (t : ℕ) (hm : Matches p₀ g₀ p q k hk t) (v : Node n t) :
    Graph.Used (graph p₀ g₀ p q k hk t) v ↔ Occupied p₀ p q t v := by
  induction t with
  | zero =>
    rcases v with i|⟨i,v⟩
    · rw [used_equiv]
      rfl
    · exact Fin.elim0 i
  | succ t ih =>
    have hm' : ∀ i : Fin 4,Graph.Used (disk p₀ g₀ p q k hk t).wiring
        ((disk p₀ g₀ p q k hk t).boundary (Gate4.slot (k t) (hk t) i)) ↔
          Graph.Used (Rhombus.disk (p t) (q t)).wiring
            ((Rhombus.disk (p t) (q t)).boundary (Gate4.input i)) := by
      intro i
      have hu := (used_equiv p₀ g₀ p q k hk t
        (boundary p₀ g₀ p q k hk t (Gate4.slot (k t) (hk t) i)))
      simp only [boundary,Equiv.symm_apply_apply] at hu
      erw [←hu,ih (Matches.mono _ _ _ _ _ _ hm (by omega)),hm.2 t (by omega),Rhombus.input_boundary,
        Rhombus.used _ _ (hm.1 t (by omega))]
      exact (BoundaryInsert.used_left (p t).Adj (q t).Adj _).symm
    obtain ⟨w,rfl⟩|⟨w,rfl⟩:=cover v
    · rw [occupied_old,used_equiv,inv_old]
      change Graph.Used ((disk p₀ g₀ p q k hk t).gate4 _ _ _).wiring _ ↔ _
      erw [Gate4.used _ _ _ _ hm',BoundaryInsert.used_left,←used_equiv]
      exact ih (Matches.mono _ _ _ _ _ _ hm (by omega)) w
    · rw [occupied_fresh,used_equiv,inv_fresh]
      change Graph.Used ((disk p₀ g₀ p q k hk t).gate4 _ _ _).wiring _ ↔ _
      erw [Gate4.used _ _ _ _ hm',BoundaryInsert.used_right,Rhombus.used _ _ (hm.1 t (by omega))]
      cases w with
      | inl i => exact BoundaryInsert.used_left _ _ _
      | inr i => exact BoundaryInsert.used_right _ _ _

lemma gate_matches (t : ℕ) (hm : Matches p₀ g₀ p q k hk (t+1)) :
    ∀ i : Fin 4,Graph.Used (disk p₀ g₀ p q k hk t).wiring
        ((disk p₀ g₀ p q k hk t).boundary (Gate4.slot (k t) (hk t) i)) ↔
          Graph.Used (Rhombus.disk (p t) (q t)).wiring
            ((Rhombus.disk (p t) (q t)).boundary (Gate4.input i)) := by
  intro i
  have hu := (used_equiv p₀ g₀ p q k hk t
    (boundary p₀ g₀ p q k hk t (Gate4.slot (k t) (hk t) i)))
  simp only [boundary,Equiv.symm_apply_apply] at hu
  erw [←hu,occupied_iff_used _ _ _ _ _ _ _ (Matches.mono _ _ _ _ _ _ hm (by omega)),hm.2 t (by omega),
    Rhombus.input_boundary,Rhombus.used _ _ (hm.1 t (by omega))]
  exact (BoundaryInsert.used_left (p t).Adj (q t).Adj _).symm

lemma compatible (t : ℕ) (hm : Matches p₀ g₀ p q k hk t)
    (hg : ∀ u,u<t → ∀ i : Fin 4,
      (disk p₀ g₀ p q k hk u).gauge (Gate4.slot (k u) (hk u) i)=
        if i.val<2 then 0 else -2) :
    (disk p₀ g₀ p q k hk t).Compatible := by
  induction t with
  | zero => trivial
  | succ t ih =>
    apply Gate4.compatible _ _ _ _ (gate_matches p₀ g₀ p q k hk t hm)
      (ih (Matches.mono _ _ _ _ _ _ hm (by omega)) (fun u hu=>hg u (by omega)))
      (Rhombus.compatible _ _ (hm.1 t (by omega)))
    intro i
    rw [Rhombus.gauge_input,hg t (by omega)]
    split_ifs <;> rfl

lemma wire_edge (t : ℕ) (hm : Matches p₀ g₀ p q k hk (t+1)) (i : Fin 4)
    (hi : (p t).Occupied ⟨3-i.val,by omega⟩) :
    graph p₀ g₀ p q k hk (t+1)
      (old (boundary p₀ g₀ p q k hk t (Gate4.slot (k t) (hk t) i)))
      (fresh (.inl ⟨3-i.val,by omega⟩)) := by
  unfold graph
  rw [inv_old,inv_fresh]
  simp only [boundary,Equiv.symm_apply_apply]
  apply (Gate4.wiring _ _ _ _ (gate_matches p₀ g₀ p q k hk t hm) _ _).mpr
  right
  refine ⟨i,?_,Or.inl ⟨rfl,?_⟩⟩
  · erw [Rhombus.input_boundary,Rhombus.used _ _ (hm.1 t (by omega)),BoundaryInsert.used_left]
    exact hi
  · rw [Rhombus.input_boundary]
    rfl

end TurnNetwork

 

 

namespace TurnRectangle
open TurnDisk TurnNetwork
section BoundaryEvolution

lemma position_time {M N c r : ℕ} (hN : 1 ≤ N) (hr : r<N) :
    position M N (c*N+r)=width M N+2*(M-1-c+r) := by
  have hd : (c*N+r)/N=c := by
    rw [Nat.mul_comm c N,Nat.mul_add_div (by omega),Nat.div_eq_of_lt hr,Nat.add_zero]
  have hm : (c*N+r)%N=r := by
    rw [Nat.mul_comm c N,Nat.mul_add_mod,Nat.mod_eq_of_lt hr]
  simp only [position,hd,hm]

variable {M N : ℕ} (hM : 1 ≤ M) (hN : 1 ≤ N)
  (p₀ : Pairing (ports M N)) (g₀ : Fin (ports M N) → ℤ) (p q : ℕ → Pairing 6)

lemma southSlot_val {c r : ℕ} (hc : c<M) (hr : r<N) (l : Fin 2) :
    (southSlot hM hN hc hr l).val=width M N+2*(M-1-c+r)+l.val := by
  change position M N (c*N+r)+l.val=_
  rw [position_time hN hr]
lemma westSlot_val {c r : ℕ} (hc : c<M) (hr : r<N) (l : Fin 2) :
    (westSlot hM hN hc hr l).val=width M N+2*(M-1-c+r)+2+l.val := by
  change position M N (c*N+r)+(2+l.val)=_
  rw [position_time hN hr]
  omega

omit p₀ g₀ p q
lemma south_initial_untouched {c u : ℕ} (hc : c<M) (hu : u < c*N) (l : Fin 2) :
    (southSlot hM hN hc (by omega : 0<N) l).val<position M N u := by
  have hc' : u/N < c := (Nat.div_lt_iff_lt_mul (by omega : 0<N)).mpr (by simpa only [Nat.mul_comm] using hu)
  rw [southSlot_val]
  dsimp only [position]
  omega

lemma west_initial_untouched {r u : ℕ} (hr : r<N) (hu : u < r) (l : Fin 2) :
    position M N u+4 ≤ (westSlot hM hN (by omega : 0<M) hr l).val := by
  have hd : u/N=0 := Nat.div_eq_of_lt (hu.trans hr)
  have hm : u%N=u := Nat.mod_eq_of_lt (hu.trans hr)
  rw [westSlot_val]
  dsimp only [position]
  rw [hd,hm]
  omega

lemma west_previous_untouched {c r u : ℕ} (hc : c<M) (hc0 : 0 < c) (hr : r<N)
    (hu₁ : (c-1)*N+r+1 ≤ u) (hu₂ : u < c*N+r) (l : Fin 2) :
    (westSlot hM hN hc hr l).val<position M N u ∨
      position M N u+4 ≤ (westSlot hM hN hc hr l).val := by
  have hN0 : 0<N := by omega
  have hcN : (c-1)*N+N=c*N := by
    calc
      (c-1)*N+N=(c-1+1)*N := by ring
      _ = c*N := by congr 1; omega
  have hdlo : c-1 ≤ u/N := (Nat.le_div_iff_mul_le hN0).mpr (by omega)
  have hdhi : u/N ≤ c := by
    have hu : u<(c+1)*N := by rw [Nat.add_mul]; omega
    have hh:=(Nat.div_lt_iff_lt_mul hN0).mpr (by simpa only [Nat.mul_comm] using hu)
    omega
  have hdivision:=Nat.mod_add_div u N
  rw [westSlot_val]
  dsimp only [position]
  by_cases hd : u/N=c
  · rw [hd,Nat.mul_comm N c] at hdivision
    right
    rw [hd]
    omega
  · have he : u/N=c-1 := by omega
    rw [he,Nat.mul_comm N (c-1)] at hdivision
    left
    rw [he]
    omega

include p₀ g₀ p q

lemma south_initial {c : ℕ} (hc : c<M) (l : Fin 2) :
    bdry hM hN p₀ g₀ p q (c*N)
      (southSlot hM hN hc (by omega : 0<N) l)=
      .inl (southSlot hM hN hc (by omega : 0<N) l) := by
  have hh:=boundary_untouched p₀ g₀ p q (position M N) (position_bound hM hN)
    (Nat.zero_le (c*N)) (southSlot hM hN hc (by omega : 0<N) l)
    (fun u _ hu=>Or.inl (south_initial_untouched hM hN hc hu l))
  exact hh

lemma west_initial {r : ℕ} (hr : r<N) (l : Fin 2) :
    bdry hM hN p₀ g₀ p q r
      (westSlot hM hN (by omega : 0<M) hr l)=
      .inl (westSlot hM hN (by omega : 0<M) hr l) := by
  exact boundary_untouched p₀ g₀ p q (position M N) (position_bound hM hN)
    (Nat.zero_le r) (westSlot hM hN (by omega : 0<M) hr l)
    (fun u _ hu=>Or.inr (west_initial_untouched hM hN hr hu l))

lemma south_previous {c r : ℕ} (hc : c<M) (hr : r<N) (hr0 : 0 < r) (l : Fin 2) :
    bdry hM hN p₀ g₀ p q (c*N+r) (southSlot hM hN hc hr l)=
      .inr (⟨c*N+(r-1),by omega⟩,.inr ⟨4+l.val,by omega⟩) := by
  have he : southSlot hM hN hc hr l=Gate4.slot (position M N (c*N+(r-1)))
      (position_bound hM hN _) ⟨2+l.val,by omega⟩ := by
    apply Fin.ext
    rw [southSlot_val]
    change _ = position M N (c*N+(r-1))+(2+l.val)
    rw [position_time hN (by omega : r-1<N)]
    omega
  rw [he]
  simpa only [←Nat.add_assoc] using boundary_last p₀ g₀ p q (position M N) (position_bound hM hN)
    (by omega : c*N+(r-1) < c*N+r) ⟨2+l.val,by omega⟩ (by intro u hu₁ hu₂; omega)

lemma west_previous {c r : ℕ} (hc : c<M) (hc0 : 0 < c) (hr : r<N) (l : Fin 2) :
    bdry hM hN p₀ g₀ p q (c*N+r) (westSlot hM hN hc hr l)=
      .inr (⟨(c-1)*N+r,by
        calc
          (c-1)*N+r < ((c-1)+1)*N+r := Nat.add_lt_add_right
            (Nat.mul_lt_mul_of_pos_right (by omega) (by omega)) _
          _ = c*N+r := by congr 2; omega⟩,.inr ⟨2+l.val,by omega⟩) := by
  have htime : (c-1)*N+r+1 ≤ c*N+r := by
    have hh : (c-1)*N+N=c*N := by
      calc
        (c-1)*N+N=(c-1+1)*N := by ring
        _ = c*N := by congr 1; omega
    omega
  have he : westSlot hM hN hc hr l=Gate4.slot (position M N ((c-1)*N+r))
      (position_bound hM hN _) ⟨l.val,by omega⟩ := by
    apply Fin.ext
    rw [westSlot_val]
    change _=position M N ((c-1)*N+r)+l.val
    rw [position_time hN hr]
    omega
  rw [bdry,boundary_untouched p₀ g₀ p q (position M N) (position_bound hM hN) htime _
    (fun u hu₁ hu₂=>west_previous_untouched hM hN hc hc0 hr hu₁ hu₂ l),he,boundary_slot]
  rfl

end BoundaryEvolution

 

 


variable {M N : ℕ} (hM : 1 ≤ M) (hN : 1 ≤ N)
  (p₀ : Pairing (ports M N)) (g₀ : Fin (ports M N) → ℤ) (p q : ℕ → Pairing 6)

lemma retained_boundary (t : ℕ) (i : Fin (ports M N)) (hi : i.val<width M N) :
    bdry hM hN p₀ g₀ p q t i=.inl i := by
  apply boundary_untouched p₀ g₀ p q (position M N) (position_bound hM hN) (Nat.zero_le t) i
  intro u _ _
  left
  dsimp only [position]
  omega

lemma northSlot_val {c : ℕ} (hc : c<M) (l : Fin 2) :
    (northSlot hM hN hc l).val=width M N+2*(M+N-1-c)+l.val := by
  change position M N (c*N+(N-1))+(2+l.val)=_
  rw [position_time hN (by omega : N-1<N)]
  omega

omit p₀ g₀ p q
lemma north_untouched {c u : ℕ} (hc : c<M) (hu₁ : c*N+(N-1)+1 ≤ u)
    (hu₂ : u<M*N) (l : Fin 2) :
    position M N u+4 ≤ (northSlot hM hN hc l).val := by
  have hnext : (c+1)*N=c*N+(N-1)+1 := by rw [Nat.add_mul,Nat.one_mul]; omega
  have hdlo : c+1 ≤ u/N := (Nat.le_div_iff_mul_le (by omega : 0<N)).mpr (hnext ▸ hu₁)
  have hdhi : u/N<M := (Nat.div_lt_iff_lt_mul (by omega : 0<N)).mpr
    (by simpa only [Nat.mul_comm] using hu₂)
  have hr := Nat.mod_lt u (by omega : 0<N)
  rw [northSlot_val]
  dsimp only [position]
  omega

include p₀ g₀ p q

lemma north_boundary {c : ℕ} (hc : c<M) (l : Fin 2) :
    bdry hM hN p₀ g₀ p q (M*N) (northSlot hM hN hc l)=
      .inr (⟨c*N+(N-1),time_lt (by omega) hc⟩,.inr ⟨4+l.val,by omega⟩) := by
  have hh := boundary_last p₀ g₀ p q (position M N) (position_bound hM hN)
    (s := c*N+(N-1)) (t := M*N)
    (time_lt (M:=M) (N:=N) (c:=c) (r:=N-1) (by omega) hc)
    (⟨2+l.val,by omega⟩ : Fin 4)
    (fun u hu₁ hu₂=>Or.inr (north_untouched hM hN hc hu₁ hu₂ l))
  refine hh.trans ?_
  apply congrArg Sum.inr
  apply congrArg (fun j : Fin 6 => ((⟨c*N+(N-1),time_lt (by omega) hc⟩:Fin (M*N)),Sum.inr j))
  apply Fin.ext
  change 2+(2+l.val)=4+l.val
  omega



omit g₀ p₀ p q
lemma starterGauge_south {c : ℕ} (hc : c<M) (l : Fin 2) :
    starterGauge M N (southSlot hM hN hc (by omega : 0<N) l)=0 := by
  unfold starterGauge
  rw [southSlot_val]
  unfold width
  split_ifs <;> omega
lemma starterGauge_west {r : ℕ} (hr : r<N) (l : Fin 2) :
    starterGauge M N (westSlot hM hN (by omega : 0<M) hr l)= -2 := by
  unfold starterGauge
  rw [westSlot_val]
  unfold width
  split_ifs <;> omega

include p₀ p q
lemma south_gauge {c r : ℕ} (hc : c<M) (hr : r<N) (l : Fin 2) :
    (box hM hN p₀ (starterGauge M N) p q (c*N+r)).gauge (southSlot hM hN hc hr l)=0 := by
  change (disk p₀ (starterGauge M N) p q (position M N) (position_bound hM hN) _).gauge _=_
  rw [← namedGauge_boundary]
  change namedGauge (starterGauge M N) _ (bdry hM hN p₀ (starterGauge M N) p q _ _)=_
  by_cases hr0 : r=0
  · subst r
    simpa only [Nat.add_zero, namedGauge] using
      (congrArg (namedGauge (starterGauge M N) (c*N))
        (south_initial hM hN p₀ (starterGauge M N) p q hc l)).trans
          (starterGauge_south hM hN hc l)
  · have hh := congrArg (namedGauge (starterGauge M N) (c*N+r))
        (south_previous hM hN p₀ (starterGauge M N) p q hc hr (by omega) l)
    refine hh.trans ?_
    change Rhombus.downGauge ⟨4+l.val,_⟩=0
    fin_cases l <;> norm_num [Rhombus.downGauge]
lemma west_gauge {c r : ℕ} (hc : c<M) (hr : r<N) (l : Fin 2) :
    (box hM hN p₀ (starterGauge M N) p q (c*N+r)).gauge (westSlot hM hN hc hr l)= -2 := by
  by_cases hc0 : c=0
  · subst c
    have hh := gauge_untouched p₀ (starterGauge M N) p q
      (position M N) (position_bound hM hN) (Nat.zero_le r)
      (westSlot hM hN (by omega : 0<M) hr l)
      (fun u _ hu=>Or.inr (west_initial_untouched hM hN hr hu l))
    simp only [box, Nat.zero_mul, Nat.zero_add]
    exact hh.trans (starterGauge_west hM hN hr l)
  · change (disk p₀ (starterGauge M N) p q (position M N) (position_bound hM hN) _).gauge _=_
    rw [← namedGauge_boundary]
    change namedGauge (starterGauge M N) _ (bdry hM hN p₀ (starterGauge M N) p q _ _)=_
    have hh := congrArg (namedGauge (starterGauge M N) (c*N+r))
        (west_previous hM hN p₀ (starterGauge M N) p q hc (by omega) hr l)
    refine hh.trans ?_
    change Rhombus.downGauge ⟨2+l.val,_⟩= -2
    fin_cases l <;> norm_num [Rhombus.downGauge]
lemma input_gauge {c r : ℕ} (hc : c<M) (hr : r<N) (i : Fin 4) :
    (box hM hN p₀ (starterGauge M N) p q (c*N+r)).gauge
      (Gate4.slot (position M N (c*N+r)) (position_bound hM hN _) i)=
        if i.val<2 then 0 else -2 := by
  by_cases hi : i.val<2
  · rw [ite_eq_left hi]
    exact south_gauge hM hN p₀ p q hc hr ⟨i.val,hi⟩
  · rw [ite_eq_right hi]
    have he : i=(⟨2+(i.val-2),by omega⟩:Fin 4) := Fin.ext (by change i.val=2+(i.val-2); omega)
    rw [he]
    exact west_gauge hM hN p₀ p q hc hr ⟨i.val-2,by omega⟩

lemma input_gauge_all (t : ℕ) (ht : t<M*N) (i : Fin 4) :
    (box hM hN p₀ (starterGauge M N) p q t).gauge
      (Gate4.slot (position M N t) (position_bound hM hN _) i)=
        if i.val<2 then 0 else -2 := by
  have hc : t/N<M := (Nat.div_lt_iff_lt_mul (by omega : 0<N)).mpr
    (by simpa only [Nat.mul_comm] using ht)
  have hr : t%N<N := Nat.mod_lt t (by omega)
  have hh:=input_gauge hM hN p₀ p q hc hr i
  have he : t/N*N+t%N=t := by simpa only [Nat.mul_comm] using Nat.div_add_mod t N
  simpa only [he] using hh

end TurnRectangle
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TurnRectangleMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical
namespace TurnRectangle
open TurnDisk TurnNetwork

variable {M N : ℕ} (hM : 1 ≤ M) (hN : 1 ≤ N)
  (p₀ : Pairing (ports M N)) (p q : ℕ → Pairing 6)


lemma physical_matches (hm : PhysicalMatches hM hN p₀ p q) :
    Matches p₀ (starterGauge M N) p q (position M N) (position_bound hM hN) (M*N) := by
  constructor
  · intro t ht l
    have hc : t/N<M := (Nat.div_lt_iff_lt_mul (by omega : 0<N)).mpr
      (by simpa only [Nat.mul_comm] using ht)
    have hr : t%N<N := Nat.mod_lt t (by omega)
    have he : t/N*N+t%N=t := by simpa only [Nat.mul_comm] using Nat.div_add_mod t N
    simpa only [he] using hm.1 (t/N) (t%N) hc hr l
  · suffices hh : ∀ c r, (hc : c<M) → (hr : r<N) → ∀ i : Fin 4,
        Occupied p₀ p q (c*N+r) (bdry hM hN p₀ (starterGauge M N) p q (c*N+r)
          (Gate4.slot (position M N (c*N+r)) (position_bound hM hN _) i)) ↔
          (p (c*N+r)).Occupied ⟨3-i.val,by omega⟩ by
      intro t ht i
      have hc : t/N<M := (Nat.div_lt_iff_lt_mul (by omega : 0<N)).mpr
        (by simpa only [Nat.mul_comm] using ht)
      have hr : t%N<N := Nat.mod_lt t (by omega)
      have he : t/N*N+t%N=t := by simpa only [Nat.mul_comm] using Nat.div_add_mod t N
      obtain ⟨c,r,hc₁,hr₁,rfl⟩ : ∃ c r,c<M ∧ r<N ∧ t=c*N+r :=
        ⟨t/N,t%N,hc,hr,he.symm⟩
      exact hh c r hc₁ hr₁ i
    intro c r hc hr i
    by_cases hi : i.val<2
    · let l : Fin 2 := ⟨i.val,hi⟩
      change Occupied p₀ p q (c*N+r) (bdry hM hN p₀ (starterGauge M N) p q (c*N+r)
        (southSlot hM hN hc hr l)) ↔ _
      by_cases hr0 : r=0
      · subst r
        simp only [Nat.add_zero]
        rw [south_initial]
        exact hm.2.1 c hc l
      · rw [south_previous hM hN p₀ (starterGauge M N) p q hc hr (by omega) l]
        exact hm.2.2.2.1 c r hc hr (by omega) l
    · let l : Fin 2 := ⟨i.val-2,by omega⟩
      have he : i=(⟨2+l.val,by omega⟩:Fin 4) := by apply Fin.ext; change i.val=2+(i.val-2); omega
      rw [he]
      have he' : (⟨3-(2+l.val),by omega⟩:Fin 6)=(⟨1-l.val,by omega⟩:Fin 6) := by
        apply Fin.ext; dsimp; omega
      rw [he']
      change Occupied p₀ p q (c*N+r) (bdry hM hN p₀ (starterGauge M N) p q (c*N+r)
        (westSlot hM hN hc hr l)) ↔ _
      by_cases hc0 : c=0
      · subst c
        have hh:=congrArg (Occupied p₀ p q r)
          (west_initial hM hN p₀ (starterGauge M N) p q hr l)
        have hh' := (Iff.of_eq hh).trans (hm.2.2.1 r hr l)
        have hcng {t u : ℕ} (he : t=u) (j : Fin (ports M N)) :
            Occupied p₀ p q t (bdry hM hN p₀ (starterGauge M N) p q t j) ↔
              Occupied p₀ p q u (bdry hM hN p₀ (starterGauge M N) p q u j) := by
          subst u
          rfl
        exact (hcng (by omega : 0*N+r=r) _).trans (by simpa only [Nat.zero_mul,Nat.zero_add] using hh')
      · rw [west_previous hM hN p₀ (starterGauge M N) p q hc (by omega) hr l]
        exact hm.2.2.2.2 c r hc (by omega) hr l

lemma compatible (hm : PhysicalMatches hM hN p₀ p q) :
    (box hM hN p₀ (starterGauge M N) p q (M*N)).Compatible :=
  TurnNetwork.compatible _ _ _ _ _ _ _ (physical_matches hM hN p₀ p q hm)
    (input_gauge_all hM hN p₀ p q)

end TurnRectangle

 

 

namespace TurnStarter

variable (w : ℕ)
lemma cover (i : Fin (2*w)) : (∃ j,i=left w j) ∨ (∃ j,i=right w j) := by
  by_cases hi : i.val<w
  · left
    refine ⟨⟨w-1-i.val,by omega⟩,?_⟩
    apply Fin.ext
    change i.val=w-1-(w-1-i.val)
    omega
  · right
    refine ⟨⟨i.val-w,by omega⟩,?_⟩
    apply Fin.ext
    change i.val=w+(i.val-w)
    omega

lemma adj_iff (active : Fin w → Prop) (a b : Fin (2*w)) :
    (pairing w active).Adj a b ↔ ∃ j,active j ∧
      ((a=left w j ∧ b=right w j) ∨ (a=right w j ∧ b=left w j)) := by
  simp only [Pairing.Adj,pairing,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,
    true_and,Prod.mk.injEq]
  constructor
  · rintro (⟨j,hj,ha,hb⟩|⟨j,hj,hb,ha⟩)
    · exact ⟨j,hj,Or.inl ⟨ha.symm,hb.symm⟩⟩
    · exact ⟨j,hj,Or.inr ⟨ha.symm,hb.symm⟩⟩
  · rintro ⟨j,hj,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
    · exact Or.inl ⟨j,hj,rfl,rfl⟩
    · exact Or.inr ⟨j,hj,rfl,rfl⟩

lemma across (active : Fin w → Prop) {j : Fin w} (hj : active j) :
    (pairing w active).Adj (left w j) (right w j) :=
  (adj_iff w active _ _).mpr ⟨j,hj,Or.inl ⟨rfl,rfl⟩⟩

lemma occupied_right (active : Fin w → Prop) (i : Fin w) :
    (pairing w active).Occupied (right w i) ↔ active i := by
  constructor
  · rintro ⟨v,hv⟩
    obtain ⟨j,hj,h⟩:=(adj_iff w active _ _).mp hv
    rcases h with ⟨h,_⟩|⟨h,_⟩
    · exact ((left_lt_right w j i).ne.symm h).elim
    · exact right_injective w h ▸ hj
  · intro hi
    exact ⟨left w i,(across w active hi).symm⟩

end TurnStarter

 

 

namespace TurnRectangle
open TurnDisk TurnNetwork
section PhysicalMatching

variable {M N : ℕ} (hM : 1 ≤ M) (hN : 1 ≤ N)
  (p₀ : Pairing (ports M N)) (p q : ℕ → Pairing 6)

lemma local_edge {c : Fin M} {r : Fin N} {v w : Local}
    (h : (Rhombus.disk (p (c.val*N+r.val)) (q (c.val*N+r.val))).wiring v w) :
    edges hM hN p₀ p q (cellNode c r v) (cellNode c r w) :=
  lift_edge _ _ _ _ _ _ (by have :=time_lt r.isLt c.isLt; omega : c.val*N+r.val+1 ≤ M*N)
    (fresh_edge _ _ _ _ _ _ _ h)

lemma local_turn {c : Fin M} {r : Fin N} {v w : Local}
    (h : (Rhombus.disk (p (c.val*N+r.val)) (q (c.val*N+r.val))).wiring v w) :
    turns hM hN p₀ p q (cellNode c r v) (cellNode c r w)=
      (Rhombus.disk (p (c.val*N+r.val)) (q (c.val*N+r.val))).edgeTurn v w :=
  (lift_turn _ _ _ _ _ _ (by have :=time_lt r.isLt c.isLt; omega : c.val*N+r.val+1 ≤ M*N)
    (fresh_edge _ _ _ _ _ _ _ h)).trans (fresh_turn _ _ _ _ _ _ _ h)

lemma up_edge {c : Fin M} {r : Fin N} {v w : Fin 6}
    (h : (p (c.val*N+r.val)).Adj v w) :
    edges hM hN p₀ p q (cellNode c r (.inl v)) (cellNode c r (.inl w)) :=
  local_edge hM hN p₀ p q (Rhombus.up_edge _ _ h)
lemma up_turn {c : Fin M} {r : Fin N} {v w : Fin 6}
    (h : (p (c.val*N+r.val)).Adj v w) :
    turns hM hN p₀ p q (cellNode c r (.inl v)) (cellNode c r (.inl w))=
      Pairing.arcTurn Rhombus.upGauge v w :=
  (local_turn hM hN p₀ p q (Rhombus.up_edge _ _ h)).trans (Rhombus.up_turn _ _ h)
lemma down_edge {c : Fin M} {r : Fin N} {v w : Fin 6}
    (h : (q (c.val*N+r.val)).Adj v w) :
    edges hM hN p₀ p q (cellNode c r (.inr v)) (cellNode c r (.inr w)) :=
  local_edge hM hN p₀ p q (Rhombus.down_edge _ _ h)
lemma down_turn {c : Fin M} {r : Fin N} {v w : Fin 6}
    (h : (q (c.val*N+r.val)).Adj v w) :
    turns hM hN p₀ p q (cellNode c r (.inr v)) (cellNode c r (.inr w))=
      Pairing.arcTurn Rhombus.downGauge v w :=
  (local_turn hM hN p₀ p q (Rhombus.down_edge _ _ h)).trans (Rhombus.down_turn _ _ h)

variable (hm : PhysicalMatches hM hN p₀ p q)
include hm
lemma diagonal_edge {c : Fin M} {r : Fin N} (l : Fin 2)
    (h : (p (c.val*N+r.val)).Occupied ⟨4+l.val,by omega⟩) :
    edges hM hN p₀ p q (cellNode c r (.inl ⟨4+l.val,by omega⟩))
      (cellNode c r (.inr ⟨1-l.val,by omega⟩)) :=
  local_edge hM hN p₀ p q ((Rhombus.wiring _ _ (hm.1 _ _ c.isLt r.isLt) _ _).mpr
    (Or.inr ⟨l,h,Or.inl ⟨rfl,rfl⟩⟩))
lemma diagonal_turn {c : Fin M} {r : Fin N} (l : Fin 2)
    (h : (p (c.val*N+r.val)).Occupied ⟨4+l.val,by omega⟩) :
    turns hM hN p₀ p q (cellNode c r (.inl ⟨4+l.val,by omega⟩))
      (cellNode c r (.inr ⟨1-l.val,by omega⟩))=0 :=
  (local_turn hM hN p₀ p q ((Rhombus.wiring _ _ (hm.1 _ _ c.isLt r.isLt) _ _).mpr
    (Or.inr ⟨l,h,Or.inl ⟨rfl,rfl⟩⟩))).trans (Rhombus.cross_turn _ _ _ _)

lemma enter_edge {t : ℕ} (ht : t<M*N) (i : Fin 4)
    (hi : (p t).Occupied ⟨3-i.val,by omega⟩) :
    edges hM hN p₀ p q
      (lift (Nat.le_of_lt ht) (bdry hM hN p₀ (starterGauge M N) p q t
        (Gate4.slot (position M N t) (position_bound hM hN _) i)))
      (.inr (⟨t,ht⟩,.inl ⟨3-i.val,by omega⟩)) := by
  have hh := lift_edge _ _ _ _ _ _ (by omega : t+1 ≤ M*N)
    (wire_edge _ _ _ _ _ _ t ((physical_matches hM hN p₀ p q hm).mono _ _ _ _ _ _ (by omega)) i hi)
  rw [old_eq_lift,lift_trans] at hh
  exact hh
lemma enter_turn {t : ℕ} (ht : t<M*N) (i : Fin 4)
    (hi : (p t).Occupied ⟨3-i.val,by omega⟩) :
    turns hM hN p₀ p q
      (lift (Nat.le_of_lt ht) (bdry hM hN p₀ (starterGauge M N) p q t
        (Gate4.slot (position M N t) (position_bound hM hN _) i)))
      (.inr (⟨t,ht⟩,.inl ⟨3-i.val,by omega⟩))=0 := by
  have hh := (lift_turn _ _ _ _ _ _ (by omega : t+1 ≤ M*N)
    (wire_edge _ _ _ _ _ _ t ((physical_matches hM hN p₀ p q hm).mono _ _ _ _ _ _ (by omega)) i hi)).trans
      (wire_turn _ _ _ _ _ _ t _ _)
  rw [old_eq_lift,lift_trans] at hh
  exact hh

lemma vertical_edge {c : Fin M} {r : Fin N} (hr : 0 < r.val) (l : Fin 2)
    (h : (p (c.val*N+r.val)).Occupied ⟨3-l.val,by omega⟩) :
    edges hM hN p₀ p q (cellNode c ⟨r.val-1,by omega⟩ (.inr ⟨4+l.val,by omega⟩))
      (cellNode c r (.inl ⟨3-l.val,by omega⟩)) := by
  have hh:=enter_edge hM hN p₀ p q hm (time_lt r.isLt c.isLt) ⟨l.val,by omega⟩ h
  change edges hM hN p₀ p q
    (lift _ (bdry hM hN p₀ (starterGauge M N) p q _ (southSlot hM hN c.isLt r.isLt l))) _ at hh
  rw [south_previous hM hN p₀ (starterGauge M N) p q c.isLt r.isLt hr l] at hh
  exact hh
lemma vertical_turn {c : Fin M} {r : Fin N} (hr : 0 < r.val) (l : Fin 2)
    (h : (p (c.val*N+r.val)).Occupied ⟨3-l.val,by omega⟩) :
    turns hM hN p₀ p q (cellNode c ⟨r.val-1,by omega⟩ (.inr ⟨4+l.val,by omega⟩))
      (cellNode c r (.inl ⟨3-l.val,by omega⟩))=0 := by
  have hh:=enter_turn hM hN p₀ p q hm (time_lt r.isLt c.isLt) ⟨l.val,by omega⟩ h
  change turns hM hN p₀ p q
    (lift _ (bdry hM hN p₀ (starterGauge M N) p q _ (southSlot hM hN c.isLt r.isLt l))) _=0 at hh
  rw [south_previous hM hN p₀ (starterGauge M N) p q c.isLt r.isLt hr l] at hh
  exact hh

lemma horizontal_edge {c : Fin M} {r : Fin N} (hc : 0 < c.val) (l : Fin 2)
    (h : (p (c.val*N+r.val)).Occupied ⟨1-l.val,by omega⟩) :
    edges hM hN p₀ p q (cellNode ⟨c.val-1,by omega⟩ r (.inr ⟨2+l.val,by omega⟩))
      (cellNode c r (.inl ⟨1-l.val,by omega⟩)) := by
  have hi : (p (c.val*N+r.val)).Occupied ⟨3-(2+l.val),by omega⟩ := by
    convert h using 1; congr 1; omega
  have hh:=enter_edge hM hN p₀ p q hm (time_lt r.isLt c.isLt) ⟨2+l.val,by omega⟩ hi
  change edges hM hN p₀ p q
    (lift _ (bdry hM hN p₀ (starterGauge M N) p q _ (westSlot hM hN c.isLt r.isLt l))) _ at hh
  rw [west_previous hM hN p₀ (starterGauge M N) p q c.isLt hc r.isLt l] at hh
  convert hh using 1 <;> congr 3
  dsimp only
  omega
lemma horizontal_turn {c : Fin M} {r : Fin N} (hc : 0 < c.val) (l : Fin 2)
    (h : (p (c.val*N+r.val)).Occupied ⟨1-l.val,by omega⟩) :
    turns hM hN p₀ p q (cellNode ⟨c.val-1,by omega⟩ r (.inr ⟨2+l.val,by omega⟩))
      (cellNode c r (.inl ⟨1-l.val,by omega⟩))=0 := by
  have hi : (p (c.val*N+r.val)).Occupied ⟨3-(2+l.val),by omega⟩ := by
    convert h using 1; congr 1; omega
  have hh:=enter_turn hM hN p₀ p q hm (time_lt r.isLt c.isLt) ⟨2+l.val,by omega⟩ hi
  change turns hM hN p₀ p q
    (lift _ (bdry hM hN p₀ (starterGauge M N) p q _ (westSlot hM hN c.isLt r.isLt l))) _=0 at hh
  rw [west_previous hM hN p₀ (starterGauge M N) p q c.isLt hc r.isLt l] at hh
  convert hh using 1; congr 4; dsimp only; omega

end PhysicalMatching

 

 


variable {M N : ℕ}

lemma southRay_div (c : Fin M) (l : Fin 2) : (southRay (N:=N) c l).val/2=M-1-c.val := by
  rw [southRay,Nat.mul_add_div (by omega : 0<2),Nat.div_eq_of_lt l.isLt,Nat.add_zero]
lemma southRay_mod (c : Fin M) (l : Fin 2) : (southRay (N:=N) c l).val%2=l.val := by
  rw [southRay,Nat.mul_add_mod,Nat.mod_eq_of_lt l.isLt]
lemma westRay_div (r : Fin N) (l : Fin 2) : (westRay (M:=M) r l).val/2=M+r.val := by
  rw [westRay,Nat.mul_add_div (by omega : 0<2),Nat.div_eq_of_lt l.isLt,Nat.add_zero]
lemma westRay_mod (r : Fin N) (l : Fin 2) : (westRay (M:=M) r l).val%2=l.val := by
  rw [westRay,Nat.mul_add_mod,Nat.mod_eq_of_lt l.isLt]

variable (hM : 1 ≤ M) (hN : 1 ≤ N) (p q : ℕ → Pairing 6)

lemma active_south (c : Fin M) (l : Fin 2) : starterActive p (southRay (N:=N) c l) ↔
    (p (c.val*N)).Occupied ⟨3-l.val,by omega⟩ := by
  have hi : (southRay (N:=N) c l).val<2*M := by dsimp [southRay]; omega
  simp only [starterActive,ite_eq_left hi,southRay_mod,southRay_div]
  have he : M-1-(M-1-c.val)=c.val := by omega
  rw [he]
lemma active_west (r : Fin N) (l : Fin 2) : starterActive p (westRay (M:=M) r l) ↔
    (p r.val).Occupied ⟨1-l.val,by omega⟩ := by
  have hi : ¬(westRay (M:=M) r l).val<2*M := by dsimp [westRay]; omega
  simp only [starterActive,ite_eq_right hi,westRay_mod,westRay_div,Nat.add_sub_cancel_left]

lemma southSlot_right (c : Fin M) (l : Fin 2) :
    southSlot hM hN c.isLt (by omega : 0<N) l=
      TurnStarter.right (width M N) (southRay c l) := by
  apply Fin.ext
  rw [southSlot_val]
  dsimp only [TurnStarter.right,southRay]
  omega
lemma westSlot_right (r : Fin N) (l : Fin 2) :
    westSlot hM hN (by omega : 0<M) r.isLt l=
      TurnStarter.right (width M N) (westRay r l) := by
  apply Fin.ext
  rw [westSlot_val]
  change width M N+2*(M-1-0+r.val)+2+l.val=width M N+(2*(M+r.val)+l.val)
  omega

lemma start_matches_south (c : Fin M) (l : Fin 2) :
    (startPairing (M:=M) (N:=N) p).Occupied (southSlot hM hN c.isLt (by omega : 0<N) l) ↔
      (p (c.val*N)).Occupied ⟨3-l.val,by omega⟩ := by
  rw [southSlot_right]
  exact (TurnStarter.occupied_right _ _ _).trans (active_south p c l)
lemma start_matches_west (r : Fin N) (l : Fin 2) :
    (startPairing (M:=M) (N:=N) p).Occupied (westSlot hM hN (by omega : 0<M) r.isLt l) ↔
      (p r.val).Occupied ⟨1-l.val,by omega⟩ := by
  rw [westSlot_right]
  exact (TurnStarter.occupied_right _ _ _).trans (active_west p r l)



lemma starter_physical (hm : InteriorMatches (M:=M) (N:=N) p q) :
    PhysicalMatches hM hN (startPairing p) p q :=
  ⟨hm.1,fun c hc=>start_matches_south hM hN p ⟨c,hc⟩,
    fun r hr=>start_matches_west hM hN p ⟨r,hr⟩,hm.2⟩

omit p q
lemma starter_arc_turn (i : Fin (width M N)) :
    Pairing.arcTurn (starterGauge M N) (TurnStarter.left (width M N) i)
      (TurnStarter.right (width M N) i)=0 := by
  have ho:=TurnStarter.left_lt_right (width M N) i i
  dsimp only [Pairing.arcTurn,Pairing.turnOrder]
  erw [ite_eq_left ho]
  unfold starterGauge TurnStarter.left TurnStarter.right width
  dsimp only
  have hi : i.val<2*(M+N) := i.isLt
  split_ifs <;> omega

include p q
lemma starter_edge {i : Fin (width M N)} (hi : starterActive p i) :
    edges hM hN (startPairing p) p q (.inl (TurnStarter.left (width M N) i))
      (.inl (TurnStarter.right (width M N) i)) :=
  lift_edge _ _ _ _ _ _ (Nat.zero_le (M*N))
    (show graph (startPairing p) (starterGauge M N) p q (position M N) (position_bound hM hN) 0
      (.inl (TurnStarter.left _ i)) (.inl (TurnStarter.right _ i)) from
        TurnStarter.across (width M N) (starterActive p) hi)
lemma starter_turn {i : Fin (width M N)} (hi : starterActive p i) :
    turns hM hN (startPairing p) p q (.inl (TurnStarter.left (width M N) i))
      (.inl (TurnStarter.right (width M N) i))=0 :=
  (lift_turn _ _ _ _ _ _ (Nat.zero_le (M*N))
    (show graph (startPairing p) (starterGauge M N) p q (position M N) (position_bound hM hN) 0
      (.inl (TurnStarter.left _ i)) (.inl (TurnStarter.right _ i)) from
        TurnStarter.across (width M N) (starterActive p) hi)).trans (starter_arc_turn i)

variable (hm : InteriorMatches (M:=M) (N:=N) p q)
include hm
lemma south_edge {c : Fin M} (l : Fin 2)
    (hi : (p (c.val*N)).Occupied ⟨3-l.val,by omega⟩) :
    edges hM hN (startPairing p) p q
      (.inl (southSlot hM hN c.isLt (by omega : 0<N) l))
      (cellNode c ⟨0,by omega⟩ (.inl ⟨3-l.val,by omega⟩)) := by
  have hh:=enter_edge hM hN (startPairing p) p q (starter_physical hM hN p q hm)
    (by simpa only [Nat.add_zero] using time_lt (M:=M) (N:=N) (c:=c.val) (r:=0) (by omega) c.isLt)
    ⟨l.val,by omega⟩ hi
  have he : Gate4.slot (position M N (c.val*N)) (position_bound hM hN _) ⟨l.val,by omega⟩=
      southSlot hM hN c.isLt (by omega : 0<N) l := rfl
  rw [he,south_initial] at hh
  exact hh
lemma south_turn {c : Fin M} (l : Fin 2)
    (hi : (p (c.val*N)).Occupied ⟨3-l.val,by omega⟩) :
    turns hM hN (startPairing p) p q
      (.inl (southSlot hM hN c.isLt (by omega : 0<N) l))
      (cellNode c ⟨0,by omega⟩ (.inl ⟨3-l.val,by omega⟩))=0 := by
  have hh:=enter_turn hM hN (startPairing p) p q (starter_physical hM hN p q hm)
    (by simpa only [Nat.add_zero] using time_lt (M:=M) (N:=N) (c:=c.val) (r:=0) (by omega) c.isLt)
    ⟨l.val,by omega⟩ hi
  have he : Gate4.slot (position M N (c.val*N)) (position_bound hM hN _) ⟨l.val,by omega⟩=
      southSlot hM hN c.isLt (by omega : 0<N) l := rfl
  rw [he,south_initial] at hh
  exact hh

end TurnRectangle

 

 


lemma TurnDisk.edgeTurn_reverse {n : ℕ} (D : TurnDisk n) (v w : D.Vertex) :
    D.edgeTurn w v = -D.edgeTurn v w := by
  induction D with
  | atom p g => exact Pairing.arcTurn_reverse g v w
  | insert D k hk p g ih =>
    rcases v with v|v <;> rcases w with w|w
    · exact ih v w
    · rfl
    · rfl
    · exact Pairing.arcTurn_reverse g v w
  | attach D E k hk ih ihE =>
    rcases v with v|v <;> rcases w with w|w
    · exact ih v w
    · rfl
    · rfl
    · exact ihE v w
  | sew D k hk ih =>
    change (if D.wiring w v then D.edgeTurn w v else 0)= -(if D.wiring v w then D.edgeTurn v w else 0)
    have hs : D.wiring w v ↔ D.wiring v w := ⟨fun h=>(TurnDisk.instSymmVertexWiring D).symm _ _ h,
      fun h=>(TurnDisk.instSymmVertexWiring D).symm _ _ h⟩
    simp only [hs]
    split_ifs
    · exact ih v w
    · rfl

lemma TurnNetwork.edgeTurn_reverse {n : ℕ} (p₀ : Pairing n) (g₀ : Fin n → ℤ)
    (p q : ℕ → Pairing 6) (k : ℕ → ℕ) (hk : ∀ t,k t+4≤n) (t : ℕ)
    (v w : TurnNetwork.Node n t) :
    TurnNetwork.edgeTurn p₀ g₀ p q k hk t w v= -TurnNetwork.edgeTurn p₀ g₀ p q k hk t v w :=
  TurnDisk.edgeTurn_reverse _ _ _

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_RibbonLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.HoneycombBranch
noncomputable section
open scoped Classical
open Diagram


lemma slot_injective (b : Bool) : Function.Injective (slot b) := by
  intro p q h
  cases b <;> fin_cases p <;> fin_cases q <;> simp_all [slot]

lemma lane_injective (b : Bool) {p q : Fin 3} {l m : Fin 2} :
    lane b p l=lane b q m ↔ p=q ∧ l=m := by
  constructor
  · intro h
    have hh:=congrArg Fin.val h
    change 2*(slot b p).val+l.val=2*(slot b q).val+m.val at hh
    have hs : slot b p=slot b q := Fin.ext (by have := l.isLt; have :=m.isLt; omega)
    exact ⟨slot_injective b hs,Fin.ext (by have :=l.isLt; have :=m.isLt; omega)⟩
  · rintro ⟨rfl,rfl⟩; rfl

lemma local_turn (b : Bool) (p : Fin 3) (a : Bool) :
    Pairing.arcTurn (localGauge b) (lane b p 0) (lane b (outgoing p a) 1)=sign a := by
  cases b <;> cases a <;> fin_cases p <;> decide

end

 

 

noncomputable section
open scoped Classical
open Diagram FiniteBranchTree


lemma passes_shift (s : State) (l : List Bool) :
    s::(passes s l).map (fun x=>(neighbor x.1.1 x.2,x.2)) =
      (passes s l).map Prod.fst ++ [terminal next s l] := by
  induction l generalizing s with
  | nil=>rfl
  | cons b l ih=>
    simp only [passes,List.map_cons,List.cons_append,terminal,List.cons.injEq,true_and]
    exact ih (next s b)

lemma passes_mem_vertex {s : State} {l : List Bool} {v : Vertex} {p q : Fin 3}
    (h : ((v,p),q)∈passes s l) : v∈visited Prod.fst next s l := by
  rw [←passes_vertices]
  exact List.mem_map.mpr ⟨((v,p),q),h,rfl⟩

lemma routes_cons (s : State) (b : Bool) (l : List Bool) (v : Vertex) :
    routes s (b::l) v=(if v=s.1 then {(s.2,outgoing s.2 b)} else ∅) ∪ routes (next s b) l v := by
  rcases s with ⟨w,p⟩
  ext ⟨i,j⟩
  simp only [mem_routes,passes_cons,List.mem_cons,Prod.mk.injEq,Finset.mem_union]
  split_ifs <;> simp_all

lemma routes_empty_of_notMem {s : State} {l : List Bool} {v : Vertex}
    (h : v∉visited Prod.fst next s l) : routes s l v=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact h (passes_mem_vertex ((mem_routes _ _ _ _).mp hx))

lemma routes_singleton_of_nodup {s : State} {l : List Bool}
    (hn : (visited Prod.fst next s l).Nodup) (v : Vertex) :
    routes s l v=∅ ∨ ∃ p q, q≠p ∧ routes s l v={(p,q)} := by
  induction l generalizing s with
  | nil=>exact Or.inl (routes_nil _ _)
  | cons b l ih=>
    have hn':=(List.nodup_cons.mp hn)
    rw [routes_cons]
    by_cases hv : v=s.1
    · subst v
      rw [ite_eq_left rfl,routes_empty_of_notMem hn'.1,Finset.union_empty]
      exact Or.inr ⟨s.2,outgoing s.2 b,outgoing_ne _ _,rfl⟩
    · rw [ite_eq_right hv,Finset.empty_union]
      exact ih hn'.2


lemma ribbonArcs_empty (b : Bool) : ribbonArcs b ∅=∅ := by simp [ribbonArcs]

lemma ribbon_singleton (b : Bool) (p q : Fin 3) : IsPairing (ribbonArcs b {(p,q)}) := by
  cases b <;> fin_cases p <;> fin_cases q <;>
    simp [IsPairing,ribbonArcs,Pairing.orderedEdge,lane,slot]

lemma ribbonSimple_of_nodup {s : State} {l : List Bool}
    (hn : (visited Prod.fst next s l).Nodup) : RibbonSimple s l := by
  intro v
  rcases routes_singleton_of_nodup hn v with he|⟨p,q,_,he⟩
  · rw [he,ribbonArcs_empty]; exact (empty 6).property
  · rw [he]; exact ribbon_singleton _ _ _

end

 

 

noncomputable section
open scoped Classical
open Diagram Diagram.TurnNetwork Diagram.TurnDisk
namespace RibbonRectangle
section Geometry

variable (L : ℤ) (M N : ℕ)

variable {L M N}

lemma vertex_col_row {v : Vertex} (h : Inside L M N v) : vertex L M N (col h) (row h) v.2.2=v := by
  dsimp [vertex,col,row]
  congr 1
  · dsimp [Inside] at h; omega
  · apply Prod.ext
    · dsimp [Inside] at h; omega
    · rfl

variable (L M N) (F : Vertex → Pairing 6)

lemma up_time (c : Fin M) (r : Fin N) : up L N F (c.val*N+r.val)=F (vertex L M N c r true) := by
  simp only [up,vertex]
  congr 2
  · rw [Nat.mul_comm c.val N,Nat.mul_add_div (by have :=r.isLt; omega : 0<N),Nat.div_eq_of_lt r.isLt,Nat.add_zero]
  · rw [Nat.mul_comm c.val N,Nat.mul_add_mod,Nat.mod_eq_of_lt r.isLt]
lemma down_time (c : Fin M) (r : Fin N) : down L N F (c.val*N+r.val)=F (vertex L M N c r false) := by
  simp only [down,vertex]
  congr 2
  · rw [Nat.mul_comm c.val N,Nat.mul_add_div (by have :=r.isLt; omega : 0<N),Nat.div_eq_of_lt r.isLt,Nat.add_zero]
  · rw [Nat.mul_comm c.val N,Nat.mul_add_mod,Nat.mod_eq_of_lt r.isLt]

variable {L M N F}

lemma at_vertex (c : Fin M) (r : Fin N) (b : Bool) (i : Fin 6) :
    node L M N (vertex_inside L M N c r b) i=
      TurnRectangle.cellNode c r (if b then .inl i else .inr i) := by
  unfold node
  rw [col_vertex,row_vertex]
  rfl

variable (hM : 1≤M) (hN : 1≤N) (F : Vertex → Pairing 6)

lemma arc_edge {v : Vertex} (h : Inside L M N v) {i j : Fin 6} (hij : (F v).Adj i j) :
    graph (L:=L) hM hN F (node L M N h i) (node L M N h j) := by
  obtain ⟨c,r,b,rfl⟩ : ∃ c r b,v=vertex L M N c r b :=
    ⟨col h,row h,v.2.2,(vertex_col_row h).symm⟩
  cases b
  · rw [at_vertex,at_vertex]
    apply TurnRectangle.down_edge hM hN (start (L:=L) F) (up L N F) (down L N F)
    rwa [down_time]
  · rw [at_vertex,at_vertex]
    apply TurnRectangle.up_edge hM hN (start (L:=L) F) (up L N F) (down L N F)
    rwa [up_time]

lemma arc_turn {v : Vertex} (h : Inside L M N v) {i j : Fin 6} (hij : (F v).Adj i j) :
    turnEdge (L:=L) hM hN F (node L M N h i) (node L M N h j)=Pairing.arcTurn (localGauge v.2.2) i j := by
  obtain ⟨c,r,b,rfl⟩ : ∃ c r b,v=vertex L M N c r b :=
    ⟨col h,row h,v.2.2,(vertex_col_row h).symm⟩
  cases b
  · rw [at_vertex,at_vertex]
    apply TurnRectangle.down_turn hM hN (start (L:=L) F) (up L N F) (down L N F)
    rwa [down_time]
  · rw [at_vertex,at_vertex]
    apply TurnRectangle.up_turn hM hN (start (L:=L) F) (up L N F) (down L N F)
    rwa [up_time]


lemma interior_matches (hm : Matches (L:=L) (M:=M) (N:=N) F) :
    TurnRectangle.InteriorMatches (M:=M) (N:=N) (up L N F) (down L N F) := by
  refine ⟨?_,?_,?_⟩
  · intro c r hc hr l
    have hh:=hm (vertex L M N ⟨c,hc⟩ ⟨r,hr⟩ true) 2
      (vertex_inside _ _ _ _ _ _) (by simpa [neighbor,vertex] using
          (vertex_inside L M N ⟨c,hc⟩ ⟨r,hr⟩ false)) l
    rw [up_time L M N F ⟨c,hc⟩ ⟨r,hr⟩,down_time L M N F ⟨c,hc⟩ ⟨r,hr⟩]
    fin_cases l <;> simpa [neighbor,lane,slot,vertex] using hh
  · intro c r hc hr hr0 l
    have hv:=vertex_inside L M N (⟨c,hc⟩:Fin M) (⟨r,hr⟩:Fin N) true
    have he : neighbor (vertex L M N ⟨c,hc⟩ ⟨r,hr⟩ true) 0=
        vertex L M N ⟨c,hc⟩ ⟨r-1,by omega⟩ false := by
      dsimp [neighbor,vertex]; congr 2; omega
    have hh:=hm _ 0 hv (by rw [he]; exact vertex_inside _ _ _ _ _ _) (1-l)
    rw [he] at hh
    rw [down_time L M N F ⟨c,hc⟩ ⟨r-1,by omega⟩,up_time L M N F ⟨c,hc⟩ ⟨r,hr⟩]
    fin_cases l <;> simpa [lane,slot,vertex] using hh.symm
  · intro c r hc hc0 hr l
    have hv:=vertex_inside L M N (⟨c,hc⟩:Fin M) (⟨r,hr⟩:Fin N) true
    have he : neighbor (vertex L M N ⟨c,hc⟩ ⟨r,hr⟩ true) 1=
        vertex L M N ⟨c-1,by omega⟩ ⟨r,hr⟩ false := by
      dsimp [neighbor,vertex]; congr 2; omega
    have hh:=hm _ 1 hv (by rw [he]; exact vertex_inside _ _ _ _ _ _) (1-l)
    rw [he] at hh
    rw [down_time L M N F ⟨c-1,by omega⟩ ⟨r,hr⟩,up_time L M N F ⟨c,hc⟩ ⟨r,hr⟩]
    fin_cases l <;> simpa [lane,slot,vertex] using hh.symm

lemma physical_matches (hm : Matches (L:=L) (M:=M) (N:=N) F) :
    TurnRectangle.PhysicalMatches hM hN (start (L:=L) F) (up L N F) (down L N F) :=
  TurnRectangle.starter_physical hM hN _ _ (interior_matches F hm)

end Geometry

 

 


variable {L : ℤ} {M N : ℕ}

lemma node_eq {v w : Vertex} (hv : Inside L M N v) (hw : Inside L M N w)
    (he : v=w) (i : Fin 6) : node L M N hv i=node L M N hw i := by
  subst w; rfl

lemma node_of_vertex {v : Vertex} (h : Inside L M N v) {c : Fin M} {r : Fin N} {b : Bool}
    (he : v=vertex L M N c r b) (i : Fin 6) :
    node L M N h i=TurnRectangle.cellNode c r (if b then .inl i else .inr i) := by
  subst v
  exact at_vertex c r b i

variable (hM : 1≤M) (hN : 1≤N) (F : Vertex → Pairing 6)
  (hm : Matches (L:=L) (M:=M) (N:=N) F)
include hm

lemma up_wire (c : Fin M) (r : Fin N) (p : Fin 3) (l : Fin 2)
    (hw : Inside L M N (neighbor (vertex L M N c r true) p))
    (hi : (F (vertex L M N c r true)).Occupied (lane true p l)) :
    graph (L:=L) hM hN F
      (node L M N (vertex_inside L M N c r true) (lane true p l))
      (node L M N hw (lane false p (1-l))) ∧
    turnEdge (L:=L) hM hN F
      (node L M N (vertex_inside L M N c r true) (lane true p l))
      (node L M N hw (lane false p (1-l)))=0 := by
  have hm':=physical_matches hM hN F hm
  fin_cases p
  · have hr : 0 < r.val := by dsimp [Inside,neighbor,vertex] at hw; omega
    have he : neighbor (vertex L M N c r true) 0=
        vertex L M N c ⟨r.val-1,by omega⟩ false := by
      dsimp [neighbor,vertex]; congr 2; omega
    rw [at_vertex,node_of_vertex hw he]
    have hh : (up L N F (c.val*N+r.val)).Occupied ⟨3-(1-l).val,by omega⟩ := by
      rw [up_time]
      fin_cases l <;> exact hi
    have hE:=TurnRectangle.vertical_edge hM hN (start (L:=L) F) (up L N F) (down L N F) hm' hr (1-l) hh
    have hT:=TurnRectangle.vertical_turn hM hN (start (L:=L) F) (up L N F) (down L N F) hm' hr (1-l) hh
    fin_cases l
    · refine ⟨symm hE,?_⟩
      rw [turnEdge,TurnRectangle.turns,TurnNetwork.edgeTurn_reverse]
      exact congrArg Neg.neg hT
    · refine ⟨symm hE,?_⟩
      rw [turnEdge,TurnRectangle.turns,TurnNetwork.edgeTurn_reverse]
      exact congrArg Neg.neg hT
  · have hc : 0 < c.val := by dsimp [Inside,neighbor,vertex] at hw; omega
    have he : neighbor (vertex L M N c r true) 1=
        vertex L M N ⟨c.val-1,by omega⟩ r false := by
      dsimp [neighbor,vertex]; congr 2; omega
    rw [at_vertex,node_of_vertex hw he]
    have hh : (up L N F (c.val*N+r.val)).Occupied ⟨1-(1-l).val,by omega⟩ := by
      rw [up_time]
      fin_cases l <;> exact hi
    have hE:=TurnRectangle.horizontal_edge hM hN (start (L:=L) F) (up L N F) (down L N F) hm' hc (1-l) hh
    have hT:=TurnRectangle.horizontal_turn hM hN (start (L:=L) F) (up L N F) (down L N F) hm' hc (1-l) hh
    fin_cases l
    · refine ⟨symm hE,?_⟩
      rw [turnEdge,TurnRectangle.turns,TurnNetwork.edgeTurn_reverse]
      exact congrArg Neg.neg hT
    · refine ⟨symm hE,?_⟩
      rw [turnEdge,TurnRectangle.turns,TurnNetwork.edgeTurn_reverse]
      exact congrArg Neg.neg hT
  · have he : neighbor (vertex L M N c r true) 2=vertex L M N c r false := rfl
    rw [at_vertex,node_of_vertex hw he]
    have hh : (up L N F (c.val*N+r.val)).Occupied ⟨4+l.val,by omega⟩ := by
      rw [up_time]
      exact hi
    have hE:=TurnRectangle.diagonal_edge hM hN (start (L:=L) F) (up L N F) (down L N F) hm' l hh
    have hT:=TurnRectangle.diagonal_turn hM hN (start (L:=L) F) (up L N F) (down L N F) hm' l hh
    fin_cases l <;> exact ⟨hE,hT⟩

lemma wire {v : Vertex} (hv : Inside L M N v) (p : Fin 3) (l : Fin 2)
    (hw : Inside L M N (neighbor v p))
    (hi : (F v).Occupied (lane v.2.2 p l)) :
    graph (L:=L) hM hN F (node L M N hv (lane v.2.2 p l))
      (node L M N hw (lane (!v.2.2) p (1-l))) ∧
    turnEdge (L:=L) hM hN F (node L M N hv (lane v.2.2 p l))
      (node L M N hw (lane (!v.2.2) p (1-l)))=0 := by
  let w:=neighbor v p
  have hb : w.2.2= !v.2.2 := by
    cases he : v.2.2 <;> simp [w,neighbor,he] <;> split_ifs <;> rfl
  have hww : neighbor w p=v := neighbor_reverse v p
  cases hvb : v.2.2
  · have hwb : w.2.2=true := by simp [hb,hvb]
    have hwv : vertex L M N (col hw) (row hw) true=w := by
      rw [←hwb]
      exact vertex_col_row hw
    have hi' : (F w).Occupied (lane true p (1-l)) := by
      rw [←hwb,hb]
      exact (hm v p hv hw l).mp hi
    have hww' : neighbor (vertex L M N (col hw) (row hw) true) p=v := by rw [hwv,hww]
    have hh:=up_wire hM hN F hm (col hw) (row hw) p (1-l)
      (by rw [hww']; exact hv) (by rwa [hwv])
    have hn₁ (i : Fin 6) : node L M N (vertex_inside L M N (col hw) (row hw) true) i=
        node L M N hw i := by rw [at_vertex,node_of_vertex hw hwv.symm]
    have hn₂ (i : Fin 6) (hx : Inside L M N (neighbor (vertex L M N (col hw) (row hw) true) p)) :
        node L M N hx i=node L M N hv i := by
      exact node_eq hx hv hww' i
    rw [hn₁,hn₂] at hh
    simp only [Bool.not_false]
    have hll : 1-(1-l)=l := by fin_cases l <;> decide
    rw [hll] at hh
    refine ⟨symm hh.1,?_⟩
    rw [turnEdge,TurnRectangle.turns,TurnNetwork.edgeTurn_reverse]
    exact congrArg Neg.neg hh.2
  · have hvv : v=vertex L M N (col hv) (row hv) true := by
      rw [←hvb]
      exact (vertex_col_row hv).symm
    have hw' : Inside L M N (neighbor (vertex L M N (col hv) (row hv) true) p) := by rwa [←hvv]
    have hh:=up_wire hM hN F hm (col hv) (row hv) p l hw' (by rwa [←hvv,←hvb])
    rw [node_eq _ hv hvv.symm, node_eq _ hw (congrArg (fun x=>neighbor x p) hvv.symm)] at hh
    simpa only [hvb,Bool.not_true] using hh

end RibbonRectangle
end

 

 

noncomputable section
open scoped Classical
open Diagram FiniteBranchTree


lemma ribbon_arc {s : State} {l : List Bool} (h : RibbonSimple s l) {v : Vertex} {p q : Fin 3}
    (hp : ((v,p),q)∈passes s l) : (ribbon h v).Adj (lane v.2.2 p 0) (lane v.2.2 q 1) := by
  have hm : Pairing.orderedEdge (lane v.2.2 p 0) (lane v.2.2 q 1)∈(ribbon h v).val :=
    Finset.mem_image.mpr ⟨(p,q),(mem_routes _ _ _ _).mpr hp,rfl⟩
  unfold Pairing.orderedEdge at hm
  rcases le_total (lane v.2.2 p 0) (lane v.2.2 q 1) with he|he
  · exact Or.inl (by simpa only [min_eq_left he,max_eq_right he] using hm)
  · exact Or.inr (by simpa only [min_eq_right he,max_eq_left he] using hm)

lemma ribbon_occupied {s : State} {l : List Bool} (h : RibbonSimple s l) (v : Vertex) (i : Fin 6) :
    (ribbon h v).Occupied i ↔ ∃ p q, ((v,p),q)∈passes s l ∧
      (i=lane v.2.2 p 0 ∨ i=lane v.2.2 q 1) := by
  constructor
  · rintro ⟨j,hj|hj⟩ <;> obtain ⟨⟨p,q⟩,hp,he⟩:=Finset.mem_image.mp hj
    · refine ⟨p,q,(mem_routes _ _ _ _).mp hp,?_⟩
      have hi:=congrArg Prod.fst he
      change min (lane v.2.2 p 0) (lane v.2.2 q 1)=i at hi
      rcases le_total (lane v.2.2 p 0) (lane v.2.2 q 1) with hh|hh
      · exact Or.inl (hi.symm.trans (min_eq_left hh))
      · exact Or.inr (hi.symm.trans (min_eq_right hh))
    · refine ⟨p,q,(mem_routes _ _ _ _).mp hp,?_⟩
      have hi:=congrArg Prod.snd he
      change max (lane v.2.2 p 0) (lane v.2.2 q 1)=i at hi
      rcases le_total (lane v.2.2 p 0) (lane v.2.2 q 1) with hh|hh
      · exact Or.inr (hi.symm.trans (max_eq_right hh))
      · exact Or.inl (hi.symm.trans (max_eq_left hh))
  · rintro ⟨p,q,hp,rfl|rfl⟩
    · exact ⟨_,ribbon_arc h hp⟩
    · exact ⟨_,(ribbon_arc h hp).symm⟩

lemma ribbon_incoming {s : State} {l : List Bool} (h : RibbonSimple s l) (v : Vertex) (p : Fin 3) :
    (ribbon h v).Occupied (lane v.2.2 p 0) ↔ ∃ q, ((v,p),q)∈passes s l := by
  rw [ribbon_occupied]
  simp only [lane_injective,Fin.zero_ne_one,and_false,or_false,and_true]
  constructor
  · rintro ⟨p',q,hp,rfl⟩; exact ⟨q,hp⟩
  · rintro ⟨q,hq⟩; exact ⟨p,q,hq,rfl⟩

lemma ribbon_outgoing {s : State} {l : List Bool} (h : RibbonSimple s l) (v : Vertex) (p : Fin 3) :
    (ribbon h v).Occupied (lane v.2.2 p 1) ↔ ∃ q, ((v,q),p)∈passes s l := by
  rw [ribbon_occupied]
  simp only [lane_injective,(show (1:Fin 2)≠0 from by decide),and_false,false_or,and_true]
  constructor
  · rintro ⟨p',q,hp,rfl⟩; exact ⟨p',hp⟩
  · rintro ⟨q,hq⟩; exact ⟨q,p,hq,rfl⟩

lemma route_shift_iff (s : State) (l : List Bool) (v : Vertex) (p : Fin 3) :
    ((v,p)=s ∨ ∃ q,((neighbor v p,q),p)∈passes s l) ↔
      (∃q,((v,p),q)∈passes s l) ∨ (v,p)=terminal next s l := by
  have hs:=congrArg (fun xs : List State => (v,p)∈xs) (passes_shift s l)
  simp only [List.mem_cons,List.mem_append,List.mem_map] at hs
  have ha : (∃ a∈passes s l,(neighbor a.1.1 a.2,a.2)=(v,p)) ↔
      ∃q,((neighbor v p,q),p)∈passes s l := by
    constructor
    · rintro ⟨⟨⟨w,q⟩,r⟩,hm,he⟩
      obtain ⟨hw,hp⟩:=Prod.mk.inj he
      change r=p at hp
      subst r
      have hv := congrArg (fun z=>neighbor z p) hw
      rw [neighbor_reverse] at hv
      change w=neighbor v p at hv
      subst w
      exact ⟨q,hm⟩
    · rintro ⟨q,hq⟩
      exact ⟨((neighbor v p,q),p),hq,by simp only [neighbor_reverse]⟩
  have hb : (∃a∈passes s l,a.1=(v,p)) ↔ ∃q,((v,p),q)∈passes s l := by
    constructor
    · rintro ⟨⟨w,q⟩,hm,he⟩; change w=(v,p) at he; subst w; exact ⟨q,hm⟩
    · rintro ⟨q,hq⟩; exact ⟨((v,p),q),hq,rfl⟩
  simpa only [ha,hb,List.not_mem_nil,or_false] using (Iff.of_eq hs)

lemma neighbor_bool (v : Vertex) (p : Fin 3) : (neighbor v p).2.2= !v.2.2 := by
  unfold neighbor
  split_ifs <;> simp_all

namespace RibbonRectangle
variable {L : ℤ} {M N : ℕ} {s : State} {l : List Bool}

lemma route_interior_match
    (hs : ¬Inside L M N (back s).1) (ht : ¬Inside L M N (terminal next s l).1)
    {v : Vertex} {p : Fin 3} (hv : Inside L M N v) (hw : Inside L M N (neighbor v p)) :
    (∃q,((v,p),q)∈passes s l) ↔ (∃q,((neighbor v p,q),p)∈passes s l) := by
  have h₀ : (v,p)≠s := by
    intro he
    have hh:=congrArg back he
    exact hs (hh ▸ hw)
  have h₁ : (v,p)≠terminal next s l := by
    intro he
    exact ht (congrArg Prod.fst he ▸ hv)
  have hh:=route_shift_iff s l v p
  simpa only [h₀,h₁,false_or,or_false] using hh.symm

lemma ribbon_matches (h : RibbonSimple s l)
    (hs : ¬Inside L M N (back s).1) (ht : ¬Inside L M N (terminal next s l).1) :
    Matches (L:=L) (M:=M) (N:=N) (ribbon h) := by
  intro v p hv hw j
  rw [←neighbor_bool v p]
  fin_cases j
  · change (ribbon h v).Occupied (lane v.2.2 p 0) ↔
      (ribbon h (neighbor v p)).Occupied (lane (neighbor v p).2.2 p 1)
    rw [ribbon_incoming,ribbon_outgoing]
    exact route_interior_match hs ht hv hw
  · change (ribbon h v).Occupied (lane v.2.2 p 1) ↔
      (ribbon h (neighbor v p)).Occupied (lane (neighbor v p).2.2 p 0)
    rw [ribbon_outgoing,ribbon_incoming]
    have hh:=route_interior_match (p:=p) hs ht hw (by simpa only [neighbor_reverse] using hv)
    simpa only [neighbor_reverse] using hh.symm

end RibbonRectangle
end
end CriticalStrip.HoneycombBranch

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_RibbonWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.HoneycombBranch
noncomputable section
open scoped Classical
open Diagram FiniteBranchTree
namespace RibbonRectangle

variable {L : ℤ} {M N : ℕ} (hM : 1≤M) (hN : 1≤N) (F : Vertex → Pairing 6)
  (hm : Matches (L:=L) (M:=M) (N:=N) F)
include hm

lemma route_reach (s : State) (l : List Bool) (hs : Inside L M N s.1)
    (hI : ∀x∈passes s l,Inside L M N x.1.1)
    (hA : ∀x∈passes s l,(F x.1.1).Adj (lane x.1.1.2.2 x.1.2 0) (lane x.1.1.2.2 x.2 1))
    {v : Vertex} {p q : Fin 3} (hp : ((v,p),q)∈passes s l) :
    Relation.ReflTransGen (graph (L:=L) hM hN F)
      (node L M N hs (lane s.1.2.2 s.2 0))
      (node L M N (hI _ hp) (lane v.2.2 p 0)) ∧
    Relation.ReflTransGen (graph (L:=L) hM hN F)
      (node L M N hs (lane s.1.2.2 s.2 0))
      (node L M N (hI _ hp) (lane v.2.2 q 1)) := by
  induction l generalizing s with
  | nil => simp only [passes,List.not_mem_nil] at hp
  | cons b l ih =>
    have ha:=hA _ (List.mem_cons_self)
    have ea:=arc_edge hM hN F hs ha
    rcases List.mem_cons.mp hp with he|hp
    · have he₁:=congrArg (fun z : State × Fin 3=>z.1.1) he
      have he₂:=congrArg (fun z : State × Fin 3=>z.1.2) he
      have he₃:=congrArg (fun z : State × Fin 3=>z.2) he
      change v=s.1 at he₁; change p=s.2 at he₂; change q=outgoing s.2 b at he₃
      subst v p q
      exact ⟨.refl,.single ea⟩
    · cases l with
      | nil => simp only [passes,List.not_mem_nil] at hp
      | cons c l =>
        have hs' : Inside L M N (next s b).1 := hI _ (by exact List.mem_cons_of_mem _ List.mem_cons_self)
        have ew:= (wire hM hN F hm hs (outgoing s.2 b) 1 hs' ⟨_,ha.symm⟩).1
        have heB : (!s.1.2.2)=(next s b).1.2.2 := (neighbor_bool s.1 (outgoing s.2 b)).symm
        have heL : (1-(1:Fin 2))=0 := rfl
        rw [heB,heL] at ew
        obtain ⟨hi,ho⟩:=ih (next s b) hs'
          (fun x hx=>hI x (List.mem_cons_of_mem _ hx))
          (fun x hx=>hA x (List.mem_cons_of_mem _ hx)) hp
        exact ⟨(Relation.ReflTransGen.single ea).trans ((Relation.ReflTransGen.single ew).trans hi),
          (Relation.ReflTransGen.single ea).trans ((Relation.ReflTransGen.single ew).trans ho)⟩

lemma route_turn (s : State) (l : List Bool) (hl : l≠[]) (hs : Inside L M N s.1)
    (hI : ∀x∈passes s l,Inside L M N x.1.1)
    (hA : ∀x∈passes s l,(F x.1.1).Adj (lane x.1.1.2.2 x.1.2 0) (lane x.1.1.2.2 x.2 1))
    (P : Diagram.TurnNetwork.Node (Diagram.TurnRectangle.ports M N) (M*N) → ℤ)
    (hP : ∀v w, graph (L:=L) hM hN F v w → P w-P v=turnEdge (L:=L) hM hN F v w) :
    P (node L M N (last_inside s l hl hI)
      (lane (back (terminal next s l)).1.2.2 (terminal next s l).2 1)) -
    P (node L M N hs (lane s.1.2.2 s.2 0))=turn l := by
  induction l generalizing s with
  | nil => exact (hl rfl).elim
  | cons b l ih =>
    have ha:=hA _ List.mem_cons_self
    have hp:=hP _ _ (arc_edge hM hN F hs ha)
    rw [arc_turn hM hN F hs ha,local_turn] at hp
    cases l with
    | nil =>
      simp only [terminal,back_next]
      simpa only [turn,add_zero,next] using hp
    | cons c l =>
      have hs' : Inside L M N (next s b).1 := hI _ (List.mem_cons_of_mem _ List.mem_cons_self)
      have ew:= wire hM hN F hm hs (outgoing s.2 b) 1 hs' ⟨_,ha.symm⟩
      have heB : (!s.1.2.2)=(next s b).1.2.2 := (neighbor_bool s.1 (outgoing s.2 b)).symm
      have heL : (1-(1:Fin 2))=0 := rfl
      rw [heB,heL] at ew
      have hw:= (hP _ _ ew.1).trans ew.2
      have ht:=ih (next s b) (by simp)
        hs' (fun x hx=>hI x (List.mem_cons_of_mem _ hx))
        (fun x hx=>hA x (List.mem_cons_of_mem _ hx))
      change _=sign b+turn (c::l)
      change _-P (node L M N hs' (lane (next s b).1.2.2 (next s b).2 0))=turn (c::l) at ht
      change P (node L M N hs' (lane (next s b).1.2.2 (next s b).2 0))-_ =0 at hw
      dsimp only [terminal] at ht ⊢
      dsimp only [next] at hw ht ⊢
      dsimp only at hp
      omega

end RibbonRectangle
end

 

 

noncomputable section
open scoped Classical
open Diagram Diagram.TurnNetwork Diagram.TurnDisk FiniteBranchTree
namespace RibbonRectangle

variable {L : ℤ} {M N : ℕ}

section BoundaryConnection
lemma node_occupied (F : Vertex → Pairing 6) {v : Vertex} (h : Inside L M N v) (i : Fin 6) :
    TurnNetwork.Occupied (start (L:=L) F) (up L N F) (down L N F) (M*N) (node L M N h i) ↔
      (F v).Occupied i := by
  obtain ⟨c,r,b,rfl⟩ : ∃ c r b,v=vertex L M N c r b :=
    ⟨col h,row h,v.2.2,(vertex_col_row h).symm⟩
  rw [at_vertex]
  cases b
  · change (down L N F (c.val*N+r.val)).Occupied i ↔ _
    rw [down_time]
  · change (up L N F (c.val*N+r.val)).Occupied i ↔ _
    rw [up_time]

lemma cover_node (hN : 1≤N) (x : Node (TurnRectangle.ports M N) (M*N)) :
    (∃i,x=.inl i) ∨ ∃ (v : Vertex) (h : Inside L M N v),∃i, x=node L M N h i := by
  rcases x with i|⟨t,z⟩
  · exact Or.inl ⟨i,rfl⟩
  · have hc : t.val/N<M := (Nat.div_lt_iff_lt_mul (by omega)).mpr t.isLt
    have hr : t.val%N<N := Nat.mod_lt _ (by omega)
    let c : Fin M:=⟨t.val/N,hc⟩
    let r : Fin N:=⟨t.val%N,hr⟩
    have he : (⟨c.val*N+r.val,TurnRectangle.time_lt r.isLt c.isLt⟩:Fin (M*N))=t := by
      apply Fin.ext
      change (t.val/N)*N+t.val%N=t.val
      simpa only [Nat.mul_comm] using Nat.div_add_mod t.val N
    rcases z with i|i
    · refine Or.inr ⟨vertex L M N c r true,vertex_inside _ _ _ _ _ _,i,?_⟩
      rw [at_vertex]
      change Sum.inr (t,Sum.inl i)=Sum.inr (⟨c.val*N+r.val,_⟩,Sum.inl i)
      rw [he]
    · refine Or.inr ⟨vertex L M N c r false,vertex_inside _ _ _ _ _ _,i,?_⟩
      rw [at_vertex]
      change Sum.inr (t,Sum.inr i)=Sum.inr (⟨c.val*N+r.val,_⟩,Sum.inr i)
      rw [he]

variable (hM : 1≤M) (hN : 1≤N)

lemma starter_drains (F : Vertex → Pairing 6) (i : Fin (TurnRectangle.ports M N))
    (hi : (start (L:=L) F).Occupied i) :
    ∃j,Relation.ReflTransGen (graph (L:=L) hM hN F) (.inl i) (boundary (L:=L) hM hN F j) := by
  have hb (j : Fin (TurnRectangle.width M N)) : boundary (L:=L) hM hN F
      (TurnStarter.left (TurnRectangle.width M N) j)=.inl (TurnStarter.left (TurnRectangle.width M N) j) :=
    TurnRectangle.retained_boundary hM hN (start (L:=L) F) (TurnRectangle.starterGauge M N)
      (up L N F) (down L N F) (M*N) _ (by change TurnRectangle.width M N-1-j.val<TurnRectangle.width M N; omega)
  rcases TurnStarter.cover (TurnRectangle.width M N) i with ⟨j,rfl⟩|⟨j,rfl⟩
  · refine ⟨TurnStarter.left _ j,?_⟩
    rw [hb]
  · have hActive := (TurnStarter.occupied_right _ _ _).mp hi
    refine ⟨TurnStarter.left _ j,?_⟩
    rw [hb]
    exact .single (symm (TurnRectangle.starter_edge hM hN (up L N F) (down L N F) hActive))

lemma ribbon_drains (s : State) (l : List Bool) (hr : RibbonSimple s l)
    (hs : Inside L M N s.1) (hI : ∀x∈passes s l,Inside L M N x.1.1)
    (hm : Matches (L:=L) (M:=M) (N:=N) (ribbon hr))
    (i₀ : Fin (TurnRectangle.ports M N))
    (h₀ : Relation.ReflTransGen (graph (L:=L) hM hN (ribbon hr))
      (boundary (L:=L) hM hN (ribbon hr) i₀) (node L M N hs (lane s.1.2.2 s.2 0))) :
    Graph.DrainsBoundary (graph (L:=L) hM hN (ribbon hr)) (boundary (L:=L) hM hN (ribbon hr)) := by
  have hm':=TurnRectangle.physical_matches hM hN (start (L:=L) (ribbon hr))
    (up L N (ribbon hr)) (down L N (ribbon hr)) (physical_matches hM hN (ribbon hr) hm)
  intro v w hvw
  have ho := (TurnNetwork.occupied_iff_used _ _ _ _ _ _ (M*N) hm' v).mp ⟨w,hvw⟩
  rcases cover_node (L:=L) hN v with ⟨i,rfl⟩|⟨u,hu,j,rfl⟩
  · exact starter_drains hM hN (ribbon hr) i ho
  · rw [node_occupied,ribbon_occupied] at ho
    obtain ⟨p,q,hp,hj⟩:=ho
    obtain ⟨hri,hro⟩:=route_reach hM hN (ribbon hr) hm s l hs hI
      (fun x hx=>ribbon_arc hr hx) hp
    refine ⟨i₀,?_⟩
    rcases hj with rfl|rfl
    · exact ConnectivityCertificate.reach_symm ⟨fun _ _ hedge=>symm hedge⟩ (h₀.trans hri)
    · exact ConnectivityCertificate.reach_symm ⟨fun _ _ hedge=>symm hedge⟩ (h₀.trans hro)

end BoundaryConnection






lemma bottomIndex_val (c : Fin M) (l : Fin 2) :
    (bottomIndex (N:=N) c l).val=2*N+2*c.val+l.val := by
  have hl : (1-l).val=1-l.val := by fin_cases l <;> decide
  dsimp [bottomIndex,TurnStarter.left,TurnRectangle.southRay,TurnRectangle.width]
  rw [hl]
  omega

lemma bottomIndex_lt (c : Fin M) (l : Fin 2) : (bottomIndex (N:=N) c l).val<TurnRectangle.width M N := by
  rw [bottomIndex_val]
  dsimp [TurnRectangle.width]
  omega

variable (hM : 1≤M) (hN : 1≤N) (F : Vertex → Pairing 6)

lemma bottom_boundary (c : Fin M) (l : Fin 2) :
    boundary (L:=L) hM hN F (bottomIndex c l)=.inl (bottomIndex c l) := by
  exact TurnRectangle.retained_boundary _ _ _ _ _ _ _ _ (bottomIndex_lt c l)

lemma bottom_gauge (c : Fin M) (l : Fin 2) : gauge (L:=L) hM hN F (bottomIndex c l)= -3 := by
  rw [gauge,←TurnNetwork.namedGauge_boundary]
  change namedGauge (TurnRectangle.starterGauge M N) (M*N) (boundary (L:=L) hM hN F (bottomIndex c l))= -3
  rw [bottom_boundary]
  change TurnRectangle.starterGauge M N (bottomIndex c l)= -3
  unfold TurnRectangle.starterGauge
  rw [bottomIndex_val]
  have hi:=bottomIndex_lt (N:=N) c l
  rw [bottomIndex_val] at hi
  split_ifs <;> omega

lemma top_boundary (c : Fin M) (l : Fin 2) :
    boundary (L:=L) hM hN F (TurnRectangle.northSlot hM hN c.isLt l)=
      node L M N (vertex_inside L M N c ⟨N-1,by omega⟩ false) (lane false 0 l) := by
  rw [boundary,TurnRectangle.north_boundary,at_vertex]
  rfl

lemma top_gauge (c : Fin M) (l : Fin 2) :
    gauge (L:=L) hM hN F (TurnRectangle.northSlot hM hN c.isLt l)=0 := by
  rw [gauge,←TurnNetwork.namedGauge_boundary]
  change namedGauge (TurnRectangle.starterGauge M N) (M*N)
    (boundary (L:=L) hM hN F (TurnRectangle.northSlot hM hN c.isLt l))=0
  rw [top_boundary,at_vertex]
  fin_cases l <;> rfl

variable (hm : Matches (L:=L) (M:=M) (N:=N) F)
include hm

lemma bottom_connector (c : Fin M) (l : Fin 2)
    (hi : (F (vertex L M N c ⟨0,by omega⟩ true)).Occupied (lane true 0 l)) :
    Relation.ReflTransGen (graph (L:=L) hM hN F)
      (boundary (L:=L) hM hN F (bottomIndex c l))
      (node L M N (vertex_inside L M N c ⟨0,by omega⟩ true) (lane true 0 l)) ∧
    ∀ P : Node (TurnRectangle.ports M N) (M*N) → ℤ,
      (∀v w,graph (L:=L) hM hN F v w → P w-P v=turnEdge (L:=L) hM hN F v w) →
      P (node L M N (vertex_inside L M N c ⟨0,by omega⟩ true) (lane true 0 l))-
        P (boundary (L:=L) hM hN F (bottomIndex c l))=0 := by
  have him : (up L N F (c.val*N)).Occupied ⟨3-(1-l).val,by omega⟩ := by
    have hh:=up_time L M N F c (⟨0,by omega⟩:Fin N)
    simp only [Nat.add_zero] at hh
    rw [hh]
    fin_cases l <;> exact hi
  have hact:=(TurnRectangle.active_south (up L N F) c (1-l)).mpr him
  have e₁:=TurnRectangle.starter_edge hM hN (up L N F) (down L N F) hact
  have t₁:=TurnRectangle.starter_turn hM hN (up L N F) (down L N F) hact
  have e₂:=TurnRectangle.south_edge hM hN (up L N F) (down L N F) (interior_matches F hm) (1-l) him
  have t₂:=TurnRectangle.south_turn hM hN (up L N F) (down L N F) (interior_matches F hm) (1-l) him
  rw [TurnRectangle.southSlot_right] at e₂ t₂
  rw [bottom_boundary,at_vertex]
  have he : (⟨3-(1-l).val,by omega⟩:Fin 6)=lane true 0 l := by fin_cases l <;> rfl
  rw [he] at e₂ t₂
  refine ⟨(Relation.ReflTransGen.single e₁).trans (.single e₂),?_⟩
  intro P hP
  have hp₁:=(hP _ _ e₁).trans t₁
  have hp₂:=(hP _ _ e₂).trans t₂
  simp only [ite_true]
  change _-P (Sum.inl (TurnStarter.left _ _))=0
  omega

end RibbonRectangle

 

 


lemma last_pass (s : State) (l : List Bool) (hl : l≠[]) :
    ∃ p, (((back (terminal next s l)).1,p),(terminal next s l).2)∈passes s l := by
  induction l generalizing s with
  | nil=>exact (hl rfl).elim
  | cons b l ih=>
    cases l with
    | nil=>
      refine ⟨s.2,?_⟩
      simp only [terminal,back_next]
      exact List.mem_cons_self
    | cons c l=>
      obtain ⟨p,hp⟩:=ih (next s b) (by simp)
      exact ⟨p,List.mem_cons_of_mem _ hp⟩

lemma first_occupied (s : State) (l : List Bool) (hl : l≠[]) (hr : RibbonSimple s l) :
    (ribbon hr s.1).Occupied (lane s.1.2.2 s.2 0) := by
  cases l with
  | nil=>exact (hl rfl).elim
  | cons b l=>exact ⟨_,ribbon_arc hr List.mem_cons_self⟩

namespace RibbonRectangle
variable {L : ℤ} {M N : ℕ} (hM : 1≤M) (hN : 1≤N)

lemma endpoint_turn (s : State) (l : List Bool) (hl : l≠[]) (hr : RibbonSimple s l)
    (hs : Inside L M N s.1) (hI : ∀x∈passes s l,Inside L M N x.1.1)
    (hm : Matches (L:=L) (M:=M) (N:=N) (ribbon hr))
    (i j : Fin (TurnRectangle.ports M N)) (hne : i≠j)
    (hsi : Relation.ReflTransGen (graph (L:=L) hM hN (ribbon hr))
      (boundary (L:=L) hM hN (ribbon hr) i) (node L M N hs (lane s.1.2.2 s.2 0)))
    (hjt : Relation.ReflTransGen (graph (L:=L) hM hN (ribbon hr))
      (boundary (L:=L) hM hN (ribbon hr) j)
      (node L M N (last_inside s l hl hI)
        (lane (back (terminal next s l)).1.2.2 (terminal next s l).2 1)))
    (hzero : ∀P : Node (TurnRectangle.ports M N) (M*N) → ℤ,
      (∀v w,graph (L:=L) hM hN (ribbon hr) v w →
        P w-P v=turnEdge (L:=L) hM hN (ribbon hr) v w) →
      P (node L M N hs (lane s.1.2.2 s.2 0))-
          P (boundary (L:=L) hM hN (ribbon hr) i)=0 ∧
      P (node L M N (last_inside s l hl hI)
        (lane (back (terminal next s l)).1.2.2 (terminal next s l).2 1))-
          P (boundary (L:=L) hM hN (ribbon hr) j)=0) :
    turn l=Pairing.arcTurn (gauge (L:=L) hM hN (ribbon hr)) i j := by
  have hc:=TurnRectangle.compatible hM hN (start (L:=L) (ribbon hr))
    (up L N (ribbon hr)) (down L N (ribbon hr)) (physical_matches hM hN (ribbon hr) hm)
  obtain ⟨a,P,hreach,ha,he⟩:=TurnNetwork.potential (start (L:=L) (ribbon hr))
    (TurnRectangle.starterGauge M N) (up L N (ribbon hr)) (down L N (ribbon hr))
    (TurnRectangle.position M N) (TurnRectangle.position_bound hM hN) (M*N) hc
    (ribbon_drains hM hN s l hr hs hI hm i hsi)
  obtain ⟨p,hp⟩:=last_pass s l hl
  have hrt:=(route_reach hM hN (ribbon hr) hm s l hs hI (fun x hx=>ribbon_arc hr hx) hp).2
  have hab : a.Adj i j := ((hreach i j).mp (hsi.trans (hrt.trans
    (ConnectivityCertificate.reach_symm ⟨fun _ _ hedge=>symm hedge⟩ hjt)))).resolve_left hne
  have ht:=route_turn hM hN (ribbon hr) hm s l hl hs hI (fun x hx=>ribbon_arc hr hx) P he
  have hz:=hzero P he
  have hb:=ha i j hab
  change P (boundary (L:=L) hM hN (ribbon hr) j)-P (boundary (L:=L) hM hN (ribbon hr) i)=Pairing.arcTurn (gauge (L:=L) hM hN (ribbon hr)) i j at hb
  omega

lemma bottom_outside (c : Fin M) :
    ¬Inside L M N (back (vertex L M N c ⟨0,by omega⟩ true,0)).1 := by
  simp [Inside,back,neighbor,vertex]

include hM in
lemma bottom_turn (c₀ c₁ : Fin M) (l : List Bool) (hl : l≠[])
    (hr : RibbonSimple (vertex L M N c₀ ⟨0,by omega⟩ true,0) l)
    (hI : ∀x∈passes (vertex L M N c₀ ⟨0,by omega⟩ true,0) l,Inside L M N x.1.1)
    (ht : terminal next (vertex L M N c₀ ⟨0,by omega⟩ true,0) l=
      back (vertex L M N c₁ ⟨0,by omega⟩ true,0)) :
    turn l=if c₀ ≤ c₁ then -3 else 3 := by
  let s : State:=(vertex L M N c₀ ⟨0,by omega⟩ true,0)
  have hm:=ribbon_matches (L:=L) (M:=M) (N:=N) hr (bottom_outside hN c₀)
    (by rw [ht]; exact bottom_outside hN c₁)
  have hi:=bottom_connector hM hN (ribbon hr) hm c₀ 0 (first_occupied s l hl hr)
  have heV : (back (terminal next s l)).1=vertex L M N c₁ ⟨0,by omega⟩ true := by rw [ht,back_back]
  have heP : (terminal next s l).2=0 := by rw [ht]; rfl
  obtain ⟨p,hp⟩:=last_pass s l hl
  have hocc : (ribbon hr (vertex L M N c₁ ⟨0,by omega⟩ true)).Occupied (lane true 0 1) := by
    have hh : (ribbon hr (back (terminal next s l)).1).Occupied
        (lane (back (terminal next s l)).1.2.2 (terminal next s l).2 1) := ⟨_,(ribbon_arc hr hp).symm⟩
    simpa only [heV,heP,vertex] using hh
  have hj:=bottom_connector hM hN (ribbon hr) hm c₁ 1 hocc
  have heNode : node L M N (last_inside s l hl hI)
        (lane (back (terminal next s l)).1.2.2 (terminal next s l).2 1)=
      node L M N (vertex_inside L M N c₁ ⟨0,by omega⟩ true) (lane true 0 1) := by
    rw [node_of_vertex _ heV,at_vertex,heV,heP]
    rfl
  have hne : bottomIndex (N:=N) c₀ 0 ≠bottomIndex c₁ 1 := by
    intro he
    have hv:=congrArg Fin.val he
    simp only [bottomIndex_val,Fin.val_zero,Fin.val_one] at hv
    omega
  have hh:=endpoint_turn hM hN s l hl hr (vertex_inside _ _ _ _ _ _) hI hm
    (bottomIndex c₀ 0) (bottomIndex c₁ 1) hne hi.1 (by rw [heNode]; exact hj.1)
    (fun P hP=>⟨hi.2 P hP,by rw [heNode]; exact hj.2 P hP⟩)
  rw [hh,Pairing.arcTurn,bottom_gauge,bottom_gauge]
  unfold Pairing.turnOrder
  simp only [Fin.le_iff_val_le_val,Fin.lt_def,bottomIndex_val,Fin.val_zero,Fin.val_one]
  split_ifs <;> omega

end RibbonRectangle
end





end CriticalStrip.HoneycombBranch

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
namespace HoneycombBranch
open scoped Classical
section TreeMass
open Diagram FiniteBranchTree


lemma finite_columns (p : List Vertex) (i j : ℤ) :
    ∃ L : ℤ, ∃ M : ℕ, 1 ≤ M ∧ L ≤ i ∧ i < L + (M:ℤ) ∧ L ≤ j ∧ j < L + (M:ℤ) ∧
      ∀v∈p,L≤v.1 ∧ v.1<L+(M:ℤ) := by
  let F:= ((bottom i).1::(bottom j).1::p).toFinset
  let B:=F.sup (fun v=>v.1.natAbs)
  have hb (v : Vertex) (hv : v∈F) : -(B:ℤ)≤v.1 ∧ v.1<(B:ℤ)+1 := by
    have hh:=Finset.le_sup (f:=fun v : Vertex=>v.1.natAbs) hv
    have h₁:=(Int.le_natAbs : v.1 ≤ (v.1.natAbs : ℤ))
    have h₂:=(Int.le_natAbs : -v.1 ≤ ((-v.1).natAbs : ℤ))
    rw [Int.natAbs_neg] at h₂
    change v.1.natAbs≤B at hh
    omega
  have hi:=hb (bottom i).1 (by simp [F])
  have hj:=hb (bottom j).1 (by simp [F])
  dsimp only [bottom,Prod.fst] at hi hj
  refine ⟨-(B:ℤ),2*B+1,by omega,by omega,by omega,by omega,by omega,?_⟩
  intro v hv
  have hh:=hb v (by simp only [F,List.mem_toFinset,List.mem_cons]; tauto)
  constructor <;> omega

lemma finite_rows (p : List Vertex) : ∃N : ℕ,1≤N ∧ ∀v∈p,v.2.1<(N:ℤ) := by
  let B:=p.toFinset.sup (fun v=>v.2.1.natAbs)
  refine ⟨B+1,by omega,?_⟩
  intro v hv
  have hh:=Finset.le_sup (f:=fun v : Vertex=>v.2.1.natAbs) (List.mem_toFinset.mpr hv)
  have ha:=(Int.le_natAbs : v.2.1 ≤ (v.2.1.natAbs : ℤ))
  change v.2.1.natAbs≤B at hh
  omega

 

theorem bottom_turn (i j : ℤ) (l : List Bool) (hl : l≠[])
    (hr : RibbonSimple (bottom i) l)
    (hrow : ∀v∈visited Prod.fst next (bottom i) l,0≤v.2.1)
    (ht : terminal next (bottom i) l=back (bottom j)) :
    turn l=if i≤j then -3 else 3 := by
  obtain ⟨L,M,hM,hi₁,hi₂,hj₁,hj₂,hcol⟩:=finite_columns (visited Prod.fst next (bottom i) l) i j
  obtain ⟨N,hN,hupper⟩:=finite_rows (visited Prod.fst next (bottom i) l)
  let c₀ : Fin M:=⟨(i-L).toNat,by omega⟩
  let c₁ : Fin M:=⟨(j-L).toNat,by omega⟩
  have he₀ : (RibbonRectangle.vertex L M N c₀ ⟨0,by omega⟩ true,0)=bottom i := by
    dsimp [RibbonRectangle.vertex,bottom,c₀]
    congr 2
    omega
  have he₁ : (RibbonRectangle.vertex L M N c₁ ⟨0,by omega⟩ true,0)=bottom j := by
    dsimp [RibbonRectangle.vertex,bottom,c₁]
    congr 2
    omega
  have hh:=RibbonRectangle.bottom_turn hM hN c₀ c₁ l hl
    (by rw [he₀]; exact hr) (by
      rw [he₀]
      intro x hx
      have hm:=passes_mem_vertex hx
      exact ⟨(hcol _ hm).1,(hcol _ hm).2,hrow _ hm,hupper _ hm⟩)
    (by rw [he₀,he₁]; exact ht)
  rw [hh]
  have he : c₀ ≤ c₁ ↔ i≤j := by dsimp [c₀,c₁]; simp only [Fin.le_iff_val_le_val]; omega
  simp only [he]

end TreeMass

section BoundaryConnection
open Diagram Diagram.TurnNetwork Diagram.TurnDisk FiniteBranchTree
namespace RibbonRectangle
variable {L : ℤ} {M N : ℕ} (hM : 1≤M) (hN : 1≤N)

lemma top_outside (c : Fin M) :
    ¬Inside L M N (back (vertex L M N c ⟨N-1,by omega⟩ false,0)).1 := by
  have he : ((N-1:ℕ):ℤ)+1=(N:ℤ) := by omega
  simp [Inside,back,neighbor,vertex,he]

include hM in
lemma top_turn (c₀ c₁ : Fin M) (l : List Bool) (hl : l≠[])
    (hr : RibbonSimple (vertex L M N c₀ ⟨0,by omega⟩ true,0) l)
    (hI : ∀x∈passes (vertex L M N c₀ ⟨0,by omega⟩ true,0) l,Inside L M N x.1.1)
    (ht : terminal next (vertex L M N c₀ ⟨0,by omega⟩ true,0) l=
      back (vertex L M N c₁ ⟨N-1,by omega⟩ false,0)) : turn l=0 := by
  let s : State:=(vertex L M N c₀ ⟨0,by omega⟩ true,0)
  have hm:=ribbon_matches (L:=L) (M:=M) (N:=N) hr (bottom_outside hN c₀)
    (by rw [ht]; exact top_outside hN c₁)
  have hi:=bottom_connector hM hN (ribbon hr) hm c₀ 0 (first_occupied s l hl hr)
  have heV : (back (terminal next s l)).1=vertex L M N c₁ ⟨N-1,by omega⟩ false := by rw [ht,back_back]
  have heP : (terminal next s l).2=0 := by rw [ht]; rfl
  have heNode : node L M N (last_inside s l hl hI)
        (lane (back (terminal next s l)).1.2.2 (terminal next s l).2 1)=
      node L M N (vertex_inside L M N c₁ ⟨N-1,by omega⟩ false) (lane false 0 1) := by
    rw [node_of_vertex _ heV,at_vertex,heV,heP]
    rfl
  have hbd : boundary (L:=L) hM hN (ribbon hr) (TurnRectangle.northSlot hM hN c₁.isLt 1)=
      node L M N (last_inside s l hl hI)
        (lane (back (terminal next s l)).1.2.2 (terminal next s l).2 1) := by
    rw [heNode,top_boundary]
  have hlt : bottomIndex (N:=N) c₀ 0 < TurnRectangle.northSlot hM hN c₁.isLt 1 := by
    have hh:=bottomIndex_lt (N:=N) c₀ 0
    rw [Fin.lt_def,TurnRectangle.northSlot_val]
    omega
  have hh:=endpoint_turn hM hN s l hl hr (vertex_inside _ _ _ _ _ _) hI hm
    (bottomIndex c₀ 0) (TurnRectangle.northSlot hM hN c₁.isLt 1) (ne_of_lt hlt) hi.1
    (by rw [hbd])
    (fun P hP=>⟨hi.2 P hP,by rw [hbd,sub_self]⟩)
  rw [hh,Pairing.arcTurn,bottom_gauge,top_gauge,Pairing.turnOrder,ite_eq_left hlt]
  norm_num

end RibbonRectangle

 
theorem top_turn (H : ℕ) (hH : 1≤H) (i j : ℤ) (l : List Bool) (hl : l≠[])
    (hn : (visited Prod.fst next (bottom i) l).Nodup)
    (hrow : ∀v∈visited Prod.fst next (bottom i) l,0≤v.2.1 ∧ v.2.1<(H:ℤ))
    (ht : terminal next (bottom i) l=back (top H j)) : turn l=0 := by
  obtain ⟨L,M,hM,hi₁,hi₂,hj₁,hj₂,hcol⟩:=finite_columns (visited Prod.fst next (bottom i) l) i j
  let c₀ : Fin M:=⟨(i-L).toNat,by omega⟩
  let c₁ : Fin M:=⟨(j-L).toNat,by omega⟩
  have he₀ : (RibbonRectangle.vertex L M H c₀ ⟨0,by omega⟩ true,0)=bottom i := by
    dsimp [RibbonRectangle.vertex,bottom,c₀]
    congr 2
    omega
  have he₁ : (RibbonRectangle.vertex L M H c₁ ⟨H-1,by omega⟩ false,0)=top H j := by
    dsimp [RibbonRectangle.vertex,top,c₁]
    congr 2
    · omega
    · ext <;> dsimp
      omega
  apply RibbonRectangle.top_turn hM hH c₀ c₁ l hl
    (by rw [he₀]; exact ribbonSimple_of_nodup hn) (by
      rw [he₀]
      intro x hx
      have hm:=passes_mem_vertex hx
      exact ⟨(hcol _ hm).1,(hcol _ hm).2,(hrow _ hm).1,(hrow _ hm).2⟩)
    (by rw [he₀,he₁]; exact ht)

end BoundaryConnection

open FiniteBranchTree



end HoneycombBranch
open scoped Classical BigOperators



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
open scoped Classical
open FiniteBranchTree


lemma steppedVertices_bound (N : ℕ) (s : ℤ) (v : Vertex) (hv : steppedVertices N s v) :
    0≤v.2.1 ∧ v.2.1<((N+1:ℕ):ℤ) := by
  dsimp [steppedVertices] at hv
  exact ⟨hv.1,by omega⟩

lemma lower_top_turn (N : ℕ) (hN : 1≤N) (s i j : ℤ) (hj : j < s)
    (l : List Bool) (_hl : l≠[]) (hn : (visited Prod.fst next (bottom i) l).Nodup)
    (hD : ∀v∈visited Prod.fst next (bottom i) l,steppedVertices N s v)
    (ht : terminal next (bottom i) l=back (top N j)) : turn l=0 := by
  have hu : (j,(N:ℤ),true)∉visited Prod.fst next (bottom i) l := by
    intro hv
    have hh:=hD _ hv
    simp only [steppedVertices,lt_self_iff_false,true_and,false_or] at hh
    omega
  have hd : (j,(N:ℤ),false)∉visited Prod.fst next (bottom i) l := by
    intro hv
    have hh:=hD _ hv
    simp only [steppedVertices,lt_self_iff_false,true_and,false_or] at hh
    omega
  have hv : visited Prod.fst next (bottom i) (l++[false,true])=
      visited Prod.fst next (bottom i) l++[(j,(N:ℤ),true),(j,(N:ℤ),false)] := by
    rw [visited_append,ht]
    simp [visited,back,top,neighbor,next,outgoing]
  have he : terminal next (bottom i) (l++[false,true])=back (top (N+1) j) := by
    rw [terminal_append,ht]
    simp [terminal,back,top,neighbor,next,outgoing,Fin.add_def]
  have hh:=top_turn (N+1) (by omega) i j (l++[false,true]) (by simp) (by
      rw [hv]
      apply List.nodup_append.mpr
      refine ⟨hn,by simp,?_⟩
      intro v hv w hw hew
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl
      · exact hu (hew ▸ hv)
      · exact hd (hew ▸ hv)) (by
      intro v hm
      rw [hv] at hm
      rcases List.mem_append.mp hm with hm|hm
      · exact steppedVertices_bound N s v (hD v hm)
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
        rcases hm with rfl|rfl <;> dsimp <;> omega) he
  simpa [turn_append,turn,sign] using hh

lemma step_top_turn (N : ℕ) (hN : 1≤N) (s i j : ℤ)
    (l : List Bool) (hl : l≠[]) (hn : (visited Prod.fst next (bottom i) l).Nodup)
    (hD : ∀v∈visited Prod.fst next (bottom i) l,steppedVertices N s v)
    (ht : terminal next (bottom i) l=back (stepTop N s j)) : turn l=0 := by
  by_cases hj : j < s
  · rw [stepTop,ite_eq_left hj] at ht
    exact lower_top_turn N hN s i j hj l hl hn hD ht
  · rw [stepTop,ite_eq_right hj] at ht
    exact top_turn (N+1) (by omega) i j l hl hn (fun v hv=>steppedVertices_bound N s v (hD v hv)) ht

lemma step_side_turn (N : ℕ) (s i : ℤ)
    (l : List Bool) (_hl : l≠[]) (hn : (visited Prod.fst next (bottom i) l).Nodup)
    (hD : ∀v∈visited Prod.fst next (bottom i) l,steppedVertices N s v)
    (ht : terminal next (bottom i) l=back (sidePort N s)) : turn l=1 := by
  have hd : (s-1,(N:ℤ),false)∉visited Prod.fst next (bottom i) l := by
    intro hv
    have hh:=hD _ hv
    simp only [steppedVertices,lt_self_iff_false,true_and,false_or] at hh
    omega
  have hv : visited Prod.fst next (bottom i) (l++[false])=
      visited Prod.fst next (bottom i) l++[(s-1,(N:ℤ),false)] := by
    rw [visited_append,ht]
    simp [visited,back,sidePort,neighbor]
  have he : terminal next (bottom i) (l++[false])=back (top (N+1) (s-1)) := by
    rw [terminal_append,ht]
    simp [terminal,back,top,sidePort,neighbor,next,outgoing,Fin.add_def]
  have hh:=top_turn (N+1) (by omega) i (s-1) (l++[false]) (by simp) (by
      rw [hv]
      apply List.nodup_append.mpr
      refine ⟨hn,by simp,?_⟩
      intro v hm w hw hew
      have hw:=List.mem_singleton.mp hw
      exact hd ((hew.trans hw) ▸ hm)) (by
      intro v hm
      rw [hv] at hm
      rcases List.mem_append.mp hm with hm|hm
      · exact steppedVertices_bound N s v (hD v hm)
      · have he:=List.mem_singleton.mp hm
        rw [he]
        dsimp
        omega) he
  simp [turn_append,turn,sign] at hh
  omega

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



lemma step_turn_oai (N : ℕ) (hN : 1≤N) (s i : ℤ) (x : ExitWord (steppedVertices N s) i) :
    turn x.val=stepTurn i (exitPort (stepBoundaryPorts N hN s) x) := by
  have ht:=exitPort_terminal (stepBoundaryPorts N hN s) x
  generalize hb : exitPort (stepBoundaryPorts N hN s) x=b at ht ⊢
  rcases b with j|(j|u)
  · exact bottom_turn i j x.val x.property.1 (ribbonSimple_of_nodup x.property.2.1)
      (fun v hv=>(x.property.2.2.1 v hv).1) ht
  · exact step_top_turn N hN s i j x.val x.property.1 x.property.2.1 x.property.2.2.1 ht
  · exact step_side_turn N s i x.val x.property.1 x.property.2.1 x.property.2.2.1 ht

end
end CriticalStrip.HoneycombBranch





end OAI
end

theorem solution : type_of% @OAI.CriticalStrip.HoneycombBranch.step_turn_oai := @OAI.CriticalStrip.HoneycombBranch.step_turn_oai
