-- Prove2me | solution 1 for NagamochiIbaraki.NodeConn.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T15:52:10.233037+00:00
-- url     : https://prove2.me/submissions/56a30aa1-6c6c-4fed-81d7-6e540c44bbb8

import Mathlib
import Definitions.Def_NagamochiIbaraki_NodeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_NodeConn_localNodeConn
import Definitions.Def_NagamochiIbaraki_NodeConn_Forest

set_option autoImplicit false

open NagamochiIbaraki.NodeConn in
/-- The vertices of `W` already charged to `z` in the state `s`: those scanned, plus the current
node when it lies in `W` and has already scanned its edge to `z`. -/
def ni31cnt {V E : Type*} [DecidableEq V] [Fintype E] (ends : E → Sym2 V) (W : Finset V) (s : State V E)
    (z : V) : ℕ :=
  (W.filter (fun w => w ∈ s.done ∨
    (s.cur = some w ∧ ∃ e, s.idx e ≠ 0 ∧ ends e = s(w, z)))).card

open NagamochiIbaraki.NodeConn in
/-- Every unprocessed node `z ∉ W` on the side `b` of `P` has label at most its charge. -/
def ni31Good {V E : Type*} [DecidableEq V] [Fintype E] (ends : E → Sym2 V) (W : Finset V) (P : V → Prop) (b : Prop)
    (s : State V E) : Prop :=
  ∀ z, z ∉ W → (P z ↔ b) → z ∉ s.done → s.cur ≠ some z → s.r z ≤ ni31cnt ends W s z

open NagamochiIbaraki.NodeConn in
/-- The run invariant. -/
def ni31Inv {V E : Type*} [DecidableEq V] [Fintype E] (ends : E → Sym2 V) (W : Finset V) (P : V → Prop)
    (s : State V E) : Prop :=
  (∀ x, s.cur = some x → x ∉ s.done) ∧
  (∀ z, z ∈ s.done → ∀ e, z ∈ ends e → s.idx e ≠ 0) ∧
  (∀ e a b, s.idx e ≠ 0 → ends e = s(a, b) → a ∉ W → b ∉ W → (P a ↔ P b)) ∧
  (∃ b : Prop, ni31Good ends W P b s) ∧
  (∀ x, s.cur = some x → x ∉ W → ni31Good ends W P (¬ P x) s)

open NagamochiIbaraki.NodeConn in
theorem ni31cnt_le_card {V E : Type*} [DecidableEq V] [Fintype E] (ends : E → Sym2 V) (W : Finset V) (s : State V E)
    (z : V) : ni31cnt ends W s z ≤ W.card := by
  unfold ni31cnt
  exact Finset.card_filter_le _ _

open NagamochiIbaraki.NodeConn in
theorem ni31cnt_mono {V E : Type*} [DecidableEq V] [Fintype E] (ends : E → Sym2 V) (W : Finset V) (s t : State V E)
    (z z' : V)
    (h : ∀ w, w ∈ W → (w ∈ s.done ∨ (s.cur = some w ∧ ∃ e, s.idx e ≠ 0 ∧ ends e = s(w, z))) →
      (w ∈ t.done ∨ (t.cur = some w ∧ ∃ e, t.idx e ≠ 0 ∧ ends e = s(w, z')))) :
    ni31cnt ends W s z ≤ ni31cnt ends W t z' := by
  unfold ni31cnt
  apply Finset.card_le_card
  intro w hw
  rw [Finset.mem_filter] at hw ⊢
  exact ⟨hw.1, h w hw.1 hw.2⟩

open NagamochiIbaraki.NodeConn in
theorem ni31_inv_init {V E : Type*} [DecidableEq V] [Fintype E] (ends : E → Sym2 V) (W : Finset V) (P : V → Prop) :
    ni31Inv ends W P (init : State V E) := by
  refine ⟨?_, ?_, ?_, ⟨True, ?_⟩, ?_⟩
  · intro x hx
    simp [init] at hx
  · intro z hz
    simp [init] at hz
  · intro e a b he
    simp [init] at he
  · intro z _ _ _ _
    simp [init]
  · intro x hx
    simp [init] at hx

open NagamochiIbaraki.NodeConn in
theorem ni31_inv_step {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
    {ends : E → Sym2 V} (hloop : ∀ e, ¬ (ends e).IsDiag) (hsimple : Function.Injective ends)
    {W : Finset V} {P : V → Prop} {i : ℕ} (hWi : W.card < i) {F : Finset E}
    (hsep : ∀ a b, a ∉ W → b ∉ W → (edgeGraph ends F).Adj a b → (P a ↔ P b))
    {s t : State V E} (hst : Step ends s t)
    (hF : ∀ e, t.idx e ≠ 0 → t.idx e ≤ i → e ∈ F)
    (hs : ni31Inv ends W P s) : ni31Inv ends W P t := by
  obtain ⟨I1, I2, I4, ⟨b, I5⟩, I6⟩ := hs
  rcases hst with ⟨x, hcur, hxd, hmax, rfl⟩ | ⟨x, y, e, hcur, he0, hends, rfl⟩ |
    ⟨x, hcur, hall, rfl⟩
  · -- select
    have hcnt : ∀ z z', ni31cnt ends W s z ≤
        ni31cnt ends W { s with cur := some x, order := s.order ++ [x] } z' := by
      intro z z'
      apply ni31cnt_mono
      intro w _ hw
      left
      rcases hw with h | ⟨h, -⟩
      · exact h
      · simp [hcur] at h
    have hgood : ∀ b', ni31Good ends W P b' s →
        ni31Good ends W P b' { s with cur := some x, order := s.order ++ [x] } := by
      intro b' hg z hzW hzb hzd _
      exact (hg z hzW hzb hzd (by simp [hcur])).trans (hcnt z z)
    refine ⟨?_, I2, I4, ⟨b, hgood b I5⟩, ?_⟩
    · intro x' hx'
      have hx : x = x' := Option.some.inj hx'
      subst hx
      exact hxd
    · intro x' hx' hx'W
      have hx : x = x' := Option.some.inj hx'
      subst hx
      by_cases hb : (P x ↔ b)
      · intro z _ _ hzd _
        have h1 : s.r x ≤ ni31cnt ends W s x := I5 x hx'W hb hxd (by simp [hcur])
        exact (hmax z hzd).trans (h1.trans (hcnt x z))
      · intro z hzW hzb hzd hzc
        have hzb' : (P z ↔ b) := by tauto
        exact hgood b I5 z hzW hzb' hzd hzc
  · -- scan
    have hxy : x ≠ y := by
      intro h
      apply hloop e
      rw [hends, h]
      exact Sym2.mk_isDiag_iff.2 rfl
    have hyd : y ∉ s.done := by
      intro h
      exact I2 y h e (by rw [hends]; exact Sym2.mem_mk_right x y) he0
    have hxd : x ∉ s.done := I1 x hcur
    have hidx_ne : ∀ e', s.idx e' ≠ 0 → Function.update s.idx e (s.r y + 1) e' ≠ 0 := by
      intro e' he'
      have hne : e' ≠ e := by
        rintro rfl
        exact he' he0
      rw [Function.update_of_ne hne]
      exact he'
    have hidx_e : Function.update s.idx e (s.r y + 1) e = s.r y + 1 := Function.update_self _ _ _
    have hr_other : ∀ z, z ≠ x → z ≠ y →
        Function.update (Function.update s.r x (if s.r x = s.r y then s.r x + 1 else s.r x))
          y (s.r y + 1) z = s.r z := by
      intro z hzx hzy
      rw [Function.update_of_ne hzy, Function.update_of_ne hzx]
    have hr_y : Function.update (Function.update s.r x (if s.r x = s.r y then s.r x + 1 else s.r x))
          y (s.r y + 1) y = s.r y + 1 := Function.update_self _ _ _
    set t : State V E := { s with
              idx := Function.update s.idx e (s.r y + 1),
              r := Function.update
                (Function.update s.r x (if s.r x = s.r y then s.r x + 1 else s.r x))
                y (s.r y + 1) } with ht
    have htcur : t.cur = some x := hcur
    have hcnt : ∀ z, ni31cnt ends W s z ≤ ni31cnt ends W t z := by
      intro z
      apply ni31cnt_mono
      intro w _ hw
      rcases hw with h | ⟨h1, e', he', h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, e', hidx_ne e' he', h2⟩
    have hnew : x ∉ W → y ∉ W → (P x ↔ P y) := by
      intro hxW hyW
      by_contra hne
      have hg := I6 x hcur hxW
      have hyside : (P y ↔ ¬ P x) := by tauto
      have h1 : s.r y ≤ ni31cnt ends W s y :=
        hg y hyW hyside hyd (by rw [hcur]; exact fun h => hxy (Option.some.inj h))
      have h2 := ni31cnt_le_card ends W s y
      have hmem : e ∈ F := hF e (by show Function.update s.idx e (s.r y + 1) e ≠ 0; omega)
        (by show Function.update s.idx e (s.r y + 1) e ≤ i; omega)
      have hadj : (edgeGraph ends F).Adj x y := by
        unfold edgeGraph
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨⟨e, Finset.mem_coe.2 hmem, hends⟩, hxy⟩
      exact hne (hsep x y hxW hyW hadj)
    have hI4 : ∀ e' a c, t.idx e' ≠ 0 → ends e' = s(a, c) → a ∉ W → c ∉ W → (P a ↔ P c) := by
      intro e' a c he' hends' haW hcW
      by_cases hee : e' = e
      · subst hee
        rw [hends] at hends'
        rcases Sym2.eq_iff.1 hends' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hnew haW hcW
        · exact (hnew hcW haW).symm
      · have : s.idx e' ≠ 0 := by
          have h := he'
          simp only [t, Function.update_of_ne hee] at h
          exact h
        exact I4 e' a c this hends' haW hcW
    refine ⟨fun x' hx' => I1 x' hx', fun z hz e' he' => hidx_ne e' (I2 z hz e' he'), hI4, ?_, ?_⟩
    · by_cases hxW : x ∈ W
      · -- the current node lies in `W`
        have hcnt_y : ni31cnt ends W s y + 1 ≤ ni31cnt ends W t y := by
          unfold ni31cnt
          have hxA : x ∉ W.filter (fun w => w ∈ s.done ∨
              (s.cur = some w ∧ ∃ e, s.idx e ≠ 0 ∧ ends e = s(w, y))) := by
            rw [Finset.mem_filter]
            rintro ⟨-, h | ⟨-, e', he', h2⟩⟩
            · exact hxd h
            · have : e' = e := hsimple (h2.trans hends.symm)
              subst this
              exact he' he0
          rw [← Finset.card_insert_of_notMem hxA]
          apply Finset.card_le_card
          intro w hw
          rw [Finset.mem_insert] at hw
          rw [Finset.mem_filter]
          rcases hw with rfl | hw
          · exact ⟨hxW, Or.inr ⟨htcur, e, by show Function.update s.idx e (s.r y + 1) e ≠ 0; omega,
              hends⟩⟩
          · rw [Finset.mem_filter] at hw
            refine ⟨hw.1, ?_⟩
            rcases hw.2 with h | ⟨h1, e', he', h2⟩
            · exact Or.inl h
            · exact Or.inr ⟨h1, e', hidx_ne e' he', h2⟩
        refine ⟨b, ?_⟩
        intro z hzW hzb hzd hzc
        have hzx : z ≠ x := by
          rintro rfl
          exact hzc htcur
        by_cases hzy : z = y
        · subst hzy
          have h1 : s.r z ≤ ni31cnt ends W s z :=
            I5 z hzW hzb hzd (by rw [hcur]; exact fun h => hzx (Option.some.inj h).symm)
          show Function.update (Function.update s.r x
            (if s.r x = s.r z then s.r x + 1 else s.r x)) z (s.r z + 1) z ≤ ni31cnt ends W t z
          rw [hr_y]
          omega
        · have h1 : s.r z ≤ ni31cnt ends W s z :=
            I5 z hzW hzb hzd (by rw [hcur]; exact fun h => hzx (Option.some.inj h).symm)
          show Function.update (Function.update s.r x
            (if s.r x = s.r y then s.r x + 1 else s.r x)) y (s.r y + 1) z ≤ ni31cnt ends W t z
          rw [hr_other z hzx hzy]
          exact h1.trans (hcnt z)
      · exact ⟨¬ P x, fun z hzW hzb hzd hzc => by
          have hzx : z ≠ x := by
            rintro rfl
            exact hzc htcur
          have hzy : z ≠ y := by
            rintro rfl
            have := hnew hxW hzW
            tauto
          have h1 : s.r z ≤ ni31cnt ends W s z :=
            I6 x hcur hxW z hzW hzb hzd (by rw [hcur]; exact fun h => hzx (Option.some.inj h).symm)
          show Function.update (Function.update s.r x
            (if s.r x = s.r y then s.r x + 1 else s.r x)) y (s.r y + 1) z ≤ ni31cnt ends W t z
          rw [hr_other z hzx hzy]
          exact h1.trans (hcnt z)⟩
    · intro x' hx' hx'W
      have hx : x = x' := Option.some.inj (htcur.symm.trans hx')
      subst hx
      intro z hzW hzb hzd hzc
      have hzx : z ≠ x := by
        rintro rfl
        exact hzc htcur
      have hzy : z ≠ y := by
        rintro rfl
        have := hnew hx'W hzW
        tauto
      have h1 : s.r z ≤ ni31cnt ends W s z :=
        I6 x hcur hx'W z hzW hzb hzd (by rw [hcur]; exact fun h => hzx (Option.some.inj h).symm)
      show Function.update (Function.update s.r x
        (if s.r x = s.r y then s.r x + 1 else s.r x)) y (s.r y + 1) z ≤ ni31cnt ends W t z
      rw [hr_other z hzx hzy]
      exact h1.trans (hcnt z)
  · -- finish
    have hcnt : ∀ z, ni31cnt ends W s z ≤
        ni31cnt ends W { s with done := insert x s.done, cur := none } z := by
      intro z
      apply ni31cnt_mono
      intro w _ hw
      left
      show w ∈ insert x s.done
      rw [Finset.mem_insert]
      rcases hw with h | ⟨h, -⟩
      · exact Or.inr h
      · rw [hcur] at h
        exact Or.inl (Option.some.inj h).symm
    refine ⟨?_, ?_, I4, ⟨b, ?_⟩, ?_⟩
    · intro x' hx'
      simp at hx'
    · intro z hz e' he'
      have hz' : z = x ∨ z ∈ s.done := Finset.mem_insert.1 hz
      rcases hz' with rfl | hz'
      · exact hall e' he'
      · exact I2 z hz' e' he'
    · intro z hzW hzb hzd _
      have hzd' : z ≠ x ∧ z ∉ s.done := by
        have : ¬ (z = x ∨ z ∈ s.done) := fun h => hzd (Finset.mem_insert.2 h)
        tauto
      exact (I5 z hzW hzb hzd'.2 (by rw [hcur]; exact fun h => hzd'.1 (Option.some.inj h).symm)).trans
        (hcnt z)
    · intro x' hx'
      simp at hx'

open NagamochiIbaraki.NodeConn in
theorem ni31_step_idx {V E : Type*} [DecidableEq V] [DecidableEq E] {ends : E → Sym2 V}
    {s t : State V E} (h : Step ends s t) (e : E) (he : s.idx e ≠ 0) : t.idx e = s.idx e := by
  rcases h with ⟨x, -, -, -, rfl⟩ | ⟨x, y, e', -, h0, -, rfl⟩ | ⟨x, -, -, rfl⟩
  · rfl
  · have hne : e ≠ e' := by
      rintro rfl
      exact he h0
    exact Function.update_of_ne hne _ _
  · rfl

open NagamochiIbaraki.NodeConn in
theorem ni31_persist {V E : Type*} [DecidableEq V] [DecidableEq E] {ends : E → Sym2 V}
    {σ : ℕ → State V E} {K : ℕ} (hrun : IsRun ends σ K) (j : ℕ) (hj : j ≤ K) (e : E)
    (he : (σ j).idx e ≠ 0) : (σ K).idx e = (σ j).idx e := by
  have key : ∀ m, j + m ≤ K → (σ (j + m)).idx e = (σ j).idx e := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have hstep := hrun.2 (j + m) (by omega)
      rw [show j + (m + 1) = j + m + 1 by omega, ni31_step_idx hstep e (by rw [h1]; exact he), h1]
  have := key (K - j) (by omega)
  rwa [show j + (K - j) = K by omega] at this

open NagamochiIbaraki.NodeConn in
theorem ni31_sides {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    {ends : E → Sym2 V} (hloop : ∀ e, ¬ (ends e).IsDiag) (hsimple : Function.Injective ends)
    {σ : ℕ → State V E} {K : ℕ} (hrun : IsCompletedRun ends σ K) (i : ℕ) (W : Finset V)
    (hWi : W.card < i) (P : V → Prop)
    (hsep : ∀ a b, a ∉ W → b ∉ W → (edgeGraph ends (upto (σ K) i)).Adj a b → (P a ↔ P b))
    (e : E) (a c : V) (he : ends e = s(a, c)) (ha : a ∉ W) (hc : c ∉ W) : P a ↔ P c := by
  have hinv : ∀ j, j ≤ K → ni31Inv ends W P (σ j) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [hrun.1.1]
      exact ni31_inv_init ends W P
    | succ j ih =>
      intro hj
      refine ni31_inv_step hloop hsimple hWi hsep (hrun.1.2 j (by omega)) ?_ (ih (by omega))
      intro e' h0 hle
      have hp := ni31_persist hrun.1 (j + 1) hj e' h0
      unfold upto
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩ <;> rw [hp] <;> omega
  obtain ⟨-, I2, I4, -, -⟩ := hinv K le_rfl
  have hne : (σ K).idx e ≠ 0 :=
    I2 a (by rw [hrun.2]; exact Finset.mem_univ a) e (by rw [he]; exact Sym2.mem_mk_left a c)
  exact I4 e a c hne he ha hc

open NagamochiIbaraki.NodeConn in
theorem ni31_edge_conn {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    {ends : E → Sym2 V} (hloop : ∀ e, ¬ (ends e).IsDiag) (hsimple : Function.Injective ends)
    {σ : ℕ → State V E} {K : ℕ} (hrun : IsCompletedRun ends σ K) (i : ℕ) (W : Finset V)
    (hWi : W.card < i) (u v : V) (hu : u ∉ W) (hv : v ∉ W)
    (hadj : (edgeGraph ends Finset.univ).Adj u v) :
    ConnAvoid ends (upto (σ K) i) W u v := by
  have hsep : ∀ a b, a ∉ W → b ∉ W → (edgeGraph ends (upto (σ K) i)).Adj a b →
      (ConnAvoid ends (upto (σ K) i) W u a ↔ ConnAvoid ends (upto (σ K) i) W u b) := by
    intro a b ha hb hab
    unfold ConnAvoid
    constructor
    · intro h
      exact Relation.ReflTransGen.tail h ⟨ha, hb, hab⟩
    · intro h
      exact Relation.ReflTransGen.tail h ⟨hb, ha, hab.symm⟩
  unfold edgeGraph at hadj
  rw [SimpleGraph.fromEdgeSet_adj] at hadj
  obtain ⟨⟨e, -, he⟩, -⟩ := hadj
  exact (ni31_sides hloop hsimple hrun i W hWi (ConnAvoid ends (upto (σ K) i) W u) hsep e u v he
    hu hv).1 Relation.ReflTransGen.refl

open NagamochiIbaraki.NodeConn in
theorem ni31_lift {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    {ends : E → Sym2 V} (hloop : ∀ e, ¬ (ends e).IsDiag) (hsimple : Function.Injective ends)
    {σ : ℕ → State V E} {K : ℕ} (hrun : IsCompletedRun ends σ K) (i : ℕ) (W : Finset V)
    (hWi : W.card < i) (a b : V) (h : ConnAvoid ends Finset.univ W a b) :
    ConnAvoid ends (upto (σ K) i) W a b := by
  unfold ConnAvoid at h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    exact Relation.ReflTransGen.trans ih
      (ni31_edge_conn hloop hsimple hrun i W hWi _ _ hbc.1 hbc.2.1 hbc.2.2)

open NagamochiIbaraki.NodeConn in
theorem solution
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (hsimple : Function.Injective ends)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsCompletedRun ends σ K) :
    ∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card E → ∀ x y : V,
      min (localNodeConn ends Finset.univ x y) (i : ℕ∞)
        ≤ localNodeConn ends (upto (σ K) i) x y := by
  intro i _ _ x y
  by_cases hAi : (edgeGraph ends (upto (σ K) i)).Adj x y
  · have hA : (edgeGraph ends Finset.univ).Adj x y := by
      unfold edgeGraph at hAi ⊢
      rw [SimpleGraph.fromEdgeSet_adj] at hAi ⊢
      obtain ⟨⟨e, -, he⟩, hne⟩ := hAi
      exact ⟨⟨e, Finset.mem_coe.2 (Finset.mem_univ e), he⟩, hne⟩
    have h1 : localNodeConn ends Finset.univ x y = ((Fintype.card V - 1 : ℕ) : ℕ∞) := by
      unfold localNodeConn
      split_ifs
      rfl
    have h2 : localNodeConn ends (upto (σ K) i) x y = ((Fintype.card V - 1 : ℕ) : ℕ∞) := by
      unfold localNodeConn
      split_ifs
      rfl
    rw [h1, h2]
    exact min_le_left _ _
  · have h2 : localNodeConn ends (upto (σ K) i) x y =
        ⨅ W ∈ {W : Finset V | x ∉ W ∧ y ∉ W ∧ ¬ ConnAvoid ends (upto (σ K) i) W x y},
          (W.card : ℕ∞) := by
      unfold localNodeConn
      split_ifs
      rfl
    rw [h2]
    refine le_iInf₂ fun W hW => ?_
    obtain ⟨hxW, hyW, hnc⟩ := hW
    by_cases hWi : W.card < i
    · have hnG : ¬ (edgeGraph ends Finset.univ).Adj x y := fun h =>
        hnc (ni31_edge_conn hloop hsimple hrun i W hWi x y hxW hyW h)
      have hncG : ¬ ConnAvoid ends Finset.univ W x y := fun h =>
        hnc (ni31_lift hloop hsimple hrun i W hWi x y h)
      have h1 : localNodeConn ends Finset.univ x y =
          ⨅ W ∈ {W : Finset V | x ∉ W ∧ y ∉ W ∧ ¬ ConnAvoid ends Finset.univ W x y},
            (W.card : ℕ∞) := by
        unfold localNodeConn
        split_ifs
        rfl
      calc min (localNodeConn ends Finset.univ x y) (i : ℕ∞)
          ≤ localNodeConn ends Finset.univ x y := min_le_left _ _
        _ = ⨅ W ∈ {W : Finset V | x ∉ W ∧ y ∉ W ∧ ¬ ConnAvoid ends Finset.univ W x y},
            (W.card : ℕ∞) := h1
        _ ≤ (W.card : ℕ∞) := iInf₂_le W ⟨hxW, hyW, hncG⟩
    · calc min (localNodeConn ends Finset.univ x y) (i : ℕ∞) ≤ (i : ℕ∞) := min_le_right _ _
        _ ≤ (W.card : ℕ∞) := by exact_mod_cast (not_lt.mp hWi)
