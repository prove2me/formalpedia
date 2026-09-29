-- Prove2me | solution 1 for NagamochiIbaraki.EdgeConn.forest_partition_theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:05:02.34903+00:00
-- url     : https://prove2.me/submissions/9ce0610e-319e-4d31-b092-a078b0461f26

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_EdgeConn_localEdgeConn
import Definitions.Def_NagamochiIbaraki_EdgeConn_Forest

namespace NagamochiIbaraki.EdgeConn

section aux_fpt

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem aux_fpt_mono (ends : E → Sym2 V) {F F' : Finset E} (h : F ⊆ F') {u v : V}
    (hr : (edgeGraph ends F).Reachable u v) : (edgeGraph ends F').Reachable u v := by
  refine SimpleGraph.Reachable.mono ?_ hr
  unfold edgeGraph
  exact SimpleGraph.fromEdgeSet_mono (Set.image_mono (by exact_mod_cast h))

theorem aux_fpt_adj (ends : E → Sym2 V) {F : Finset E} {e : E} (he : e ∈ F) {x y : V}
    (hxy : x ≠ y) (hends : ends e = s(x, y)) : (edgeGraph ends F).Adj x y := by
  unfold edgeGraph
  rw [SimpleGraph.fromEdgeSet_adj]
  exact ⟨⟨e, by simpa using he, hends⟩, hxy⟩

theorem aux_fpt_adj_inv (ends : E → Sym2 V) {F : Finset E} {x y : V}
    (h : (edgeGraph ends F).Adj x y) : ∃ e ∈ F, ends e = s(x, y) := by
  unfold edgeGraph at h
  rw [SimpleGraph.fromEdgeSet_adj] at h
  obtain ⟨⟨e, he, hends⟩, _⟩ := h
  exact ⟨e, by simpa using he, hends⟩

/-- Touched nodes: scanned nodes together with the current node. -/
def aux_fpt_touch (s : State V E) : Finset V :=
  match s.cur with
  | none => s.done
  | some x => insert x s.done

structure aux_fpt_Inv (ends : E → Sym2 V) (s : State V E) : Prop where
  curnd : ∀ x, s.cur = some x → x ∉ s.done
  doneSc : ∀ v ∈ s.done, ∀ e, v ∈ ends e → s.idx e ≠ 0
  curMax : ∀ x, s.cur = some x → ∀ v, v ∉ s.done → v ≠ x → s.r v ≤ s.r x
  conn : ∀ j, 1 ≤ j → ∀ u v, u ∉ s.done → j ≤ s.r u → v ∉ s.done → j ≤ s.r v →
    (edgeGraph ends (cls s j)).Reachable u v
  key : ∀ e j, 1 ≤ j → j < s.idx e → ∀ u v, ends e = s(u, v) →
    (edgeGraph ends (cls s j)).Reachable u v
  rbound : ∀ v, s.r v ≤ (Finset.univ.filter (fun e => s.idx e ≠ 0)).card
  idxle : ∀ e, s.idx e ≤ Fintype.card E
  fcount : ∀ i, 1 ≤ i → cls s i ≠ ∅ →
    (cls s i).card + 1 ≤ (Finset.univ.filter (fun v => i ≤ s.r v)).card
  touched : ∀ e, s.idx e ≠ 0 → ∃ w, w ∈ ends e ∧ w ∈ aux_fpt_touch s
  rinc : ∀ v, s.r v ≤ (Finset.univ.filter (fun e => s.idx e ≠ 0 ∧ v ∈ ends e)).card
  cnt : Function.Injective ends → ∀ i, 1 ≤ i →
    (cls s i).card + min i (aux_fpt_touch s).card ≤
      (Finset.univ.filter (fun v => v ∉ aux_fpt_touch s ∧ i ≤ s.r v)).card +
        (aux_fpt_touch s).card

theorem aux_fpt_init (ends : E → Sym2 V) : aux_fpt_Inv ends (init : State V E) := by
  have htouch : aux_fpt_touch (init : State V E) = ∅ := by
    simp [aux_fpt_touch, init]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; simp [init] at hx
  · intro v hv; simp [init] at hv
  · intro x hx; simp [init] at hx
  · intro j hj u v _ hju; simp [init] at hju; omega
  · intro e j _ hj; simp [init] at hj
  · intro v; simp [init]
  · intro e; simp [init]
  · intro i hi hne
    exfalso; apply hne
    ext e
    simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false]
    show ¬ (0 = i); omega
  · intro e he; simp [init] at he
  · intro v; simp [init]
  · intro _ i hi
    have : cls (init : State V E) i = ∅ := by
      ext e
      simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      show ¬ (0 = i); omega
    rw [this, htouch]; simp

theorem aux_fpt_step (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    {s t : State V E} (hs : aux_fpt_Inv ends s) (hst : Step ends s t) : aux_fpt_Inv ends t := by
  rcases hst with ⟨x, hcur, hxd, hmax, ht⟩ | ⟨x, y, e, hcur, hidx0, hends, ht⟩ |
      ⟨x, hcur, hall, ht⟩
  · -- select
    have hd : t.done = s.done := by rw [ht]
    have hc : t.cur = some x := by rw [ht]
    have hr : t.r = s.r := by rw [ht]
    have hi : t.idx = s.idx := by rw [ht]
    have hcls : ∀ j, cls t j = cls s j := by intro j; unfold cls; rw [hi]
    have hts : aux_fpt_touch s = s.done := by unfold aux_fpt_touch; rw [hcur]
    have htt : aux_fpt_touch t = insert x s.done := by unfold aux_fpt_touch; rw [hc, hd]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x' hx'; rw [hc] at hx'; cases hx'; rw [hd]; exact hxd
    · intro v hv f hvf; rw [hd] at hv; rw [hi]; exact hs.doneSc v hv f hvf
    · intro x' hx' v hv hvx; rw [hc] at hx'; cases hx'; rw [hd] at hv; rw [hr]
      exact hmax v hv
    · intro j hj u v hu hju hv hjv; rw [hcls]; rw [hd] at hu hv; rw [hr] at hju hjv
      exact hs.conn j hj u v hu hju hv hjv
    · intro f j hj hjf u v huv; rw [hcls]; rw [hi] at hjf; exact hs.key f j hj hjf u v huv
    · intro v; rw [hr, hi]; exact hs.rbound v
    · intro f; rw [hi]; exact hs.idxle f
    · intro i hi' hne; rw [hcls] at hne ⊢; rw [hr]; exact hs.fcount i hi' hne
    · intro f hf; rw [hi] at hf
      obtain ⟨w, hw, hwt⟩ := hs.touched f hf
      rw [hts] at hwt; rw [htt]
      exact ⟨w, hw, Finset.mem_insert_of_mem hwt⟩
    · intro v; rw [hr, hi]; exact hs.rinc v
    · intro hinj i hi'
      have hrx : s.r x ≤ s.done.card := by
        refine (hs.rinc x).trans ?_
        have hsub : (Finset.univ.filter (fun e => s.idx e ≠ 0 ∧ x ∈ ends e)).image ends ⊆
            s.done.image (fun w => s(x, w)) := by
          intro z hz
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
          obtain ⟨e, ⟨he0, hxe⟩, rfl⟩ := hz
          obtain ⟨w, hwe, hwt⟩ := hs.touched e he0
          rw [hts] at hwt
          have hwx : x ≠ w := fun h => hxd (h ▸ hwt)
          exact ⟨w, hwt, ((Sym2.mem_and_mem_iff hwx).mp ⟨hxe, hwe⟩).symm⟩
        calc (Finset.univ.filter (fun e => s.idx e ≠ 0 ∧ x ∈ ends e)).card
            = ((Finset.univ.filter (fun e => s.idx e ≠ 0 ∧ x ∈ ends e)).image ends).card :=
              (Finset.card_image_of_injective _ hinj).symm
          _ ≤ (s.done.image (fun w => s(x, w))).card := Finset.card_le_card hsub
          _ ≤ s.done.card := Finset.card_image_le
      have h1 := hs.cnt hinj i hi'
      rw [hts] at h1
      rw [htt, hcls, hr, Finset.card_insert_of_notMem hxd]
      by_cases hix : i ≤ s.r x
      · have hsub : Finset.univ.filter (fun v => v ∉ s.done ∧ i ≤ s.r v) ⊆
            insert x (Finset.univ.filter (fun v => v ∉ insert x s.done ∧ i ≤ s.r v)) := by
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hv ⊢
          by_cases hvx : v = x
          · exact Or.inl hvx
          · exact Or.inr ⟨fun h => h.elim hvx hv.1, hv.2⟩
        have h2 := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
        have h3 : min i (s.done.card + 1) = i := min_eq_left (by omega)
        have h4 : min i s.done.card = i := min_eq_left (by omega)
        rw [h4] at h1; rw [h3]; omega
      · have hsub : Finset.univ.filter (fun v => v ∉ s.done ∧ i ≤ s.r v) ⊆
            Finset.univ.filter (fun v => v ∉ insert x s.done ∧ i ≤ s.r v) := by
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hv ⊢
          refine ⟨fun h => h.elim (fun h' => ?_) hv.1, hv.2⟩
          subst h'; exact hix hv.2
        have h2 := Finset.card_le_card hsub
        have h3 : min i (s.done.card + 1) ≤ min i s.done.card + 1 := by
          rcases le_total i s.done.card with h | h
          · rw [min_eq_left h, min_eq_left (by omega)]; omega
          · rw [min_eq_right h]; exact min_le_right _ _
        omega
  · -- scan
    have hxy : x ≠ y := by
      intro h; apply hloop e; rw [hends, h]; exact Sym2.mk_isDiag_iff.mpr rfl
    have hxd : x ∉ s.done := hs.curnd x hcur
    have hyd : y ∉ s.done := fun h =>
      hs.doneSc y h e (by rw [hends]; exact Sym2.mem_mk_right x y) hidx0
    have hyx : s.r y ≤ s.r x := hs.curMax x hcur y hyd (Ne.symm hxy)
    have hd : t.done = s.done := by rw [ht]
    have hc : t.cur = s.cur := by rw [ht]
    have hie : t.idx e = s.r y + 1 := by rw [ht]; simp
    have hif : ∀ f, f ≠ e → t.idx f = s.idx f := by
      intro f hf; rw [ht]; simp [Function.update_of_ne hf]
    have hry : t.r y = s.r y + 1 := by rw [ht]; simp
    have hrx : t.r x = if s.r x = s.r y then s.r x + 1 else s.r x := by
      rw [ht]; simp [Function.update_of_ne hxy]
    have hrv : ∀ v, v ≠ x → v ≠ y → t.r v = s.r v := by
      intro v h1 h2; rw [ht]; simp [Function.update_of_ne h1, Function.update_of_ne h2]
    have hrmono : ∀ v, s.r v ≤ t.r v := by
      intro v
      by_cases h1 : v = x
      · rw [h1, hrx]; split_ifs <;> omega
      by_cases h2 : v = y
      · rw [h2, hry]; omega
      rw [hrv v h1 h2]
    have hrle : ∀ v, t.r v ≤ s.r v + 1 := by
      intro v
      by_cases h1 : v = x
      · rw [h1, hrx]; split_ifs <;> omega
      by_cases h2 : v = y
      · rw [h2, hry]
      rw [hrv v h1 h2]; omega
    have hrxk : s.r y + 1 ≤ t.r x := by rw [hrx]; split_ifs <;> omega
    have hrdown : ∀ v j, j ≠ s.r y + 1 → j ≤ t.r v → j ≤ s.r v := by
      intro v j hj hjv
      by_cases h1 : v = x
      · rw [h1] at hjv ⊢; rw [hrx] at hjv; split_ifs at hjv <;> omega
      by_cases h2 : v = y
      · rw [h2] at hjv ⊢; rw [hry] at hjv; omega
      rwa [hrv v h1 h2] at hjv
    have hen : e ∉ cls s (s.r y + 1) := by simp [cls, hidx0]
    have hclsk : cls t (s.r y + 1) = insert e (cls s (s.r y + 1)) := by
      ext f
      by_cases hf : f = e
      · subst hf; simp [cls, hie]
      · simp [cls, hif f hf, hf]
    have hclsj : ∀ j, j ≠ s.r y + 1 → 1 ≤ j → cls t j = cls s j := by
      intro j hj hj1
      ext f
      by_cases hf : f = e
      · subst hf; simp [cls, hie, hidx0]; omega
      · simp [cls, hif f hf]
    have hclssub : ∀ j, 1 ≤ j → cls s j ⊆ cls t j := by
      intro j hj
      by_cases hjk : j = s.r y + 1
      · rw [hjk, hclsk]; exact Finset.subset_insert _ _
      · rw [hclsj j hjk hj]
    have hscan : Finset.univ.filter (fun f => t.idx f ≠ 0) =
        insert e (Finset.univ.filter (fun f => s.idx f ≠ 0)) := by
      ext f
      by_cases hf : f = e
      · subst hf; simp [hie]
      · simp [hif f hf, hf]
    have htouch : aux_fpt_touch t = aux_fpt_touch s := by unfold aux_fpt_touch; rw [hc, hd]
    have hts : aux_fpt_touch s = insert x s.done := by unfold aux_fpt_touch; rw [hcur]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x' hx'; rw [hc] at hx'; rw [hd]; exact hs.curnd x' hx'
    · intro v hv f hvf; rw [hd] at hv
      by_cases hf : f = e
      · rw [hf, hie]; omega
      · rw [hif f hf]; exact hs.doneSc v hv f hvf
    · intro x' hx' v hv hvx
      rw [hc, hcur] at hx'; cases hx'
      rw [hd] at hv
      by_cases hvy : v = y
      · rw [hvy, hry]; exact hrxk
      · rw [hrv v hvx hvy]; exact (hs.curMax x hcur v hv hvx).trans (hrmono x)
    · intro j hj u v hu hju hv hjv
      rw [hd] at hu hv
      by_cases hjk : j = s.r y + 1
      · subst hjk
        have hreach : ∀ w, w ∉ s.done → s.r y + 1 ≤ t.r w →
            (edgeGraph ends (cls t (s.r y + 1))).Reachable x w := by
          intro w hw hwk
          by_cases hwx : w = x
          · rw [hwx]
          by_cases hwy : w = y
          · rw [hwy]
            exact (aux_fpt_adj ends (by rw [hclsk]; exact Finset.mem_insert_self _ _)
              hxy hends).reachable
          rw [hrv w hwx hwy] at hwk
          have hwx' := hs.curMax x hcur w hw hwx
          exact aux_fpt_mono ends (hclssub _ hj) (hs.conn _ hj x w hxd (by omega) hw hwk)
        exact (hreach u hu hju).symm.trans (hreach v hv hjv)
      · exact aux_fpt_mono ends (hclssub j hj)
          (hs.conn j hj u v hu (hrdown u j hjk hju) hv (hrdown v j hjk hjv))
    · intro f j hj hjf u v huv
      by_cases hf : f = e
      · rw [hf, hie] at hjf
        rw [hf, hends] at huv
        have hr : (edgeGraph ends (cls s j)).Reachable x y :=
          hs.conn j hj x y hxd (by omega) hyd (by omega)
        have hr' := aux_fpt_mono ends (hclssub j hj) hr
        rcases Sym2.eq_iff.mp huv with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← h1, ← h2]; exact hr'
        · rw [← h1, ← h2]; exact hr'.symm
      · rw [hif f hf] at hjf
        exact aux_fpt_mono ends (hclssub j hj) (hs.key f j hj hjf u v huv)
    · intro v
      rw [hscan, Finset.card_insert_of_notMem (by simp [hidx0])]
      exact (hrle v).trans (Nat.add_le_add_right (hs.rbound v) 1)
    · intro f
      by_cases hf : f = e
      · rw [hf, hie]
        have h1 := hs.rbound y
        have h2 : (Finset.univ.filter (fun f => s.idx f ≠ 0)).card < Fintype.card E := by
          rw [← Finset.card_univ]
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
          exact ⟨e, Finset.mem_univ _, by simp [hidx0]⟩
        omega
      · rw [hif f hf]; exact hs.idxle f
    · intro i hi hne
      by_cases hik : i = s.r y + 1
      · subst hik
        rw [hclsk] at hne ⊢
        rw [Finset.card_insert_of_notMem hen]
        by_cases hemp : cls s (s.r y + 1) = ∅
        · rw [hemp, Finset.card_empty]
          have hsub : ({x, y} : Finset V) ⊆
              Finset.univ.filter (fun v => s.r y + 1 ≤ t.r v) := by
            intro w hw
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with hw | hw
            · rw [hw]; simpa using hrxk
            · rw [hw]; simp [hry]
          have h2 := Finset.card_le_card hsub
          rw [Finset.card_pair hxy] at h2
          omega
        · have h1 := hs.fcount _ hi hemp
          have hsub : insert y (Finset.univ.filter (fun v => s.r y + 1 ≤ s.r v)) ⊆
              Finset.univ.filter (fun v => s.r y + 1 ≤ t.r v) := by
            intro w hw
            rw [Finset.mem_insert] at hw
            rcases hw with hw | hw
            · rw [hw]; simp [hry]
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
              exact hw.trans (hrmono w)
          have h2 := Finset.card_le_card hsub
          rw [Finset.card_insert_of_notMem (by simp)] at h2
          omega
      · rw [hclsj i hik hi] at hne ⊢
        have h1 := hs.fcount i hi hne
        have h2 : (Finset.univ.filter (fun v => i ≤ s.r v)).card ≤
            (Finset.univ.filter (fun v => i ≤ t.r v)).card := by
          apply Finset.card_le_card
          intro w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro h; exact h.trans (hrmono w)
        omega
    · intro f hf
      rw [htouch]
      by_cases hfe : f = e
      · refine ⟨x, ?_, ?_⟩
        · rw [hfe, hends]; exact Sym2.mem_mk_left x y
        · rw [hts]; exact Finset.mem_insert_self _ _
      · rw [hif f hfe] at hf; exact hs.touched f hf
    · intro v
      have hsub0 : Finset.univ.filter (fun f => s.idx f ≠ 0 ∧ v ∈ ends f) ⊆
          Finset.univ.filter (fun f => t.idx f ≠ 0 ∧ v ∈ ends f) := by
        intro f hf
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
        refine ⟨?_, hf.2⟩
        by_cases hfe : f = e
        · rw [hfe, hie]; omega
        · rw [hif f hfe]; exact hf.1
      by_cases hv : v ∈ ends e
      · have hsub : insert e (Finset.univ.filter (fun f => s.idx f ≠ 0 ∧ v ∈ ends f)) ⊆
            Finset.univ.filter (fun f => t.idx f ≠ 0 ∧ v ∈ ends f) := by
          intro f hf
          rw [Finset.mem_insert] at hf
          rcases hf with hf | hf
          · rw [hf]; simp [hie, hv]
          · exact hsub0 hf
        have h2 := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem (by simp [hidx0])] at h2
        have h1 := hs.rinc v
        have h3 := hrle v
        omega
      · have hvx : v ≠ x := by
          rintro rfl; apply hv; rw [hends]; exact Sym2.mem_mk_left _ _
        have hvy : v ≠ y := by
          rintro rfl; apply hv; rw [hends]; exact Sym2.mem_mk_right _ _
        rw [hrv v hvx hvy]
        exact (hs.rinc v).trans (Finset.card_le_card hsub0)
    · intro hinj i hi
      rw [htouch]
      have h1 := hs.cnt hinj i hi
      have hUsub : Finset.univ.filter (fun v => v ∉ aux_fpt_touch s ∧ i ≤ s.r v) ⊆
          Finset.univ.filter (fun v => v ∉ aux_fpt_touch s ∧ i ≤ t.r v) := by
        intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        exact ⟨hw.1, hw.2.trans (hrmono w)⟩
      by_cases hik : i = s.r y + 1
      · subst hik
        rw [hclsk, Finset.card_insert_of_notMem hen]
        have hyt : y ∉ aux_fpt_touch s := by
          rw [hts, Finset.mem_insert]; rintro (h | h)
          · exact hxy h.symm
          · exact hyd h
        have hsub : insert y (Finset.univ.filter
              (fun v => v ∉ aux_fpt_touch s ∧ s.r y + 1 ≤ s.r v)) ⊆
            Finset.univ.filter (fun v => v ∉ aux_fpt_touch s ∧ s.r y + 1 ≤ t.r v) := by
          intro w hw
          rw [Finset.mem_insert] at hw
          rcases hw with hw | hw
          · rw [hw]; simp [hry, hyt]
          · exact hUsub hw
        have h2 := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem (by simp)] at h2
        omega
      · rw [hclsj i hik hi]
        have h2 := Finset.card_le_card hUsub
        omega
  · -- finish
    have hd : t.done = insert x s.done := by rw [ht]
    have hc : t.cur = none := by rw [ht]
    have hr : t.r = s.r := by rw [ht]
    have hi : t.idx = s.idx := by rw [ht]
    have hcls : ∀ j, cls t j = cls s j := by intro j; unfold cls; rw [hi]
    have htouch : aux_fpt_touch t = aux_fpt_touch s := by
      unfold aux_fpt_touch; rw [hc, hcur, hd]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x' hx'; rw [hc] at hx'; cases hx'
    · intro v hv f hvf
      rw [hd, Finset.mem_insert] at hv
      rw [hi]
      rcases hv with hv | hv
      · rw [hv] at hvf; exact hall f hvf
      · exact hs.doneSc v hv f hvf
    · intro x' hx'; rw [hc] at hx'; cases hx'
    · intro j hj u v hu hju hv hjv
      rw [hcls]; rw [hr] at hju hjv; rw [hd] at hu hv
      exact hs.conn j hj u v (fun h => hu (Finset.mem_insert_of_mem h)) hju
        (fun h => hv (Finset.mem_insert_of_mem h)) hjv
    · intro f j hj hjf u v huv; rw [hcls]; rw [hi] at hjf; exact hs.key f j hj hjf u v huv
    · intro v; rw [hr, hi]; exact hs.rbound v
    · intro f; rw [hi]; exact hs.idxle f
    · intro i hi' hne; rw [hcls] at hne ⊢; rw [hr]; exact hs.fcount i hi' hne
    · intro f hf; rw [hi] at hf; rw [htouch]; exact hs.touched f hf
    · intro v; rw [hr, hi]; exact hs.rinc v
    · intro hinj i hi'; rw [htouch, hcls, hr]; exact hs.cnt hinj i hi'

theorem aux_fpt_part2 (ends : E → Sym2 V) (s : State V E)
    (hpos : ∀ e, 1 ≤ s.idx e)
    (hkey : ∀ e j, 1 ≤ j → j < s.idx e → ∀ u v, ends e = s(u, v) →
      (edgeGraph ends (cls s j)).Reachable u v)
    (i : ℕ) (x y : V) :
    min (localEdgeConn ends Finset.univ x y) (i : ℕ∞) ≤
      localEdgeConn ends (upto s i) x y := by
  classical
  unfold localEdgeConn
  apply le_iInf₂
  intro W hW
  obtain ⟨hWsub, hnr⟩ := hW
  set G := edgeGraph ends (upto s i \ W) with hG
  let X : Set V := {v | G.Reachable x v}
  have hxX : x ∈ X := SimpleGraph.Reachable.refl _
  have hyX : y ∉ X := hnr
  -- an edge of `upto s i` leaving `X` lies in `W`
  have hleave : ∀ f a b, f ∈ upto s i → ends f = s(a, b) → a ∈ X → b ∉ X → f ∈ W := by
    intro f a b hf hfab ha hb
    by_contra hfW
    apply hb
    have hab : a ≠ b := by rintro rfl; exact hb ha
    have hadj : G.Adj a b := aux_fpt_adj ends (Finset.mem_sdiff.mpr ⟨hf, hfW⟩) hab hfab
    exact SimpleGraph.Reachable.trans ha hadj.reachable
  by_cases hA : ∃ e : E, i < s.idx e ∧ ∃ a b, ends e = s(a, b) ∧ a ∈ X ∧ b ∉ X
  · obtain ⟨e, he, a, b, hab, haX, hbX⟩ := hA
    have hj : ∀ j ∈ Finset.Icc 1 i, ∃ f ∈ W, s.idx f = j := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      obtain ⟨p⟩ := hkey e j hj.1 (by omega) a b hab
      obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart X haX hbX
      obtain ⟨f, hf, hfe⟩ := aux_fpt_adj_inv ends d.adj
      have hfj : s.idx f = j := by simpa [cls] using hf
      refine ⟨f, hleave f _ _ ?_ hfe hd1 hd2, hfj⟩
      simp [upto, hfj, hj.1, hj.2]
    haveI : Nonempty E := ⟨e⟩
    choose! g hgW hgidx using hj
    have hinj : Set.InjOn g (Finset.Icc 1 i : Set ℕ) := by
      intro j₁ hj₁ j₂ hj₂ h
      rw [← hgidx j₁ hj₁, ← hgidx j₂ hj₂, h]
    have hcard := Finset.card_le_card_of_injOn g (fun j hj => hgW j hj) hinj
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at hcard
    calc min _ (i : ℕ∞) ≤ (i : ℕ∞) := min_le_right _ _
      _ ≤ (W.card : ℕ∞) := by exact_mod_cast hcard
  · push Not at hA
    let W' : Finset E := Finset.univ.filter (fun e => ∃ a b, ends e = s(a, b) ∧ a ∈ X ∧ b ∉ X)
    have hW'W : W' ⊆ W := by
      intro e he
      simp only [W', Finset.mem_filter, Finset.mem_univ, true_and] at he
      obtain ⟨a, b, hab, ha, hb⟩ := he
      have hle : s.idx e ≤ i := by
        by_contra hlt
        exact hb (hA e (by omega) a b hab ha)
      exact hleave e a b (by simp [upto, hle, hpos e]) hab ha hb
    have hW'nr : ¬ (edgeGraph ends (Finset.univ \ W')).Reachable x y := by
      rintro ⟨p⟩
      obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart X hxX hyX
      obtain ⟨f, hf, hfe⟩ := aux_fpt_adj_inv ends d.adj
      rw [Finset.mem_sdiff] at hf
      apply hf.2
      simp only [W', Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨_, _, hfe, hd1, hd2⟩
    calc min _ (i : ℕ∞) ≤ ⨅ W ∈ {W : Finset E | W ⊆ Finset.univ ∧
          ¬ (edgeGraph ends (Finset.univ \ W)).Reachable x y}, (W.card : ℕ∞) := min_le_left _ _
      _ ≤ (W'.card : ℕ∞) := iInf₂_le W' ⟨Finset.subset_univ _, hW'nr⟩
      _ ≤ (W.card : ℕ∞) := by exact_mod_cast Finset.card_le_card hW'W

end aux_fpt

end NagamochiIbaraki.EdgeConn

open NagamochiIbaraki.EdgeConn

theorem solution
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsCompletedRun ends σ K) :
    (∀ e : E, 1 ≤ (σ K).idx e ∧ (σ K).idx e ≤ Fintype.card E) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card E → ∀ x y : V,
      min (localEdgeConn ends Finset.univ x y) (i : ℕ∞) ≤
        localEdgeConn ends (upto (σ K) i) x y) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card E →
      (cls (σ K) i).card ≤ Fintype.card V - 1) ∧
    (Function.Injective ends →
      (∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card V - 1 →
        (cls (σ K) i).card ≤ Fintype.card V - i) ∧
      (∀ i : ℕ, Fintype.card V ≤ i → i ≤ Fintype.card E → cls (σ K) i = ∅)) := by
  obtain ⟨⟨h0, hstep⟩, hdone⟩ := hrun
  have hinv : ∀ k, k ≤ K → aux_fpt_Inv ends (σ k) := by
    intro k
    induction k with
    | zero => intro _; rw [h0]; exact aux_fpt_init ends
    | succ n ih =>
      intro hn
      exact aux_fpt_step ends hloop (ih (by omega)) (hstep n (by omega))
  have hI := hinv K le_rfl
  have hcur : (σ K).cur = none := by
    cases h : (σ K).cur with
    | none => rfl
    | some x =>
      exfalso
      exact hI.curnd x h (by rw [hdone]; exact Finset.mem_univ x)
  have htouch : aux_fpt_touch (σ K) = Finset.univ := by
    unfold aux_fpt_touch; rw [hcur, hdone]
  have hpos : ∀ e, 1 ≤ (σ K).idx e := by
    intro e
    have := hI.doneSc (ends e).out.1 (by rw [hdone]; exact Finset.mem_univ _) e
      (Sym2.out_fst_mem _)
    omega
  refine ⟨fun e => ⟨hpos e, hI.idxle e⟩, ?_, ?_, ?_⟩
  · intro i _ _ x y
    exact aux_fpt_part2 ends (σ K) hpos hI.key i x y
  · intro i hi _
    by_cases hne : cls (σ K) i = ∅
    · rw [hne]; simp
    · have h1 := hI.fcount i hi hne
      have h2 := Finset.card_le_univ (Finset.univ.filter (fun v => i ≤ (σ K).r v))
      omega
  · intro hinj
    have h := hI.cnt hinj
    rw [htouch] at h
    have hz : ∀ i, (Finset.univ.filter
        (fun v => v ∉ (Finset.univ : Finset V) ∧ i ≤ (σ K).r v)).card = 0 := by
      intro i; simp
    refine ⟨fun i hi hiV => ?_, fun i hiV _ => ?_⟩
    · have h1 := h i hi
      rw [hz, Finset.card_univ, min_eq_left (by omega)] at h1
      omega
    · have h1 := h i (by omega)
      rw [hz, Finset.card_univ, min_eq_right hiV] at h1
      exact Finset.card_eq_zero.mp (by omega)
