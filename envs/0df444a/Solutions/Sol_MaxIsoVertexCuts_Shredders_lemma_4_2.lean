-- Prove2me | solution 1 for MaxIsoVertexCuts.Shredders.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T16:53:41.70013+00:00
-- url     : https://prove2.me/submissions/444a1f06-5d13-49eb-8be4-00e181532454

import Definitions.Def_MaxIsoVertexCuts_Shredders_CollectionTargets

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders.L42Aux

open MaxIsoVertexCuts.Shredders

variable {n : ℕ} {G : SimpleGraph (Fin n)} {w : Fin n → ℝ}

lemma weight_eq (w : Fin n → ℝ) (X : VSet n) :
    weight w X = ∑ v, if v ∈ X then w v else 0 := by
  unfold weight; rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma eq_of_sub_weight (hw : Positive w) {X Y : VSet n} (hXY : X ⊆ Y)
    (h : weight w Y ≤ weight w X) : X = Y := by
  by_contra hne
  have hss : X ⊂ Y := Finset.ssubset_iff_subset_ne.mpr ⟨hXY, hne⟩
  obtain ⟨i, hiY, hiX⟩ := Finset.exists_of_ssubset hss
  have := Finset.sum_lt_sum_of_subset hXY hiY hiX (hw i) (fun j _ _ => (hw j).le)
  unfold weight at h; linarith

lemma cut_facts {c : Cut n} (h : IsCut G c) (v : Fin n) :
    (v ∈ c.L ∨ v ∈ c.S ∨ v ∈ c.R) ∧ ¬(v ∈ c.L ∧ v ∈ c.S) ∧ ¬(v ∈ c.L ∧ v ∈ c.R) ∧
      ¬(v ∈ c.S ∧ v ∈ c.R) := by
  obtain ⟨h1, h2, h3, h4, _⟩ := h
  refine ⟨?_, fun ⟨a, b⟩ => Finset.disjoint_left.mp h1 a b,
    fun ⟨a, b⟩ => Finset.disjoint_left.mp h2 a b, fun ⟨a, b⟩ => Finset.disjoint_left.mp h3 a b⟩
  have : v ∈ c.L ∪ c.S ∪ c.R := by rw [h4]; exact Finset.mem_univ v
  simp only [Finset.mem_union] at this; tauto

lemma mk_cut {L S R : VSet n}
    (hp : ∀ v, (v ∈ L ∨ v ∈ S ∨ v ∈ R) ∧ ¬(v ∈ L ∧ v ∈ S) ∧ ¬(v ∈ L ∧ v ∈ R) ∧
      ¬(v ∈ S ∧ v ∈ R))
    (he : ∀ u ∈ L, ∀ v ∈ R, ¬ G.Adj u v) : IsCut G ⟨L, S, R⟩ := by
  refine ⟨Finset.disjoint_left.mpr fun {v} a b => (hp v).2.1 ⟨a, b⟩,
    Finset.disjoint_left.mpr fun {v} a b => (hp v).2.2.1 ⟨a, b⟩,
    Finset.disjoint_left.mpr fun {v} a b => (hp v).2.2.2 ⟨a, b⟩, ?_, he⟩
  ext v
  simp only [Finset.mem_union, Finset.mem_univ, iff_true]
  have := (hp v).1; tauto

lemma S_sub (hw : Positive w) {X Y : VSet n} {c d : Cut n} (hc : IsMinCut G w X Y c)
    (hd : IsXYCut G X Y d) (hL : c.L = d.L) : c.S ⊆ d.S := by
  obtain ⟨⟨hX, hY, hXY, hcut, hXL, hYR⟩, hmin⟩ := hc
  obtain ⟨_, _, _, hdcut, _, hdY⟩ := hd
  have he : IsXYCut G X Y ⟨c.L, c.S ∩ d.S, c.R ∪ d.R⟩ := by
    refine ⟨hX, hY, hXY, mk_cut ?_ ?_, hXL, fun y hy => Finset.mem_union_left _ (hYR hy)⟩
    · intro v
      have f1 := cut_facts hcut v
      have f2 := cut_facts hdcut v
      rw [← hL] at f2
      simp only [Finset.mem_inter, Finset.mem_union]
      generalize hpp1 : (v ∈ c.L) = p1 at *
      generalize hpp2 : (v ∈ c.S) = p2 at *
      generalize hpp3 : (v ∈ c.R) = p3 at *
      generalize hpp4 : (v ∈ d.S) = p4 at *
      generalize hpp5 : (v ∈ d.R) = p5 at *
      itauto!
    · intro u hu v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact hcut.2.2.2.2 u hu v hv
      · exact hdcut.2.2.2.2 u (hL ▸ hu) v hv
  have h1 := hmin _ he
  have := eq_of_sub_weight hw (Finset.inter_subset_left (s₁ := c.S) (s₂ := d.S)) h1
  rw [← this]; exact Finset.inter_subset_right

lemma min_cut_unique (hw : Positive w) {X Y : VSet n} {c d : Cut n} (hc : IsMinCut G w X Y c)
    (hd : IsMinCut G w X Y d) (hL : c.L = d.L) : c = d := by
  have hS : c.S = d.S :=
    Finset.Subset.antisymm (S_sub hw hc hd.1 hL) (S_sub hw hd hc.1 hL.symm)
  have hR : c.R = d.R := by
    ext v
    have f1 := cut_facts hc.1.2.2.2.1 v
    have f2 := cut_facts hd.1.2.2.2.1 v
    rw [← hL, ← hS] at f2
    tauto
  obtain ⟨L1, S1, R1⟩ := c
  obtain ⟨L2, S2, R2⟩ := d
  simp only at hL hS hR
  subst hL hS hR
  rfl

/-- union of two minimum cuts -/
def cupCut (c1 c2 : Cut n) : Cut n :=
  ⟨c1.L ∪ c2.L, Finset.univ.filter (fun v => v ∉ c1.L ∧ v ∉ c2.L ∧ ¬(v ∈ c1.R ∧ v ∈ c2.R)),
    c1.R ∩ c2.R⟩

def capCut (c1 c2 : Cut n) : Cut n :=
  ⟨c1.L ∩ c2.L, Finset.univ.filter (fun v => ¬(v ∈ c1.L ∧ v ∈ c2.L) ∧ v ∉ c1.R ∧ v ∉ c2.R),
    c1.R ∪ c2.R⟩

lemma cup_min (hw : Positive w) {X Y : VSet n} {c1 c2 : Cut n} (h1 : IsMinCut G w X Y c1)
    (h2 : IsMinCut G w X Y c2) : IsMinCut G w X Y (cupCut c1 c2) := by
  obtain ⟨⟨hX, hY, hXY, hc1, hXL1, hYR1⟩, hmin1⟩ := h1
  obtain ⟨⟨_, _, _, hc2, hXL2, hYR2⟩, hmin2⟩ := h2
  have hcup : IsXYCut G X Y (cupCut c1 c2) := by
    refine ⟨hX, hY, hXY, mk_cut ?_ ?_, fun x hx => Finset.mem_union_left _ (hXL1 hx),
      Finset.subset_inter hYR1 hYR2⟩
    · intro v
      have f1 := cut_facts hc1 v
      have f2 := cut_facts hc2 v
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      generalize hpp1 : (v ∈ c1.L) = p1 at *
      generalize hpp2 : (v ∈ c1.S) = p2 at *
      generalize hpp3 : (v ∈ c1.R) = p3 at *
      generalize hpp4 : (v ∈ c2.L) = p4 at *
      generalize hpp5 : (v ∈ c2.S) = p5 at *
      generalize hpp6 : (v ∈ c2.R) = p6 at *
      itauto!
    · intro u hu v hv
      rcases Finset.mem_union.mp hu with hu | hu
      · exact hc1.2.2.2.2 u hu v (Finset.mem_inter.mp hv).1
      · exact hc2.2.2.2.2 u hu v (Finset.mem_inter.mp hv).2
  have hcap : IsXYCut G X Y (capCut c1 c2) := by
    refine ⟨hX, hY, hXY, mk_cut ?_ ?_, Finset.subset_inter hXL1 hXL2,
      fun y hy => Finset.mem_union_left _ (hYR1 hy)⟩
    · intro v
      have f1 := cut_facts hc1 v
      have f2 := cut_facts hc2 v
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      generalize hpp1 : (v ∈ c1.L) = p1 at *
      generalize hpp2 : (v ∈ c1.S) = p2 at *
      generalize hpp3 : (v ∈ c1.R) = p3 at *
      generalize hpp4 : (v ∈ c2.L) = p4 at *
      generalize hpp5 : (v ∈ c2.S) = p5 at *
      generalize hpp6 : (v ∈ c2.R) = p6 at *
      itauto!
    · intro u hu v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact hc1.2.2.2.2 u (Finset.mem_inter.mp hu).1 v hv
      · exact hc2.2.2.2.2 u (Finset.mem_inter.mp hu).2 v hv
  have hsub : weight w (cupCut c1 c2).S + weight w (capCut c1 c2).S ≤
      weight w c1.S + weight w c2.S := by
    rw [weight_eq, weight_eq, weight_eq, weight_eq, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro v _
    have f1 := cut_facts hc1 v
    have f2 := cut_facts hc2 v
    have hv := hw v
    simp only [cupCut, capCut, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> (try linarith)
    all_goals
      exfalso
      generalize hpp1 : (v ∈ c1.L) = p1 at *
      generalize hpp2 : (v ∈ c1.S) = p2 at *
      generalize hpp3 : (v ∈ c1.R) = p3 at *
      generalize hpp4 : (v ∈ c2.L) = p4 at *
      generalize hpp5 : (v ∈ c2.S) = p5 at *
      generalize hpp6 : (v ∈ c2.R) = p6 at *
      itauto!
  refine ⟨hcup, fun d hd => ?_⟩
  have := hmin1 _ hcap
  have := hmin2 d hd
  linarith

lemma reachIn_mono {L L' : VSet n} (hL : L ⊆ L') {u v : Fin n} (h : ReachIn G L u v) :
    ReachIn G L' u v := by
  obtain ⟨hu, hv, hr⟩ := h
  exact ⟨hL hu, hL hv, hr.map (G.induceHomOfLE (Finset.coe_subset.mpr hL)).toHom⟩

lemma areach_union {L1 L2 A : VSet n} (h1 : AReachable G L1 A) (h2 : AReachable G L2 A) :
    AReachable G (L1 ∪ L2) A := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨a, ha, hr⟩ := h1 x hx
    exact ⟨a, ha, reachIn_mono Finset.subset_union_left hr⟩
  · obtain ⟨a, ha, hr⟩ := h2 x hx
    exact ⟨a, ha, reachIn_mono Finset.subset_union_right hr⟩

lemma reachIn_adj {L : VSet n} {u v a : Fin n} (hv : v ∈ L) (huv : G.Adj u v)
    (h : ReachIn G L u a) : ReachIn G L v a := by
  obtain ⟨hu, ha, hr⟩ := h
  refine ⟨hv, ha, SimpleGraph.Reachable.trans ?_ hr⟩
  apply SimpleGraph.Adj.reachable
  exact huv.symm

/-- restriction of `L` to what is reachable from `A` -/
def restr (G : SimpleGraph (Fin n)) (L A : VSet n) : VSet n :=
  L.filter (fun x => ∃ a ∈ A, ReachIn G L x a)

lemma restr_closed {L A : VSet n} {u v : Fin n} (hu : u ∈ restr G L A) (hv : v ∈ L)
    (huv : G.Adj u v) : v ∈ restr G L A := by
  simp only [restr, Finset.mem_filter] at hu ⊢
  obtain ⟨_, a, ha, hr⟩ := hu
  exact ⟨hv, a, ha, reachIn_adj hv huv hr⟩

lemma restr_reach {L A : VSet n} :
    ∀ (y z : ↥(L : Set (Fin n))) (p : (G.induce (L : Set (Fin n))).Walk y z)
      (hy : y.1 ∈ restr G L A) (hz : z.1 ∈ restr G L A),
      (G.induce (restr G L A : Set (Fin n))).Reachable ⟨y.1, hy⟩ ⟨z.1, hz⟩ := by
  intro y z p
  induction p with
  | nil => intro hy hz; rfl
  | @cons y y' z h p ih =>
    intro hy hz
    have hy' : y'.1 ∈ restr G L A := restr_closed hy (Finset.mem_coe.mp y'.2) h
    refine SimpleGraph.Reachable.trans ?_ (ih hy' hz)
    apply SimpleGraph.Adj.reachable
    exact h

lemma restr_areach {L A : VSet n} (hAL : A ⊆ L) : AReachable G (restr G L A) A := by
  intro x hx
  have hx' := hx
  simp only [restr, Finset.mem_filter] at hx'
  obtain ⟨hxL, a, ha, hxL', haL, hr⟩ := hx'
  have haR : a ∈ restr G L A := by
    simp only [restr, Finset.mem_filter]
    exact ⟨hAL ha, a, ha, hAL ha, hAL ha, SimpleGraph.Reachable.refl _⟩
  obtain ⟨p⟩ := hr
  exact ⟨a, ha, hx, haR, restr_reach _ _ p hx haR⟩

lemma exists_areach_min {X Y : VSet n} {c : Cut n} (hc : IsMinCut G w X Y c) :
    ∃ d, IsMinCut G w X Y d ∧ AReachable G d.L X := by
  obtain ⟨⟨hX, hY, hXY, hcut, hXL, hYR⟩, hmin⟩ := hc
  refine ⟨⟨restr G c.L X, c.S, c.R ∪ (c.L \ restr G c.L X)⟩, ⟨⟨hX, hY, hXY, mk_cut ?_ ?_, ?_,
    fun y hy => Finset.mem_union_left _ (hYR hy)⟩, fun d hd => hmin d hd⟩,
    restr_areach hXL⟩
  · intro v
    have f1 := cut_facts hcut v
    have hsub : v ∈ restr G c.L X → v ∈ c.L := fun h => (Finset.mem_filter.mp h).1
    simp only [Finset.mem_union, Finset.mem_sdiff]
    generalize hpp1 : (v ∈ c.L) = p1 at *
    generalize hpp2 : (v ∈ c.S) = p2 at *
    generalize hpp3 : (v ∈ c.R) = p3 at *
    generalize hpp4 : (v ∈ restr G c.L X) = p4 at *
    clear hpp1 hpp2 hpp3 hpp4 hmin
    by_cases p1 <;> by_cases p2 <;> by_cases p3 <;> by_cases p4 <;> simp_all
  · intro u hu v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hcut.2.2.2.2 u (Finset.mem_filter.mp hu).1 v hv
    · intro hadj
      exact (Finset.mem_sdiff.mp hv).2 (restr_closed hu (Finset.mem_sdiff.mp hv).1 hadj)
  · intro a ha
    simp only [restr, Finset.mem_filter]
    exact ⟨hXL ha, a, ha, hXL ha, hXL ha, SimpleGraph.Reachable.refl _⟩

end MaxIsoVertexCuts.Shredders.L42Aux

open MaxIsoVertexCuts.Shredders MaxIsoVertexCuts.Shredders.L42Aux

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℝ)
    (hw : Positive w) (T A : VSet n) (hT : Independent G T)
    (hA : A.Nonempty) (hAT : A ⊂ T) : ∃! c, IsMaxMinCut G w T A c := by
  have hY : (T \ A).Nonempty := Finset.sdiff_nonempty.mpr hAT.2
  have hdisj : Disjoint A (T \ A) := Finset.disjoint_sdiff
  have c0 : IsXYCut G A (T \ A) ⟨A, Finset.univ \ T, T \ A⟩ := by
    refine ⟨hA, hY, hdisj, mk_cut ?_ ?_, subset_refl _, subset_refl _⟩
    · intro v
      have := @hAT.1 v
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      tauto
    · intro u hu v hv
      exact hT u (hAT.1 hu) v (Finset.mem_sdiff.mp hv).1
  -- a minimum cut
  set 𝒮 := Finset.univ.filter (fun S : VSet n => ∃ d, IsXYCut G A (T \ A) d ∧ d.S = S)
  have h𝒮 : 𝒮.Nonempty := by
    refine ⟨Finset.univ \ T, ?_⟩
    simp only [𝒮, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨_, c0, rfl⟩
  obtain ⟨S0, hS0, hS0min⟩ := Finset.exists_min_image 𝒮 (weight w) h𝒮
  simp only [𝒮, Finset.mem_filter, Finset.mem_univ, true_and] at hS0
  obtain ⟨d0, hd0, rfl⟩ := hS0
  have hd0min : IsMinCut G w A (T \ A) d0 := by
    refine ⟨hd0, fun d hd => hS0min d.S ?_⟩
    simp only [𝒮, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨d, hd, rfl⟩
  obtain ⟨d1, hd1, hd1r⟩ := exists_areach_min hd0min
  -- maximal cardinality shore
  set 𝓛 := Finset.univ.filter (fun L : VSet n =>
    ∃ c, IsMinCut G w A (T \ A) c ∧ AReachable G c.L A ∧ c.L = L)
  have h𝓛 : 𝓛.Nonempty := by
    refine ⟨d1.L, ?_⟩
    simp only [𝓛, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨d1, hd1, hd1r, rfl⟩
  obtain ⟨Lm, hLm, hLmax⟩ := Finset.exists_max_image 𝓛 Finset.card h𝓛
  have hLm' := hLm
  simp only [𝓛, Finset.mem_filter, Finset.mem_univ, true_and] at hLm'
  obtain ⟨cm, hcm, hcmr, rfl⟩ := hLm'
  have hmax : ∀ d, IsMinCut G w A (T \ A) d → AReachable G d.L A → d.L ⊆ cm.L := by
    intro d hd hdr
    have hu := cup_min hw hcm hd
    have hmem : (cupCut cm d).L ∈ 𝓛 := by
      simp only [𝓛, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨_, hu, areach_union hcmr hdr, rfl⟩
    have hcard := hLmax _ hmem
    have heq : cm.L = cm.L ∪ d.L :=
      Finset.eq_of_subset_of_card_le Finset.subset_union_left hcard
    rw [heq]; exact Finset.subset_union_right
  refine ⟨cm, ⟨hcm, hcmr, hmax⟩, ?_⟩
  intro y hy
  have h1 := hmax y hy.1 hy.2.1
  have h2 := hy.2.2 cm hcm hcmr
  exact min_cut_unique hw hy.1 hcm (Finset.Subset.antisymm h1 h2)
