-- Prove2me | solution 1 for NicerEars.TJoin.theorem_25_twoVertexConnected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T11:28:42.756143+00:00
-- url     : https://prove2.me/submissions/9a3f6a33-e094-44d0-b8b5-07a7f85eb4f5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NicerEars_TJoin_Earmuff
import Theorems.Thm_NicerEars_TJoin_lemma_23
import Theorems.Thm_NicerEars_TJoin_theorem_24
import Theorems.Thm_NicerEars_TJoin_theorem_20
import Theorems.Thm_NicerEars_TJoin_proposition_3
import Theorems.Thm_NicerEars_TJoin_proposition_8

open Finset NicerEars.TJoin

namespace Sol25TwoVCAux

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem mk_path2 (G : NicerEars.TJoin.Graph V E) (z a r : V) (g h : E)
    (hg : G.ends g = s(z, a)) (hh : G.ends h = s(a, r))
    (hza : z ≠ a) (har : a ≠ r) (hzr : z ≠ r) :
    ∃ P : Ear G, P.IsOpen ∧ P.inner = {a} := by
  have hgh : g ≠ h := by
    intro hgh; rw [hgh, hh] at hg
    rcases Sym2.eq_iff.mp hg with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
  refine ⟨Ear.mk 2 (by norm_num) ![z, a, r] ![g, h] ?_ ?_ ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [hg, hh]
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [eq_comm, Fin.last]
  · simp [Ear.IsOpen, Ear.first, Ear.last, hzr]
  · ext v
    simp only [Ear.inner, mem_image, mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨i, ⟨h0, h1⟩, rfl⟩
      fin_cases i <;> simp_all
    · rintro rfl; exact ⟨1, by decide, by simp⟩

theorem mk_path3 (G : NicerEars.TJoin.Graph V E) (z a b r : V) (g h k : E)
    (hg : G.ends g = s(z, a)) (hh : G.ends h = s(a, b)) (hk : G.ends k = s(b, r))
    (hza : z ≠ a) (hzb : z ≠ b) (hab : a ≠ b) (har : a ≠ r) (hbr : b ≠ r) (hzr : z ≠ r) :
    ∃ P : Ear G, P.IsOpen ∧ P.inner = {a, b} := by
  have hgh : g ≠ h := by
    intro e; rw [e, hh] at hg
    rcases Sym2.eq_iff.mp hg with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
  have hgk : g ≠ k := by
    intro e; rw [e, hk] at hg
    rcases Sym2.eq_iff.mp hg with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
  have hhk : h ≠ k := by
    intro e; rw [e, hk] at hh
    rcases Sym2.eq_iff.mp hh with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
  refine ⟨Ear.mk 3 (by norm_num) ![z, a, b, r] ![g, h, k] ?_ ?_ ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [hg, hh, hk]
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [eq_comm, Fin.last]
  · simp [Ear.IsOpen, Ear.first, Ear.last, hzr]
  · ext v
    simp only [Ear.inner, mem_image, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro ⟨i, ⟨h0, h1⟩, rfl⟩
      fin_cases i <;> simp_all
    · rintro (rfl | rfl)
      · exact ⟨1, by decide, by simp⟩
      · exact ⟨2, by decide, by simp⟩


theorem inner_two {G : NicerEars.TJoin.Graph V E} (hpos : 0 < 2) (vert : Fin (2 + 1) → V) (edge : Fin 2 → E) (link) (einj) (vinj) :
    (Ear.mk (G := G) 2 hpos vert edge link einj vinj).inner = {vert 1} := by
  have : (univ.filter (fun i : Fin (2 + 1) => 0 < i.val ∧ i.val < 2)) = {1} := by decide
  simp only [Ear.inner, this, image_singleton]

theorem inner_three {G : NicerEars.TJoin.Graph V E} (hpos : 0 < 3) (vert : Fin (3 + 1) → V) (edge : Fin 3 → E) (link) (einj) (vinj) :
    (Ear.mk (G := G) 3 hpos vert edge link einj vinj).inner = {vert 1, vert 2} := by
  have : (univ.filter (fun i : Fin (3 + 1) => 0 < i.val ∧ i.val < 3)) = {1, 2} := by decide
  simp only [Ear.inner, this, image_insert, image_singleton]

theorem short_inner_eardrum (G : NicerEars.TJoin.Graph V E) (P : Ear G) (hs : P.IsShort) :
    #P.inner = 1 ∨ (#P.inner = 2 ∧ ∀ u ∈ P.inner, ∀ w ∈ P.inner, u ≠ w →
      (G.spanGraph univ).Adj u w) := by
  obtain ⟨len, hpos, vert, edge, link, einj, vinj⟩ := P
  simp only [Ear.IsShort] at hs
  rcases hs with rfl | rfl
  · left; rw [inner_two]; simp
  · right
    rw [inner_three]
    have h12 : vert 1 ≠ vert 2 := fun h => absurd (vinj _ _ h) (by decide)
    refine ⟨card_pair h12, ?_⟩
    have hadj : (G.spanGraph univ).Adj (vert 1) (vert 2) := by
      rw [NicerEars.TJoin.Graph.spanGraph, SimpleGraph.fromEdgeSet_adj]
      exact ⟨⟨edge 1, by simp, link 1⟩, h12⟩
    intro u hu w hw huw
    simp only [mem_insert, mem_singleton] at hu hw
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
    · exact absurd rfl huw
    · exact hadj
    · exact hadj.symm
    · exact absurd rfl huw

theorem inner_nonempty (G : NicerEars.TJoin.Graph V E) (P : Ear G) (hs : P.IsNontrivial) :
    P.inner.Nonempty := by
  refine ⟨P.vert ⟨1, by unfold Ear.IsNontrivial at hs; omega⟩, ?_⟩
  simp only [Ear.inner, mem_image, mem_filter, mem_univ, true_and]
  exact ⟨_, ⟨by simp, by unfold Ear.IsNontrivial at hs; simpa using hs⟩, rfl⟩

theorem first_not_mem_inner (G : NicerEars.TJoin.Graph V E) (P : Ear G) : P.first ∉ P.inner := by
  simp only [Ear.inner, Ear.first, mem_image, mem_filter, mem_univ, true_and, not_exists, not_and]
  intro i ⟨h0, h1⟩ h
  rcases P.vert_inj _ _ h with h | ⟨h, -⟩ | ⟨h, -⟩
  · subst h; simp at h0
  · subst h; simp at h0
  · subst h; simp at h1

theorem inner_subset_verts (G : NicerEars.TJoin.Graph V E) (P : Ear G) : P.inner ⊆ P.verts := by
  intro v hv
  simp only [Ear.inner, mem_image, mem_filter] at hv
  obtain ⟨i, -, rfl⟩ := hv
  simp [Ear.verts]

theorem paths_of_outside (G : NicerEars.TJoin.Graph V E) (hG : G.IsTwoVertexConnected)
    (P : Ear G) (hs : P.IsShort) (hc : P.first = P.last) (w : V) (hw : w ∉ P.inner)
    (hwr : w ≠ P.first) : (PathsThrough G P.inner).Nonempty := by
  have hnt : P.IsNontrivial := by
    unfold Ear.IsNontrivial; unfold Ear.IsShort at hs; omega
  obtain ⟨a, ha⟩ := inner_nonempty G P hnt
  have haf : a ≠ P.first := fun h => first_not_mem_inner G P (h ▸ ha)
  obtain ⟨p⟩ := hG.2 P.first ⟨a, haf⟩ ⟨w, hwr⟩
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart {x | x.1 ∈ P.inner} ha hw
  have hadj : (G.spanGraph (univ : Finset E)).Adj d.fst.1 d.snd.1 := d.adj
  simp only [NicerEars.TJoin.Graph.spanGraph, SimpleGraph.fromEdgeSet_adj] at hadj
  obtain ⟨⟨g, -, hg⟩, -⟩ := hadj
  have hzf : d.snd.1 ≠ P.first := d.snd.2
  have hy : d.fst.1 ∈ P.inner := hd1
  have hz : d.snd.1 ∉ P.inner := hd2
  generalize d.fst.1 = y at hy hg
  generalize d.snd.1 = z at hz hzf hg
  obtain ⟨len, hpos, vert, edge, link, einj, vinj⟩ := P
  simp only [Ear.IsShort] at hs
  simp only [Ear.first, Ear.last] at hc hzf
  rcases hs with rfl | rfl
  · rw [inner_two] at hy hz ⊢
    simp only [mem_singleton] at hy hz
    subst hy
    have h12 : vert 1 ≠ vert 2 := fun h => absurd (vinj _ _ h) (by decide)
    have hz2 : z ≠ vert 2 := fun h => hzf (h.trans hc.symm)
    obtain ⟨Q, hQ, hQi⟩ := mk_path2 G z (vert 1) (vert 2) g (edge 1)
      (by rw [hg, Sym2.eq_swap]) (link 1) hz h12 hz2
    exact ⟨Q, hQ, hQi⟩
  · rw [inner_three] at hy hz ⊢
    simp only [mem_insert, mem_singleton, not_or] at hy hz
    have h12 : vert 1 ≠ vert 2 := fun h => absurd (vinj _ _ h) (by decide)
    have h13 : vert 1 ≠ vert 3 := fun h => absurd (vinj _ _ h) (by decide)
    have h23 : vert 2 ≠ vert 3 := fun h => absurd (vinj _ _ h) (by decide)
    have h10 : vert 1 ≠ vert 0 := fun h => absurd (vinj _ _ h) (by decide)
    have h20 : vert 2 ≠ vert 0 := fun h => absurd (vinj _ _ h) (by decide)
    have hz3 : z ≠ vert 3 := fun h => hzf (h.trans hc.symm)
    rcases hy with rfl | rfl
    · obtain ⟨Q, hQ, hQi⟩ := mk_path3 G z (vert 1) (vert 2) (vert 3) g (edge 1) (edge 2)
        (by rw [hg, Sym2.eq_swap]) (link 1) (link 2) hz.1 hz.2 h12 h13 h23 hz3
      exact ⟨Q, hQ, hQi⟩
    · obtain ⟨Q, hQ, hQi⟩ := mk_path3 G z (vert 2) (vert 1) (vert 0) g (edge 1) (edge 0)
        (by rw [hg, Sym2.eq_swap]) (by rw [link 1, Sym2.eq_swap]; rfl)
        (by rw [link 0, Sym2.eq_swap]; rfl) hz.2 hz.1 h12.symm h20 h10 hzf
      refine ⟨Q, hQ, ?_⟩
      rw [hQi, pair_comm]


theorem root_not_mem_inner {G : NicerEars.TJoin.Graph V E} (D : EarDecomposition G) (i : Fin D.k) :
    D.root ∉ (D.ear i).inner := by
  have := (D.attach i).2.2
  exact fun h => Finset.disjoint_left.mp this h (mem_insert_self _ _)

theorem inner_disjoint_verts {G : NicerEars.TJoin.Graph V E} (D : EarDecomposition G)
    (i j : Fin D.k) (hij : i < j) : Disjoint (D.ear j).inner (D.ear i).verts := by
  have := (D.attach j).2.2
  refine Finset.disjoint_of_subset_right ?_ this
  intro v hv
  apply mem_insert_of_mem
  simp only [mem_biUnion, mem_filter, mem_univ, true_and]
  exact ⟨i, hij, hv⟩

theorem inner_disjoint {G : NicerEars.TJoin.Graph V E} (D : EarDecomposition G)
    (i j : Fin D.k) (hij : i ≠ j) : Disjoint (D.ear i).inner (D.ear j).inner := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact (Finset.disjoint_of_subset_right (inner_subset_verts G _)
      (inner_disjoint_verts D i j h)).symm
  · exact Finset.disjoint_of_subset_right (inner_subset_verts G _) (inner_disjoint_verts D j i h)

theorem mem_eardrumOf {G : NicerEars.TJoin.Graph V E} (D : EarDecomposition G) (T : Finset V)
    (f : Finset V) : f ∈ D.eardrumOf T ↔ ∃ i, D.IsClean T i ∧ (D.ear i).inner = f := by
  simp [EarDecomposition.eardrumOf]

theorem eardrumOf_isEardrum {G : NicerEars.TJoin.Graph V E} (D : EarDecomposition G) (T : Finset V)
    (hD : D.ShortEarsNonadjacent) : IsEardrum G (D.eardrumOf T) := by
  constructor
  · intro f hf
    obtain ⟨i, hi, rfl⟩ := (mem_eardrumOf D T f).mp hf
    exact short_inner_eardrum G _ hi.1
  · intro f hf g hg hfg
    obtain ⟨i, hi, rfl⟩ := (mem_eardrumOf D T f).mp hf
    obtain ⟨j, hj, rfl⟩ := (mem_eardrumOf D T g).mp hg
    have hij : i ≠ j := fun h => hfg (h ▸ rfl)
    exact ⟨inner_disjoint D i j hij, hD i j hij hi.1 hj.1⟩

theorem eardrumOf_disjoint {G : NicerEars.TJoin.Graph V E} (D : EarDecomposition G) (T : Finset V) :
    Disjoint (VM (D.eardrumOf T)) T := by
  unfold VM
  rw [Finset.disjoint_biUnion_left]
  intro f hf
  obtain ⟨i, hi, rfl⟩ := (mem_eardrumOf D T f).mp hf
  exact hi.2

theorem card_le_sum (G : NicerEars.TJoin.Graph V E) (x : E → ℝ) (hx0 : ∀ e, 0 ≤ x e)
    (hcut : ∀ v : V, 2 ≤ ∑ e ∈ G.cut {v}, x e) : (Fintype.card V : ℝ) ≤ ∑ e, x e := by
  have hfil : ∀ e : E, #(univ.filter (fun v : V => e ∈ G.cut {v})) ≤ 2 := by
    intro e
    obtain ⟨⟨p, q⟩, hpq⟩ := Quot.exists_rep (G.ends e)
    have hpq' : G.ends e = s(p, q) := hpq.symm
    calc #(univ.filter (fun v : V => e ∈ G.cut {v})) ≤ #({p, q} : Finset V) := by
          apply card_le_card
          intro v hv
          simp only [mem_filter, mem_univ, true_and, NicerEars.TJoin.Graph.cut, mem_singleton] at hv
          obtain ⟨u, rfl, w, -, h⟩ := hv
          rw [hpq'] at h
          rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h1⟩ <;> simp [h1]
      _ ≤ 2 := card_le_two
  have key : ∑ v : V, ∑ e ∈ G.cut {v}, x e ≤ 2 * ∑ e, x e := by
    simp only [NicerEars.TJoin.Graph.cut, sum_filter]
    rw [sum_comm, mul_sum]
    apply sum_le_sum
    intro e _
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have := hfil e
    have h2 : (#(univ.filter (fun v : V => ∃ u ∈ ({v} : Finset V), ∃ w ∉ ({v} : Finset V),
        G.ends e = s(u, w))) : ℝ) ≤ 2 := by
      have : #(univ.filter (fun v : V => ∃ u ∈ ({v} : Finset V), ∃ w ∉ ({v} : Finset V),
        G.ends e = s(u, w))) ≤ 2 := by
        simpa [NicerEars.TJoin.Graph.cut] using hfil e
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right h2 (hx0 e)
  have hlow : 2 * (Fintype.card V : ℝ) ≤ ∑ v : V, ∑ e ∈ G.cut {v}, x e := by
    have := sum_le_sum (fun v (_ : v ∈ (univ : Finset V)) => hcut v)
    simpa [mul_comm] using this
  linarith


theorem short_nontrivial {G : NicerEars.TJoin.Graph V E} (P : Ear G) (h : P.IsShort) :
    P.IsNontrivial := by
  unfold Ear.IsNontrivial; unfold Ear.IsShort at h; omega

theorem bad_case (G : NicerEars.TJoin.Graph V E) (hG : G.IsTwoVertexConnected)
    (D : EarDecomposition G) (T : Finset V) (hT : Even #T) (f : Finset V)
    (hf : f ∈ D.eardrumOf T) (hbad : ¬ (PathsThrough G f).Nonempty) :
    T = ∅ ∧ #(D.eardrumOf T) ≤ 1 ∧ 2 ≤ Fintype.card V := by
  obtain ⟨i, hi, rfl⟩ := (mem_eardrumOf D T f).mp hf
  have hclosed : (D.ear i).first = (D.ear i).last := by
    by_contra h
    exact hbad ⟨D.ear i, h, rfl⟩
  have hall : ∀ w, w ∈ (D.ear i).inner ∨ w = (D.ear i).first := by
    intro w
    by_contra h
    push_neg at h
    exact hbad (paths_of_outside G hG _ hi.1 hclosed w h.1 h.2)
  have hroot : D.root = (D.ear i).first := (hall D.root).resolve_left (root_not_mem_inner D i)
  refine ⟨?_, ?_, ?_⟩
  · have hsub : T ⊆ {(D.ear i).first} := fun t ht =>
      mem_singleton.mpr ((hall t).resolve_left (fun h => Finset.disjoint_left.mp hi.2 h ht))
    have := card_le_card hsub
    rw [card_singleton] at this
    rcases hT with ⟨r, hr⟩
    exact card_eq_zero.mp (by omega)
  · have key : ∀ g ∈ D.eardrumOf T, g = (D.ear i).inner := by
      intro g hg
      obtain ⟨j, hj, rfl⟩ := (mem_eardrumOf D T g).mp hg
      by_contra hne
      have hij : j ≠ i := fun h => hne (h ▸ rfl)
      obtain ⟨u, hu⟩ := inner_nonempty G _ (short_nontrivial _ hj.1)
      rcases hall u with h | h
      · exact Finset.disjoint_left.mp (inner_disjoint D j i hij) hu h
      · rw [h, ← hroot] at hu
        exact root_not_mem_inner D j hu
    exact card_le_one.mpr (fun g hg g' hg' => (key g hg).trans (key g' hg').symm)
  · obtain ⟨a, ha⟩ := inner_nonempty G _ (short_nontrivial _ hi.1)
    have hne : a ≠ (D.ear i).first := fun h => first_not_mem_inner G _ (h ▸ ha)
    rw [← card_univ]
    exact one_lt_card.mpr ⟨a, mem_univ _, _, mem_univ _, hne⟩

theorem lmu_le (G : NicerEars.TJoin.Graph V E) (hG : G.IsTwoVertexConnected)
    (D : EarDecomposition G) (hD : D.IsNice) (T : Finset V) (hT : Even #T) (x : E → ℝ)
    (hx : G.LPTFeasible T x) : (Lmu G (D.eardrumOf T) : ℝ) ≤ ∑ e, x e := by
  by_cases hp : ∀ f ∈ D.eardrumOf T, (PathsThrough G f).Nonempty
  · exact (theorem_20 G hG.1.1 T hT _ (eardrumOf_isEardrum D T hD.2.2) (eardrumOf_disjoint D T)
      hp).1 x hx
  · simp only [not_forall] at hp
    obtain ⟨f, hf, hbad⟩ := hp
    obtain ⟨hT0, hM, h2⟩ := bad_case G hG D T hT f hf hbad
    subst hT0
    have hcV : (Fintype.card V : ℝ) ≤ ∑ e, x e := by
      refine card_le_sum G x hx.1 (fun v => hx.2.1 {v} (singleton_nonempty v) ?_ (by simp))
      intro h
      have := congrArg card h
      rw [card_singleton, card_univ] at this
      omega
    have hL : Lmu G (D.eardrumOf (∅ : Finset V)) ≤ (Fintype.card V : ℤ) := by
      unfold Lmu
      have : (#(D.eardrumOf (∅ : Finset V)) : ℤ) ≤ 1 := by exact_mod_cast hM
      have h0 : (0 : ℤ) ≤ (mu G (D.eardrumOf (∅ : Finset V)) : ℤ) := by positivity
      linarith
    have : (Lmu G (D.eardrumOf (∅ : Finset V)) : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast hL
    linarith

theorem num2Ears_le {G : NicerEars.TJoin.Graph V E} (D : EarDecomposition G) (hD : D.IsNice) :
    D.num2Ears ≤ D.numPendant := by
  unfold EarDecomposition.num2Ears EarDecomposition.numPendant
  apply card_le_card
  intro i hi
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  exact hD.2.1 i (Or.inl hi)

end Sol25TwoVCAux

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : NicerEars.TJoin.Graph V E) (hG : G.IsTwoVertexConnected) (T : Finset V)
    (hT : Even #T) :
    ∃ F : Finset (E × Fin 2), G.IsConnectedTJoin T F ∧
      ∀ x : E → ℝ, G.LPTFeasible T x → (#F : ℝ) ≤ 3 / 2 * ∑ e, x e := by
  obtain ⟨D, hnice, hmax⟩ := lemma_23 G hG T hT
  by_cases hcase : (phi G : ℝ) ≤ 2 * (D.numPendant : ℝ)
  · obtain ⟨F, hF, hb⟩ := theorem_24 G T hT D hnice hmax
    refine ⟨F, hF, fun x hx => ?_⟩
    have hL := Sol25TwoVCAux.lmu_le G hG D hnice T hT x hx
    have h3 := (proposition_3 G hG.1.1 T hT).2 x hx
    have hphi : ((Lphi G : ℤ) : ℝ) = (Fintype.card V : ℝ) + (phi G : ℝ) - 1 := by
      simp [Lphi]
    rw [hphi] at hb
    linarith
  · obtain ⟨F, hF, hb⟩ := proposition_8 G hG.1 D hnice.1 T hT
    refine ⟨F, hF, fun x hx => ?_⟩
    have h3 := (proposition_3 G hG.1.1 T hT).2 x hx
    have h2p : (D.num2Ears : ℝ) ≤ D.numPendant := by
      exact_mod_cast Sol25TwoVCAux.num2Ears_le D hnice
    push_neg at hcase
    linarith
