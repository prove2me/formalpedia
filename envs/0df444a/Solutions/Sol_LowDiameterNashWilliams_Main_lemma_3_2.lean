-- Prove2me | solution 1 for LowDiameterNashWilliams.Main.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:07:39.631528+00:00
-- url     : https://prove2.me/submissions/84e35905-90d3-4691-b44a-f74cc00a866d

import Mathlib
import Definitions.Def_NashWilliams61_TreePacking_Graphs
import Definitions.Def_LowDiameterNashWilliams_Main_Geometry

section
set_option autoImplicit false
open Classical
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn
namespace LowDiameterNashWilliams.Dev.Forest

theorem edgeGraph_mono {V E : Type*} [DecidableEq E] (ends : E → Sym2 V) {F F' : Finset E} (h : F ⊆ F') :
    edgeGraph ends F ≤ edgeGraph ends F' := by
  unfold edgeGraph
  apply SimpleGraph.fromEdgeSet_mono
  exact Set.image_mono (by exact_mod_cast h)

theorem isForest_mono {V E : Type*} [DecidableEq E] (ends : E → Sym2 V) {F F' : Finset E} (h : F ⊆ F')
    (hF : IsForest ends F') : IsForest ends F := by
  intro e he u v huv hr
  exact hF e (h he) u v huv
    (hr.mono (edgeGraph_mono ends (Finset.erase_subset_erase e h)))

theorem forest_nondiag {V E : Type*} [DecidableEq E] (ends : E → Sym2 V) {F : Finset E}
    (hF : IsForest ends F) : ∀ e ∈ F, ¬ (ends e).IsDiag := by
  intro e he hd
  obtain ⟨u, v, huv⟩ : ∃ u v, ends e = s(u, v) := by
    induction h' : ends e using Sym2.ind with
    | _ u v => exact ⟨u, v, rfl⟩
  rw [huv, Sym2.mk_isDiag_iff] at hd
  subst hd
  exact hF e he u u huv (SimpleGraph.Reachable.refl _)

theorem forest_inj {V E : Type*} [DecidableEq E] (ends : E → Sym2 V) {F : Finset E}
    (hF : IsForest ends F) : Set.InjOn ends (F : Set E) := by
  intro e he e' he' h
  by_contra hne
  have hnd := forest_nondiag ends hF e he
  obtain ⟨u, v, huv⟩ : ∃ u v, ends e = s(u, v) := by
    induction h' : ends e using Sym2.ind with
    | _ u v => exact ⟨u, v, rfl⟩
  apply hF e he u v huv
  have hne' : u ≠ v := by
    intro h2; apply hnd; rw [huv, h2]; simp
  apply SimpleGraph.Adj.reachable
  unfold edgeGraph
  rw [SimpleGraph.fromEdgeSet_adj]
  refine ⟨⟨e', ?_, ?_⟩, hne'⟩
  · simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
    exact ⟨he', fun h3 => hne h3.symm⟩
  · rw [← h, huv]

theorem acyc_card {V : Type*} [Fintype V] [Nonempty V] (H : SimpleGraph V) [Fintype H.edgeSet] (hH : H.IsAcyclic) :
    H.edgeFinset.card + 1 ≤ Fintype.card V := by
  obtain ⟨F, hle, -, hT⟩ := (SimpleGraph.connected_top (V := V)).exists_isTree_le_of_le_of_isAcyclic
    (le_top : H ≤ ⊤) hH
  have := hT.card_edgeFinset
  have : H.edgeFinset.card ≤ F.edgeFinset.card := by
    apply Finset.card_le_card
    intro x hx
    simp only [SimpleGraph.mem_edgeFinset] at hx ⊢
    exact SimpleGraph.edgeSet_mono ‹H ≤ F› hx
  omega

theorem inner_card_lt {n m : ℕ} (ends : Fin m → Sym2 (Fin n)) (T : Finset (Fin m))
    (hT : IsSpanningTree ends T) (A : Finset (Fin n)) (hA : A.Nonempty) :
    (T.filter fun e => ∀ v ∈ ends e, v ∈ A).card < A.card := by
  set F := T.filter fun e => ∀ v ∈ ends e, v ∈ A with hFdef
  have hTf : IsForest ends T := hT.2.2.2.1
  have hF : IsForest ends F := isForest_mono ends (Finset.filter_subset _ _) hTf
  have hnd := forest_nondiag ends hF
  have hinj := forest_inj ends hF
  set G := edgeGraph ends F with hG
  have hGe : G.edgeSet = ends '' (F : Set (Fin m)) := by
    rw [hG, edgeGraph, SimpleGraph.edgeSet_fromEdgeSet]
    ext x
    simp only [Set.mem_sdiff, Set.mem_image, Finset.mem_coe]
    constructor
    · exact fun h => h.1
    · rintro ⟨e, he, rfl⟩; exact ⟨⟨e, he, rfl⟩, hnd e he⟩
  have hcard : G.edgeFinset.card = F.card := by
    have : G.edgeFinset = F.image ends := by
      ext x
      rw [SimpleGraph.mem_edgeFinset, hGe]; simp
    rw [this, Finset.card_image_of_injOn hinj]
  have hac : G.IsAcyclic := by
    rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
    intro v w hvw
    have hvw' := hvw
    rw [hG, edgeGraph, SimpleGraph.fromEdgeSet_adj] at hvw'
    obtain ⟨⟨e', he', hee'⟩, hne⟩ := hvw'
    rw [SimpleGraph.isBridge_iff]
    intro hr
    apply hF e' he' v w hee'
    refine hr.mono ?_
    intro a b hab
    rw [SimpleGraph.deleteEdges_adj] at hab
    obtain ⟨hab1, hab2⟩ := hab
    have hab1' := hab1
    rw [hG, edgeGraph, SimpleGraph.fromEdgeSet_adj] at hab1'
    obtain ⟨⟨f, hf, hfab⟩, hne2⟩ := hab1'
    unfold edgeGraph
    rw [SimpleGraph.fromEdgeSet_adj]
    refine ⟨⟨f, ?_, hfab⟩, hne2⟩
    simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
    refine ⟨hf, fun hfe => hab2 ?_⟩
    rw [← hfab, hfe, hee']
    rfl
  have hsupp : G.support ⊆ (A : Set (Fin n)) := by
    rintro v ⟨w, hvw⟩
    have hvw : G.Adj v w := hvw
    rw [hG, edgeGraph, SimpleGraph.fromEdgeSet_adj] at hvw
    obtain ⟨⟨f, hf, hfe⟩, -⟩ := hvw
    have hfF := Finset.mem_coe.mp hf
    rw [hFdef, Finset.mem_filter] at hfF
    exact hfF.2 v (by rw [hfe]; simp)
  have hind := SimpleGraph.card_edgeFinset_induce_of_support_subset hsupp
  have hac2 := hac.induce (A : Set (Fin n))
  have : Nonempty (A : Set (Fin n)) := hA.coe_sort
  have := acyc_card _ hac2
  have hc : Fintype.card (A : Set (Fin n)) = A.card := Fintype.card_coe A
  rw [← hcard]
  rw [hc] at this
  have h5 : G.edgeFinset.card + 1 ≤ A.card := by
    convert this using 2
    convert hind.symm
  omega

end LowDiameterNashWilliams.Dev.Forest
end

section
set_option autoImplicit false
open scoped BigOperators
namespace LowDiameterNashWilliams.Dev.Laminar

lemma exists_maxl {α : Type*} [DecidableEq α] (G : Finset (Finset α)) :
    ∀ Y ∈ G, ∃ X ∈ G.filter (fun X => ∀ Z ∈ G, ¬ X ⊂ Z), Y ⊆ X := by
  intro Y hY
  obtain ⟨X, hX, hmax⟩ := Finset.exists_max_image (G.filter (fun X => Y ⊆ X)) Finset.card
    ⟨Y, by simp [hY]⟩
  simp only [Finset.mem_filter] at hX hmax
  refine ⟨X, ?_, hX.2⟩
  rw [Finset.mem_filter]
  refine ⟨hX.1, fun Z hZ hXZ => ?_⟩
  have := hmax Z ⟨hZ, hX.2.trans hXZ.subset⟩
  exact absurd (Finset.card_lt_card hXZ) (not_lt.2 this)

lemma disj_maxl {α : Type*} [DecidableEq α] (G : Finset (Finset α))
    (hl : ∀ X ∈ G, ∀ Y ∈ G, X ⊆ Y ∨ Y ⊆ X ∨ Disjoint X Y) :
    ∀ X ∈ G.filter (fun X => ∀ Z ∈ G, ¬ X ⊂ Z), ∀ Y ∈ G.filter (fun X => ∀ Z ∈ G, ¬ X ⊂ Z),
      X ≠ Y → Disjoint X Y := by
  intro X hX Y hY hne
  rw [Finset.mem_filter] at hX hY
  rcases hl X hX.1 Y hY.1 with h | h | h
  · exact absurd (Finset.ssubset_iff_subset_ne.2 ⟨h, hne⟩) (hX.2 Y hY.1)
  · exact absurd (Finset.ssubset_iff_subset_ne.2 ⟨h, hne.symm⟩) (hY.2 X hX.1)
  · exact h

lemma sum_card_le' {α : Type*} [DecidableEq α] (N : Finset (Finset α)) (M : Finset α)
    (hsub : ∀ X ∈ N, X ⊆ M) (hd : ∀ X ∈ N, ∀ Y ∈ N, X ≠ Y → Disjoint X Y) :
    ∑ X ∈ N, X.card ≤ M.card := by
  have h := Finset.card_biUnion (s := N) (t := id) hd
  simp only [id] at h
  rw [← h]
  exact Finset.card_le_card (Finset.biUnion_subset.2 hsub)

lemma claimC {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (b : ℝ) (hb : 0 < b)
    (hlam : ∀ X ∈ F, ∀ Y ∈ F, X ⊆ Y ∨ Y ⊆ X ∨ Disjoint X Y)
    (hsize : ∀ X ∈ F, b ≤ (X.card : ℝ))
    (hgap : ∀ X ∈ F, ∀ Y ∈ F, X ⊂ Y → (X.card : ℝ) + b ≤ Y.card) :
    ∀ n : ℕ, ∀ M ∈ F, M.card = n →
      ((F.filter (· ⊆ M)).card : ℝ) ≤ 2 * (M.card : ℝ) / b - 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M hM hn
  set G := (F.filter (· ⊆ M)).erase M with hG
  have hMmem : M ∈ F.filter (· ⊆ M) := by simp [hM]
  have hGmem : ∀ X ∈ G, X ∈ F ∧ X ⊆ M ∧ X ≠ M := by
    intro X hX
    rw [hG, Finset.mem_erase, Finset.mem_filter] at hX
    exact ⟨hX.2.1, hX.2.2, hX.1⟩
  set N := G.filter (fun X => ∀ Z ∈ G, ¬ X ⊂ Z) with hN
  have hNG : ∀ X ∈ N, X ∈ G := fun X hX => (Finset.mem_filter.1 hX).1
  have hcover : G ⊆ N.biUnion (fun X => F.filter (· ⊆ X)) := by
    intro Y hY
    obtain ⟨X, hX, hYX⟩ := exists_maxl G Y hY
    rw [Finset.mem_biUnion]
    exact ⟨X, hX, by rw [Finset.mem_filter]; exact ⟨(hGmem Y hY).1, hYX⟩⟩
  have hdisj := disj_maxl G (fun X hX Y hY => hlam X (hGmem X hX).1 Y (hGmem Y hY).1)
  have hSsum := sum_card_le' N M (fun X hX => (hGmem X (hNG X hX)).2.1) hdisj
  have hcardF : ((F.filter (· ⊆ M)).card : ℝ) = G.card + 1 := by
    have := Finset.card_erase_add_one hMmem
    rw [← hG] at this
    rw [← this]; push_cast; ring
  have hGle : (G.card : ℝ) ≤ ∑ X ∈ N, ((F.filter (· ⊆ X)).card : ℝ) := by
    have := (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    exact_mod_cast this
  have hsumle : ∑ X ∈ N, ((F.filter (· ⊆ X)).card : ℝ)
      ≤ ∑ X ∈ N, (2 * (X.card : ℝ) / b - 1) := by
    apply Finset.sum_le_sum
    intro X hX
    have h1 := hGmem X (hNG X hX)
    have hlt : X.card < n := by
      rw [← hn]
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨h1.2.1, h1.2.2⟩)
    exact ih X.card hlt X h1.1 rfl
  have hsplit : ∑ X ∈ N, (2 * (X.card : ℝ) / b - 1)
      = 2 * (∑ X ∈ N, (X.card : ℝ)) / b - N.card := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum]
    simp
  have hSreal : (∑ X ∈ N, (X.card : ℝ)) ≤ M.card := by exact_mod_cast hSsum
  have hMb := hsize M hM
  have h2 : 2 ≤ 2 * (M.card : ℝ) / b := by
    rw [le_div_iff₀ hb]; linarith
  have hMdiv : 2 * (∑ X ∈ N, (X.card : ℝ)) / b ≤ 2 * (M.card : ℝ) / b :=
    div_le_div_of_nonneg_right (by linarith) hb.le
  rw [hcardF]
  rcases Nat.lt_or_ge N.card 2 with hs | hs
  · interval_cases hc : N.card
    · have : N = ∅ := Finset.card_eq_zero.1 hc
      rw [this] at hGle
      simp only [Finset.sum_empty] at hGle
      linarith
    · obtain ⟨X, hX⟩ := Finset.card_eq_one.1 hc
      have h1 := hGmem X (hNG X (by rw [hX]; simp))
      have hg := hgap X h1.1 M hM (Finset.ssubset_iff_subset_ne.2 ⟨h1.2.1, h1.2.2⟩)
      rw [hX] at hsplit hGle hsumle
      simp only [Finset.sum_singleton] at hsplit hGle hsumle
      have : 2 * (X.card : ℝ) / b ≤ 2 * (M.card : ℝ) / b - 2 := by
        have : 2 * (X.card : ℝ) / b + 2 = 2 * ((X.card : ℝ) + b) / b := by
          field_simp
        have h3 : 2 * ((X.card : ℝ) + b) / b ≤ 2 * (M.card : ℝ) / b :=
          div_le_div_of_nonneg_right (by linarith) hb.le
        linarith
      push_cast at hsplit
      linarith
  · have : (2 : ℝ) ≤ N.card := by exact_mod_cast hs
    linarith

theorem laminar_card_le {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (U : Finset α) (b : ℝ) (hb : 0 < b)
    (hU : ∀ X ∈ F, X ⊆ U)
    (hlam : ∀ X ∈ F, ∀ Y ∈ F, X ⊆ Y ∨ Y ⊆ X ∨ Disjoint X Y)
    (hsize : ∀ X ∈ F, b ≤ (X.card : ℝ))
    (hgap : ∀ X ∈ F, ∀ Y ∈ F, X ⊂ Y → (X.card : ℝ) + b ≤ Y.card) :
    (F.card : ℝ) ≤ 2 * (U.card : ℝ) / b := by
  set T := F.filter (fun X => ∀ Z ∈ F, ¬ X ⊂ Z) with hT
  have hTF : ∀ X ∈ T, X ∈ F := fun X hX => (Finset.mem_filter.1 hX).1
  have hcover : F ⊆ T.biUnion (fun X => F.filter (· ⊆ X)) := by
    intro Y hY
    obtain ⟨X, hX, hYX⟩ := exists_maxl F Y hY
    rw [Finset.mem_biUnion]
    exact ⟨X, hX, by rw [Finset.mem_filter]; exact ⟨hY, hYX⟩⟩
  have hdisj := disj_maxl F hlam
  have hSsum := sum_card_le' T U (fun X hX => hU X (hTF X hX)) hdisj
  have hSreal : (∑ X ∈ T, (X.card : ℝ)) ≤ U.card := by exact_mod_cast hSsum
  have hle : (F.card : ℝ) ≤ ∑ X ∈ T, ((F.filter (· ⊆ X)).card : ℝ) := by
    have := (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    exact_mod_cast this
  have hsumle : ∑ X ∈ T, ((F.filter (· ⊆ X)).card : ℝ)
      ≤ ∑ X ∈ T, (2 * (X.card : ℝ) / b) := by
    apply Finset.sum_le_sum
    intro X hX
    have := claimC F b hb hlam hsize hgap X.card X (hTF X hX) rfl
    linarith
  have hsplit : ∑ X ∈ T, (2 * (X.card : ℝ) / b) = 2 * (∑ X ∈ T, (X.card : ℝ)) / b := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
  have : 2 * (∑ X ∈ T, (X.card : ℝ)) / b ≤ 2 * (U.card : ℝ) / b :=
    div_le_div_of_nonneg_right (by linarith) hb.le
  linarith

end LowDiameterNashWilliams.Dev.Laminar
end

section
set_option autoImplicit false
open scoped BigOperators
open Classical
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Dev.L32
open LowDiameterNashWilliams.Main

variable {n m k : ℕ}

structure Hyp {n m k : ℕ} (ends : Fin m → Sym2 (Fin n)) (T : Trees k m)
    (D : Fin k → Direction n m) (r : Fin n) : Prop where
  simple : Simple ends
  part : TreePartition ends T
  toward : ∀ i, Toward ends (T i) (D i) r

theorem sum_fiber (F : Finset (Fin m)) (f : Fin m → Fin n) (A : Finset (Fin n)) (P : Fin m → Prop) :
    ∑ v ∈ A, (F.filter fun e => f e = v ∧ P e).card
      = (F.filter fun e => f e ∈ A ∧ P e).card := by
  have := Finset.card_eq_sum_card_fiberwise (s := F.filter fun e => f e ∈ A ∧ P e) (f := f)
    (t := A) (fun e he => (Finset.mem_filter.mp he).2.1)
  rw [this]
  apply Finset.sum_congr rfl
  intro v hv
  congr 1
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, hf, hP⟩
    exact ⟨⟨he, hf ▸ hv, hP⟩, hf⟩
  · rintro ⟨⟨he, _, hP⟩, hf⟩
    exact ⟨he, hf, hP⟩

theorem inner_iff {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) (i : Fin k) {e : Fin m} (he : e ∈ T i) (A : Finset (Fin n)) :
    (∀ v ∈ ends e, v ∈ A) ↔ ((D i e).1 ∈ A ∧ (D i e).2 ∈ A) := by
  have := (h.toward i).1 e he
  rw [this]
  simp [Sym2.mem_iff]

theorem tail_card {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) (i : Fin k) (A : Finset (Fin n)) :
    ((T i).filter fun e => (D i e).1 ∈ A).card + (if r ∈ A then 1 else 0) = A.card := by
  have h1 := sum_fiber (T i) (fun e => (D i e).1) A (fun _ => True)
  simp only [and_true] at h1
  rw [← h1]
  have h2 : ∀ v ∈ A, ((T i).filter fun e => (D i e).1 = v).card = if v = r then 0 else 1 := by
    intro v _
    by_cases hv : v = r
    · subst hv; rw [if_pos rfl]; exact (h.toward i).2.1
    · rw [if_neg hv]; exact (h.toward i).2.2 v hv
  rw [Finset.sum_congr rfl h2]
  rw [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, smul_eq_mul, mul_one, zero_add]
  have : (A.filter fun v => ¬ v = r) = A.erase r := by
    ext v; simp [Finset.mem_erase, and_comm]
  rw [this]
  by_cases hr : r ∈ A
  · rw [Finset.card_erase_of_mem hr, if_pos hr]
    have := Finset.card_pos.mpr ⟨r, hr⟩
    omega
  · rw [Finset.erase_eq_of_notMem hr, if_neg hr]; rfl

/-- inner edges of tree `i` -/
def inner (ends : Fin m → Sym2 (Fin n)) (T : Trees k m) (i : Fin k) (A : Finset (Fin n)) : ℕ :=
  ((T i).filter fun e => ∀ v ∈ ends e, v ∈ A).card

def leave (D : Fin k → Direction n m) (T : Trees k m) (i : Fin k) (A : Finset (Fin n)) : ℕ :=
  ((T i).filter fun e => (D i e).1 ∈ A ∧ (D i e).2 ∉ A).card

theorem tree_identity {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) (i : Fin k) (A : Finset (Fin n)) :
    inner ends T i A + leave D T i A + (if r ∈ A then 1 else 0) = A.card := by
  have h1 := tail_card h i A
  have h2 : inner ends T i A + leave D T i A = ((T i).filter fun e => (D i e).1 ∈ A).card := by
    unfold inner leave
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext e
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨he, hin⟩ | ⟨he, ht, _⟩)
        · exact ⟨he, ((inner_iff h i he A).mp hin).1⟩
        · exact ⟨he, ht⟩
      · rintro ⟨he, ht⟩
        by_cases hh : (D i e).2 ∈ A
        · exact Or.inl ⟨he, (inner_iff h i he A).mpr ⟨ht, hh⟩⟩
        · exact Or.inr ⟨he, ht, hh⟩
    · rw [Finset.disjoint_left]
      intro e he he'
      simp only [Finset.mem_filter] at he he'
      exact he'.2.2 ((inner_iff h i he'.1 A).mp he.2).2
  omega

theorem inner_lt {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) (i : Fin k) (A : Finset (Fin n)) (hA : A.Nonempty) :
    inner ends T i A < A.card :=
  LowDiameterNashWilliams.Dev.Forest.inner_card_lt ends (T i) (h.part.1.1 i) A hA

theorem cover {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) (e : Fin m) : ∃ i, e ∈ T i := by
  have : e ∈ Finset.univ.biUnion T := by rw [h.part.2]; exact Finset.mem_univ e
  simpa using this

theorem edgeCount_eq {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) (A : Finset (Fin n)) :
    (edgesIn ends A).card = ∑ i, inner ends T i A := by
  have : edgesIn ends A = Finset.univ.biUnion fun i => (T i).filter fun e => ∀ v ∈ ends e, v ∈ A := by
    ext e
    simp only [edgesIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro he
      obtain ⟨i, hi⟩ := cover h e
      exact ⟨i, hi, he⟩
    · rintro ⟨i, _, he⟩
      exact he
  rw [this, Finset.card_biUnion]
  · rfl
  · intro i _ j _ hij
    exact Finset.disjoint_filter_filter (h.part.1.2 i j hij)

/-- the total outgoing arcs leaving `A` -/
noncomputable def sumOut (T : Trees k m) (D : Fin k → Direction n m) (A : Finset (Fin n)) : ℕ :=
  ∑ v ∈ A, outgoingTo T D v (Finset.univ \ A)

theorem sumOut_eq {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (A : Finset (Fin n)) :
    sumOut T D A = ∑ i, leave D T i A := by
  unfold sumOut outgoingTo leave
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have := sum_fiber (T i) (fun e => (D i e).1) A (fun e => (D i e).2 ∈ Finset.univ \ A)
  convert this using 4
  all_goals simp

theorem identity {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) (A : Finset (Fin n)) :
    (edgesIn ends A).card + sumOut T D A + k * (if r ∈ A then 1 else 0) = k * A.card := by
  rw [edgeCount_eq h, sumOut_eq (ends := ends) (r := r)]
  have : ∀ i, inner ends T i A + leave D T i A + (if r ∈ A then 1 else 0) = A.card :=
    fun i => tree_identity h i A
  have h2 := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin k)) = Finset.univ)
    (fun i _ => this i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  omega

theorem edgeCount_add_le {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) (A : Finset (Fin n)) (hA : A.Nonempty) :
    (edgesIn ends A).card + k ≤ k * A.card := by
  rw [edgeCount_eq h]
  have : ∀ i ∈ (Finset.univ : Finset (Fin k)), inner ends T i A + 1 ≤ A.card :=
    fun i _ => inner_lt h i A hA
  have h2 := Finset.sum_le_sum this
  rw [Finset.sum_add_distrib] at h2
  simpa using h2

theorem tight_iff (ends : Fin m → Sym2 (Fin n)) (A : Finset (Fin n)) :
    tight ends k A ↔ A.Nonempty ∧ (edgesIn ends A).card + k = k * A.card := by
  unfold tight
  constructor
  · rintro ⟨hA, he⟩
    refine ⟨hA, ?_⟩
    have hc := Finset.card_pos.mpr hA
    have : (((edgesIn ends A).card + k : ℕ) : ℤ) = ((k * A.card : ℕ) : ℤ) := by
      push_cast; rw [he]; ring
    exact_mod_cast this
  · rintro ⟨hA, he⟩
    refine ⟨hA, ?_⟩
    have : (((edgesIn ends A).card + k : ℕ) : ℤ) = ((k * A.card : ℕ) : ℤ) := by rw [he]
    push_cast at this
    linarith

theorem sumOut_tight {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) {A : Finset (Fin n)} (hA : tight ends k A) :
    sumOut T D A + k * (if r ∈ A then 1 else 0) = k := by
  have h1 := identity h A
  have h2 := ((tight_iff ends A).mp hA).2
  omega

end LowDiameterNashWilliams.Dev.L32
end

section
set_option autoImplicit false
open scoped BigOperators
open Classical
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Dev.L32
open LowDiameterNashWilliams.Main

variable {n m k : ℕ}

def cross (ends : Fin m → Sym2 (Fin n)) (A B : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter fun e => ∃ a ∈ A \ B, ∃ b ∈ B \ A, ends e = s(a, b)

theorem edgesIn_inter (ends : Fin m → Sym2 (Fin n)) (A B : Finset (Fin n)) :
    edgesIn ends (A ∩ B) = edgesIn ends A ∩ edgesIn ends B := by
  ext e
  simp only [edgesIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
  constructor
  · intro h
    exact ⟨fun v hv => (h v hv).1, fun v hv => (h v hv).2⟩
  · rintro ⟨h1, h2⟩ v hv
    exact ⟨h1 v hv, h2 v hv⟩

theorem union_card (ends : Fin m → Sym2 (Fin n)) (A B : Finset (Fin n)) :
    (edgesIn ends A).card + (edgesIn ends B).card + (cross ends A B).card
      ≤ (edgesIn ends (A ∪ B)).card + (edgesIn ends (A ∩ B)).card := by
  have h1 : (edgesIn ends A ∪ edgesIn ends B) ∪ cross ends A B ⊆ edgesIn ends (A ∪ B) := by
    intro e he
    simp only [Finset.mem_union] at he
    simp only [edgesIn, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases he with (he | he) | he
    · intro v hv
      have := (by simpa [edgesIn] using he : ∀ v ∈ ends e, v ∈ A) v hv
      exact Finset.mem_union_left _ this
    · intro v hv
      have := (by simpa [edgesIn] using he : ∀ v ∈ ends e, v ∈ B) v hv
      exact Finset.mem_union_right _ this
    · simp only [cross, Finset.mem_filter, Finset.mem_univ, true_and] at he
      obtain ⟨a, ha, b, hb, hab⟩ := he
      intro v hv
      rw [hab, Sym2.mem_iff] at hv
      rcases hv with rfl | rfl
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp ha).1
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hb).1
  have h2 : Disjoint (edgesIn ends A ∪ edgesIn ends B) (cross ends A B) := by
    rw [Finset.disjoint_left]
    intro e he hc
    simp only [cross, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨a, ha, b, hb, hab⟩ := hc
    have hbm : b ∈ ends e := by rw [hab]; simp
    have ham : a ∈ ends e := by rw [hab]; simp
    rcases Finset.mem_union.mp he with he | he
    · have : ∀ v ∈ ends e, v ∈ A := by simpa [edgesIn] using he
      exact (Finset.mem_sdiff.mp hb).2 (this b hbm)
    · have : ∀ v ∈ ends e, v ∈ B := by simpa [edgesIn] using he
      exact (Finset.mem_sdiff.mp ha).2 (this a ham)
  have h3 := Finset.card_le_card h1
  rw [Finset.card_union_of_disjoint h2] at h3
  have h4 := Finset.card_union_add_card_inter (edgesIn ends A) (edgesIn ends B)
  rw [← edgesIn_inter] at h4
  omega

theorem tight_union_inter {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) {A B : Finset (Fin n)} (hA : tight ends k A) (hB : tight ends k B)
    (hAB : (A ∩ B).Nonempty) :
    tight ends k (A ∪ B) ∧ tight ends k (A ∩ B) ∧ cross ends A B = ∅ := by
  have hA' := ((tight_iff ends A).mp hA).2
  have hB' := ((tight_iff ends B).mp hB).2
  have hU : (A ∪ B).Nonempty := hAB.mono (fun x hx => Finset.mem_union_left _ (Finset.mem_inter.mp hx).1)
  have h1 := edgeCount_add_le h (A ∪ B) hU
  have h2 := edgeCount_add_le h (A ∩ B) hAB
  have h3 := union_card ends A B
  have h4 : (A ∪ B).card + (A ∩ B).card = A.card + B.card := Finset.card_union_add_card_inter A B
  have h5 : k * (A ∪ B).card + k * (A ∩ B).card = k * A.card + k * B.card := by
    rw [← mul_add, ← mul_add, h4]
  have hc : (cross ends A B).card = 0 := by omega
  refine ⟨(tight_iff ends _).mpr ⟨hU, by omega⟩, (tight_iff ends _).mpr ⟨hAB, by omega⟩, ?_⟩
  exact Finset.card_eq_zero.mp hc

theorem outgoingTo_mono {T : Trees k m} {D : Fin k → Direction n m} (v : Fin n)
    {S S' : Finset (Fin n)} (hS : S ⊆ S') : outgoingTo T D v S ≤ outgoingTo T D v S' := by
  unfold outgoingTo
  apply Finset.sum_le_sum
  intro i _
  apply Finset.card_le_card
  intro e he
  simp only [Finset.mem_filter] at he ⊢
  exact ⟨he.1, he.2.1, hS he.2.2⟩

theorem outgoingTo_union {T : Trees k m} {D : Fin k → Direction n m} (v : Fin n)
    {S S' : Finset (Fin n)} (hS : Disjoint S S') :
    outgoingTo T D v (S ∪ S') = outgoingTo T D v S + outgoingTo T D v S' := by
  unfold outgoingTo
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  · rw [Finset.disjoint_left]
    intro e he he'
    simp only [Finset.mem_filter] at he he'
    exact Finset.disjoint_left.mp hS he.2.2 he'.2.2

theorem outgoingTo_le_card {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) (v : Fin n) (S : Finset (Fin n)) :
    outgoingTo T D v S ≤ S.card := by
  unfold outgoingTo
  rw [← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn (fun x => (D x.1 x.2).2)
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter] at hx
    exact hx.2.2.2
  · rintro ⟨i, e⟩ hx ⟨i', e'⟩ hx' hxx
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ,
      true_and] at hx hx'
    have h1 := (h.toward i).1 e hx.1
    have h2 := (h.toward i').1 e' hx'.1
    have hxx' : (D i e).2 = (D i' e').2 := hxx
    rw [hx.2.1, hxx'] at h1
    rw [hx'.2.1] at h2
    have he : e = e' := h.simple.1 (h1.trans h2.symm)
    subst he
    by_cases hi : i = i'
    · subst hi; rfl
    · exact absurd (Finset.disjoint_left.mp (h.part.1.2 i i' hi) hx.1) (not_not.mpr hx'.1)

theorem edgeCount_le_choose {ends : Fin m → Sym2 (Fin n)} (hs : Simple ends) (A : Finset (Fin n)) :
    2 * (edgesIn ends A).card ≤ A.card * (A.card - 1) := by
  have himg : ((edgesIn ends A).image ends).card = (edgesIn ends A).card :=
    Finset.card_image_of_injOn (fun x _ y _ hxy => hs.1 hxy)
  have hdiag : (A.image Sym2.diag).card = A.card :=
    Finset.card_image_of_injective _ Sym2.diag_injective
  have hdisj : Disjoint ((edgesIn ends A).image ends) (A.image Sym2.diag) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hz'
    exact hs.2 e (by rw [← ha]; exact Sym2.diag_isDiag a)
  have hsub : (edgesIn ends A).image ends ∪ A.image Sym2.diag ⊆ A.sym2 := by
    intro z hz
    rw [Finset.mem_sym2_iff]
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
      simpa [edgesIn] using he
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      intro x hx
      simp only [Sym2.diag, Sym2.mem_iff] at hx
      rcases hx with rfl | rfl <;> exact ha
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, himg, hdiag, Finset.card_sym2] at hc
  have h2 : 2 * (A.card + 1).choose 2 = (A.card + 1) * A.card := by
    rw [Nat.choose_two_right]
    apply Nat.mul_div_cancel'
    have := Nat.even_mul_succ_self A.card
    rw [mul_comm] at this
    exact even_iff_two_dvd.mp this
  rcases Nat.eq_zero_or_pos A.card with h0 | hpos
  · have h0' : (edgesIn ends A).card = 0 := by
      have := hc
      rw [h0] at this
      simpa using this
    rw [h0, h0']
  · have : A.card * (A.card - 1) + 2 * A.card = (A.card + 1) * A.card := by
      obtain ⟨c, hc'⟩ : ∃ c, A.card = c + 1 := ⟨A.card - 1, by omega⟩
      rw [hc']; simp; ring
    omega

theorem two_k_le {ends : Fin m → Sym2 (Fin n)} (hs : Simple ends) {A : Finset (Fin n)}
    (hA : tight ends k A) (h2 : 2 ≤ A.card) : 2 * k ≤ A.card := by
  have h1 := edgeCount_le_choose hs A
  have h3 := ((tight_iff ends A).mp hA).2
  have h4 : (edgesIn ends A).card = k * (A.card - 1) := by
    obtain ⟨c, hc⟩ : ∃ c, A.card = c + 1 := ⟨A.card - 1, by omega⟩
    rw [hc] at h3 ⊢
    simp only [Nat.add_sub_cancel]
    rw [mul_add] at h3
    omega
  rw [h4] at h1
  have : 2 * k * (A.card - 1) ≤ A.card * (A.card - 1) := by nlinarith
  exact Nat.le_of_mul_le_mul_right this (by omega)

end LowDiameterNashWilliams.Dev.L32
end

section
set_option autoImplicit false
open scoped BigOperators
open Classical
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Dev.L32
open LowDiameterNashWilliams.Main

variable {n m k : ℕ}

def Wit (ends : Fin m → Sym2 (Fin n)) (T : Trees k m) (D : Fin k → Direction n m)
    (v : Fin n) (A : Finset (Fin n)) : Prop :=
  v ∈ A ∧ 2 ≤ A.card ∧ tight ends k A ∧ (3 : ℝ) * k / 4 ≤ outgoingTo T D v (Finset.univ \ A)

theorem out_le_sumOut {T : Trees k m} {D : Fin k → Direction n m} {v : Fin n} {A : Finset (Fin n)}
    (hv : v ∈ A) : outgoingTo T D v (Finset.univ \ A) ≤ sumOut T D A :=
  Finset.single_le_sum (f := fun u => outgoingTo T D u (Finset.univ \ A))
    (fun _ _ => Nat.zero_le _) hv

theorem out_pair_le {T : Trees k m} {D : Fin k → Direction n m} {v w : Fin n}
    {A : Finset (Fin n)} (hv : v ∈ A) (hw : w ∈ A) (hvw : v ≠ w) :
    outgoingTo T D v (Finset.univ \ A) + outgoingTo T D w (Finset.univ \ A) ≤ sumOut T D A := by
  have : ∑ u ∈ ({v, w} : Finset (Fin n)), outgoingTo T D u (Finset.univ \ A) ≤ sumOut T D A :=
    Finset.sum_le_sum_of_subset (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption)
  rwa [Finset.sum_pair hvw] at this

theorem r_not_mem {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) (hk : 1 ≤ k) {v : Fin n} {A : Finset (Fin n)}
    (hw : Wit ends T D v A) : r ∉ A := by
  intro hr
  have h1 := sumOut_tight h hw.2.2.1
  rw [if_pos hr] at h1
  have h3 := out_le_sumOut (T := T) (D := D) hw.1
  have h5 : outgoingTo T D v (Finset.univ \ A) = 0 := by omega
  have h4 := hw.2.2.2
  rw [h5] at h4
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  push_cast at h4
  linarith

theorem sumOut_of_not_mem {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) {A : Finset (Fin n)} (hA : tight ends k A) (hr : r ∉ A) :
    sumOut T D A = k := by
  have h1 := sumOut_tight h hA
  rw [if_neg hr] at h1
  omega

theorem wit_distinct {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) (hk : 1 ≤ k) {v w : Fin n} {A : Finset (Fin n)}
    (hv : Wit ends T D v A) (hw : Wit ends T D w A) (hvw : v ≠ w) : False := by
  have h1 := out_pair_le (T := T) (D := D) hv.1 hw.1 hvw
  have h2 := sumOut_of_not_mem h hv.2.2.1 (r_not_mem h hk hv)
  rw [h2] at h1
  have h3 := hv.2.2.2
  have h4 := hw.2.2.2
  have h5 : ((outgoingTo T D v (Finset.univ \ A) + outgoingTo T D w (Finset.univ \ A) : ℕ) : ℝ)
      ≤ k := by exact_mod_cast h1
  push_cast at h5
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

theorem min_incl {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {v : Fin n} {A : Finset (Fin n)} (hw : Wit ends T D v A)
    (hmin : ∀ A', Wit ends T D v A' → A.card ≤ A'.card) {A' : Finset (Fin n)}
    (hv : v ∈ A') (h2 : 2 ≤ A'.card) (ht : tight ends k A') (hsub : A' ⊆ A) : A' = A := by
  have hw' : Wit ends T D v A' := by
    refine ⟨hv, h2, ht, le_trans hw.2.2.2 ?_⟩
    exact_mod_cast outgoingTo_mono v (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hsub)
  exact Finset.eq_of_subset_of_card_le hsub (hmin A' hw')

theorem no_edge_zero {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) {v : Fin n} {S : Finset (Fin n)}
    (hno : ∀ e, ∀ b ∈ S, ends e ≠ s(v, b)) : outgoingTo T D v S = 0 := by
  unfold outgoingTo
  apply Finset.sum_eq_zero
  intro i _
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he ⟨ht, hs⟩
  apply hno e _ hs
  rw [(h.toward i).1 e he, ht]

theorem nested_or_small {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) (hk : 1 ≤ k) {v w : Fin n} {A B : Finset (Fin n)}
    (hv : Wit ends T D v A) (hmv : ∀ A', Wit ends T D v A' → A.card ≤ A'.card)
    (hw : Wit ends T D w B) (hmw : ∀ B', Wit ends T D w B' → B.card ≤ B'.card)
    (hvw : v ≠ w) (h2 : 2 ≤ (A ∩ B).card) : A ⊆ B ∨ B ⊆ A := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hnAB, hnBA⟩ := hcon
  have hne : (A ∩ B).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hU, hI, hcr⟩ := tight_union_inter h hv.2.2.1 hw.2.2.1 hne
  have hvB : v ∉ B := by
    intro hvB
    have := min_incl hv hmv (Finset.mem_inter.mpr ⟨hv.1, hvB⟩) h2 hI Finset.inter_subset_left
    exact hnAB (this ▸ Finset.inter_subset_right)
  have hwA : w ∉ A := by
    intro hwA
    have h2' : 2 ≤ (B ∩ A).card := by rwa [Finset.inter_comm] at h2
    have hI' : tight ends k (B ∩ A) := by rwa [Finset.inter_comm] at hI
    have := min_incl hw hmw (Finset.mem_inter.mpr ⟨hw.1, hwA⟩) h2' hI' Finset.inter_subset_left
    apply hnBA
    rw [← this]
    exact Finset.inter_subset_right
  have hrU : r ∉ A ∪ B := by
    intro hr
    rcases Finset.mem_union.mp hr with hr | hr
    · exact r_not_mem h hk hv hr
    · exact r_not_mem h hk hw hr
  have hsU := sumOut_of_not_mem h hU hrU
  have hcr' : ∀ e, ∀ a ∈ A \ B, ∀ b ∈ B \ A, ends e ≠ s(a, b) := by
    intro e a ha b hb heq
    have : e ∈ cross ends A B := by
      simp only [cross, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a, ha, b, hb, heq⟩
    rw [hcr] at this
    simp at this
  -- v keeps its witnessing arcs outside the union
  have hvout : (3 : ℝ) * k / 4 ≤ outgoingTo T D v (Finset.univ \ (A ∪ B)) := by
    have hsplit : Finset.univ \ A = (Finset.univ \ (A ∪ B)) ∪ (B \ A) := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]; tauto
    have hdisj : Disjoint (Finset.univ \ (A ∪ B)) (B \ A) := by
      rw [Finset.disjoint_left]; intro x hx hx'
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union] at hx hx'
      tauto
    have h0 : outgoingTo T D v (B \ A) = 0 := by
      apply no_edge_zero h
      intro e b hb heq
      exact hcr' e v (Finset.mem_sdiff.mpr ⟨hv.1, hvB⟩) b hb heq
    have := hv.2.2.2
    rw [hsplit, outgoingTo_union v hdisj, h0] at this
    simpa using this
  have hwout : (3 : ℝ) * k / 4 ≤ outgoingTo T D w (Finset.univ \ (A ∪ B)) := by
    have hsplit : Finset.univ \ B = (Finset.univ \ (A ∪ B)) ∪ (A \ B) := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]; tauto
    have hdisj : Disjoint (Finset.univ \ (A ∪ B)) (A \ B) := by
      rw [Finset.disjoint_left]; intro x hx hx'
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union] at hx hx'
      tauto
    have h0 : outgoingTo T D w (A \ B) = 0 := by
      apply no_edge_zero h
      intro e a ha heq
      exact hcr' e a ha w (Finset.mem_sdiff.mpr ⟨hw.1, hwA⟩) (by rw [heq, Sym2.eq_swap])
    have := hw.2.2.2
    rw [hsplit, outgoingTo_union w hdisj, h0] at this
    simpa using this
  have hpair := out_pair_le (T := T) (D := D) (Finset.mem_union_left B hv.1)
    (Finset.mem_union_right A hw.1) hvw
  rw [hsU] at hpair
  have h5 : ((outgoingTo T D v (Finset.univ \ (A ∪ B)) + outgoingTo T D w (Finset.univ \ (A ∪ B)) : ℕ) : ℝ)
      ≤ k := by exact_mod_cast hpair
  push_cast at h5
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

theorem gap {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) (hk : 1 ≤ k) {v w : Fin n} {A B : Finset (Fin n)}
    (hv : Wit ends T D v A)
    (hw : Wit ends T D w B) (hmw : ∀ B', Wit ends T D w B' → B.card ≤ B'.card)
    (hvw : v ≠ w) (hAB : A ⊆ B) : (A.card : ℝ) + k / 2 ≤ B.card := by
  have hwA : w ∉ A := by
    intro hwA
    have := min_incl hw hmw hwA hv.2.1 hv.2.2.1 hAB
    exact wit_distinct h hk (this ▸ hv) hw hvw
  have hvB : v ∈ B := hAB hv.1
  have hrB := r_not_mem h hk hw
  have hsB := sumOut_of_not_mem h hw.2.2.1 hrB
  have hpair := out_pair_le (T := T) (D := D) hvB hw.1 hvw
  rw [hsB] at hpair
  have hsplit : Finset.univ \ A = (Finset.univ \ B) ∪ (B \ A) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hx; by_cases hxB : x ∈ B
      · exact Or.inr ⟨hxB, hx⟩
      · exact Or.inl hxB
    · rintro (hx | ⟨_, hx⟩)
      · exact fun hxA => hx (hAB hxA)
      · exact hx
  have hdisj : Disjoint (Finset.univ \ B) (B \ A) := by
    rw [Finset.disjoint_left]; intro x hx hx'
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx hx'
    exact hx hx'.1
  have h1 := hv.2.2.2
  rw [hsplit, outgoingTo_union v hdisj] at h1
  have h2 := outgoingTo_le_card h v (B \ A)
  have h3 : ((outgoingTo T D v (Finset.univ \ B) + outgoingTo T D w (Finset.univ \ B) : ℕ) : ℝ)
      ≤ k := by exact_mod_cast hpair
  push_cast at h1 h3
  have h4 := hw.2.2.2
  have h5 : ((B \ A).card : ℝ) = B.card - A.card := by
    rw [Finset.card_sdiff_of_subset hAB]
    have := Finset.card_le_card hAB
    push_cast [Nat.cast_sub this]
    ring
  have h6 : ((outgoingTo T D v (B \ A) : ℕ) : ℝ) ≤ (B \ A).card := by exact_mod_cast h2
  linarith

theorem min_wit (ends : Fin m → Sym2 (Fin n)) (T : Trees k m) (D : Fin k → Direction n m)
    (v : Fin n) (hex : ∃ A, Wit ends T D v A) :
    ∃ A, Wit ends T D v A ∧ ∀ A', Wit ends T D v A' → A.card ≤ A'.card := by
  obtain ⟨A0, hA0⟩ := hex
  obtain ⟨A, hA, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun A => Wit ends T D v A)
    Finset.card ⟨A0, by simpa using hA0⟩
  exact ⟨A, by simpa using hA, fun A' hA' => hmin A' (by simpa using hA')⟩

end LowDiameterNashWilliams.Dev.L32
end

section
set_option autoImplicit false
open scoped BigOperators
open Classical
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Dev.L32
open LowDiameterNashWilliams.Main

variable {n m k : ℕ}

theorem inner_eq {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) {A : Finset (Fin n)} (hA : tight ends k A) (i : Fin k) :
    inner ends T i A + 1 = A.card := by
  have hne := ((tight_iff ends A).mp hA).1
  have hsum := ((tight_iff ends A).mp hA).2
  rw [edgeCount_eq h] at hsum
  by_contra hne'
  have hlt : inner ends T i A + 1 < A.card := lt_of_le_of_ne (inner_lt h i A hne) hne'
  have : ∑ j, (inner ends T j A + 1) < ∑ _j : Fin k, A.card :=
    Finset.sum_lt_sum (fun j _ => inner_lt h j A hne) ⟨i, Finset.mem_univ _, hlt⟩
  rw [Finset.sum_add_distrib] at this
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
  omega

theorem two_k_le_n {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) (hn : 2 ≤ n) : 2 * k ≤ n := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have h1 := identity h Finset.univ
  have h0 : sumOut T D (Finset.univ : Finset (Fin n)) = 0 := by
    unfold sumOut
    apply Finset.sum_eq_zero
    intro v _
    have := outgoingTo_le_card h v (Finset.univ \ Finset.univ : Finset (Fin n))
    simpa using this
  rw [h0, if_pos (Finset.mem_univ r)] at h1
  have ht : tight ends k (Finset.univ : Finset (Fin n)) := by
    rw [tight_iff]
    refine ⟨hne, ?_⟩
    simp only [Finset.card_univ, Fintype.card_fin] at h1 ⊢
    omega
  have := two_k_le h.simple ht (by simpa using hn)
  simpa using this

theorem core {ends : Fin m → Sym2 (Fin n)} {T : Trees k m} {D : Fin k → Direction n m}
    {r : Fin n} (h : Hyp ends T D r) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    ((exceptional ends T D r).card : ℝ) ≤ 5 * ((n : ℝ) / k) := by
  have hkn : 2 * k ≤ n := two_k_le_n h hn
  set E := (exceptional ends T D r).erase r with hE
  have hcardexc : (exceptional ends T D r).card ≤ E.card + 1 := by
    have hsub : exceptional ends T D r ⊆ insert r E := by
      intro v hv
      by_cases hvr : v = r
      · subst hvr; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hvr, hv⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have hex : ∀ v ∈ E, ∃ A, Wit ends T D v A := by
    intro v hv
    obtain ⟨hvr, hv'⟩ := Finset.mem_erase.mp hv
    simp only [exceptional, Finset.mem_filter, Finset.mem_univ, true_and] at hv'
    rcases hv' with rfl | ⟨A, hA⟩
    · exact absurd rfl hvr
    · exact ⟨A, hA⟩
  have hch : ∀ v, ∃ A, v ∈ E →
      (Wit ends T D v A ∧ ∀ A', Wit ends T D v A' → A.card ≤ A'.card) := by
    intro v
    by_cases hv : v ∈ E
    · obtain ⟨A, hA⟩ := min_wit ends T D v (hex v hv)
      exact ⟨A, fun _ => hA⟩
    · exact ⟨∅, fun h' => absurd h' hv⟩
  choose A hA using hch
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hrel : ∀ v ∈ E, ∀ w ∈ E, v ≠ w →
      ((A v ⊆ A w ∧ ((A v).card : ℝ) + (k : ℝ) / 2 ≤ (A w).card) ∨
       (A w ⊆ A v ∧ ((A w).card : ℝ) + (k : ℝ) / 2 ≤ (A v).card) ∨
       ¬ 2 ≤ (A v ∩ A w).card) := by
    intro v hv w hw hvw
    by_cases h2 : 2 ≤ (A v ∩ A w).card
    · rcases nested_or_small h hk (hA v hv).1 (hA v hv).2 (hA w hw).1 (hA w hw).2 hvw h2
        with hsub | hsub
      · exact Or.inl ⟨hsub, gap h hk (hA v hv).1 (hA w hw).1 (hA w hw).2 hvw hsub⟩
      · exact Or.inr (Or.inl ⟨hsub, gap h hk (hA w hw).1 (hA v hv).1 (hA v hv).2 hvw.symm hsub⟩)
    · exact Or.inr (Or.inr h2)
  let i0 : Fin k := ⟨0, hk⟩
  let E0 : Fin n → Finset (Fin m) := fun v => (T i0).filter fun e => ∀ x ∈ ends e, x ∈ A v
  have hsz : ∀ v ∈ E, (E0 v).card + 1 = (A v).card := fun v hv =>
    inner_eq h (hA v hv).1.2.2.1 i0
  have h2k : ∀ v ∈ E, 2 * k ≤ (A v).card := fun v hv =>
    two_k_le h.simple (hA v hv).1.2.2.1 (hA v hv).1.2.1
  have hmono : ∀ v w, A v ⊆ A w → E0 v ⊆ E0 w := by
    intro v w hsub e he
    simp only [E0, Finset.mem_filter] at he ⊢
    exact ⟨he.1, fun x hx => hsub (he.2 x hx)⟩
  have hdisj : ∀ v w, ¬ 2 ≤ (A v ∩ A w).card → Disjoint (E0 v) (E0 w) := by
    intro v w h2
    rw [Finset.disjoint_left]
    intro e he he'
    simp only [E0, Finset.mem_filter] at he he'
    have hnd := h.simple.2 e
    obtain ⟨h1, h1'⟩ := he
    obtain ⟨_, h2'⟩ := he'
    generalize hz : ends e = z at *
    induction z using Sym2.ind with
    | h a b =>
      have hab : a ≠ b := by simpa [Sym2.mk_isDiag_iff] using hnd
      apply h2
      have ha : a ∈ A v ∩ A w := Finset.mem_inter.mpr ⟨h1' a (by simp), h2' a (by simp)⟩
      have hb : b ∈ A v ∩ A w := Finset.mem_inter.mpr ⟨h1' b (by simp), h2' b (by simp)⟩
      exact Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩
  have hpos : ∀ v ∈ E, 1 ≤ (E0 v).card := fun v hv => by
    have := hsz v hv
    have := h2k v hv
    omega
  have hinj : Set.InjOn E0 (E : Set (Fin n)) := by
    intro v hv w hw hEq
    by_contra hvw
    have hv' : v ∈ E := hv
    have hw' : w ∈ E := hw
    rcases hrel v hv' w hw' hvw with ⟨_, hg⟩ | ⟨_, hg⟩ | hs
    · have h1 := hsz v hv'
      have h2 := hsz w hw'
      rw [hEq] at h1
      have : ((A v).card : ℝ) = (A w).card := by rw [← h1, ← h2]
      linarith
    · have h1 := hsz v hv'
      have h2 := hsz w hw'
      rw [hEq] at h1
      have : ((A v).card : ℝ) = (A w).card := by rw [← h1, ← h2]
      linarith
    · have hd := hdisj v w hs
      rw [hEq] at hd
      have := Finset.disjoint_self_iff_empty _ |>.mp hd
      have := hpos w hw'
      simp_all
  have hlam := LowDiameterNashWilliams.Dev.Laminar.laminar_card_le (E.image E0) (T i0)
    ((k : ℝ) / 2) (by positivity)
    (by
      intro X hX
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hX
      exact Finset.filter_subset _ _)
    (by
      intro X hX Y hY
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hX
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hY
      by_cases hvw : v = w
      · subst hvw; exact Or.inl (Finset.Subset.refl _)
      · rcases hrel v hv w hw hvw with ⟨hs, _⟩ | ⟨hs, _⟩ | hs
        · exact Or.inl (hmono v w hs)
        · exact Or.inr (Or.inl (hmono w v hs))
        · exact Or.inr (Or.inr (hdisj v w hs)))
    (by
      intro X hX
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hX
      have h1 := hsz v hv
      have h2 := h2k v hv
      have h3 : ((E0 v).card : ℝ) + 1 = (A v).card := by exact_mod_cast h1
      have h4 : (2 * k : ℝ) ≤ (A v).card := by exact_mod_cast h2
      linarith)
    (by
      intro X hX Y hY hXY
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hX
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hY
      have hvw : v ≠ w := by
        rintro rfl
        exact absurd hXY (ssubset_irrfl _)
      have h1 := hsz v hv
      have h2 := hsz w hw
      have h3 : ((E0 v).card : ℝ) + 1 = (A v).card := by exact_mod_cast h1
      have h4 : ((E0 w).card : ℝ) + 1 = (A w).card := by exact_mod_cast h2
      rcases hrel v hv w hw hvw with ⟨_, hg⟩ | ⟨hs, _⟩ | hs
      · linarith
      · exact absurd (hmono w v hs) (not_subset_of_ssubset hXY)
      · have hd := hdisj v w hs
        have : E0 v = ∅ := by
          have := Finset.disjoint_of_subset_right hXY.subset hd
          exact Finset.disjoint_self_iff_empty _ |>.mp this
        have := hpos v hv
        simp_all)
  rw [Finset.card_image_of_injOn hinj] at hlam
  have hT0 : ((T i0).card : ℝ) ≤ n := by
    have := inner_lt h i0 Finset.univ ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    have h' : inner ends T i0 Finset.univ = (T i0).card := by
      unfold inner
      congr 1
      apply Finset.filter_true_of_mem
      intro e _ v _
      exact Finset.mem_univ v
    rw [h'] at this
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this.le
  have hkpos : (0 : ℝ) < k := by linarith
  have hE4 : (E.card : ℝ) ≤ 4 * ((n : ℝ) / k) := by
    calc (E.card : ℝ) ≤ 2 * ((T i0).card : ℝ) / ((k : ℝ) / 2) := hlam
      _ ≤ 2 * (n : ℝ) / ((k : ℝ) / 2) := by gcongr
      _ = 4 * ((n : ℝ) / k) := by field_simp; ring
  have h1 : (1 : ℝ) ≤ (n : ℝ) / k := by
    rw [le_div_iff₀ hkpos]
    have : (k : ℝ) ≤ n := by exact_mod_cast (by omega : k ≤ n)
    linarith
  have hc : ((exceptional ends T D r).card : ℝ) ≤ E.card + 1 := by exact_mod_cast hcardexc
  linarith

end LowDiameterNashWilliams.Dev.L32

namespace LowDiameterNashWilliams.Main
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

theorem chk_lemma_3_2 :
  ∃ C : ℝ, 0 < C ∧ ∀ n m k : ℕ, 2 ≤ n → 1 ≤ k →
  ∀ (ends : Fin m → Sym2 (Fin n)) (T : Trees k m)
    (D : Fin k → Direction n m) (r : Fin n),
  Simple ends → TreePartition ends T → (∀ i, Toward ends (T i) (D i) r) →
    ((exceptional ends T D r).card : ℝ) ≤ C * ((n : ℝ) / k) := by
  refine ⟨5, by norm_num, ?_⟩
  intro n m k hn hk ends T D r hs hp ht
  exact LowDiameterNashWilliams.Dev.L32.core ⟨hs, hp, ht⟩ hn hk

end LowDiameterNashWilliams.Main
end

theorem solution : type_of% @LowDiameterNashWilliams.Main.chk_lemma_3_2 := @LowDiameterNashWilliams.Main.chk_lemma_3_2
