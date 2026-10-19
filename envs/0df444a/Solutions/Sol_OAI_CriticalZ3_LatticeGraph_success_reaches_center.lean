-- Prove2me | solution 1 for OAI.CriticalZ3.LatticeGraph.success_reaches_center
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:55:41.030229+00:00
-- url     : https://prove2.me/submissions/ffa1cfca-7226-40e7-af25-f0bb48d1b72f

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials

open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Classical
variable (G : LatticeGraph)
theorem cz_nn_close {x y : Vertex} (h : NearestNeighbor x y) (i : Fin 3) : |x i - y i| ≤ 1 := by
  obtain ⟨j, h | h⟩ := h <;> subst h <;> simp only [step] <;> split_ifs <;> simp

theorem cz_entry (C : Box) {y : Vertex} (hy : C.Exterior y) :
    C.Contains (C.entry y) ∧ NearestNeighbor y (C.entry y) := by
  unfold Box.entry; rw [dif_pos hy]; exact hy.2.choose_spec

theorem cz_entry_in_seed (C : Box) (r : ℕ) (hw : ∀ i, C.lower i+r ≤ C.upper i-r) {y : Vertex}
    (hy : C.Exterior y) : (C.seedBox r y).Contains (C.entry y) := by
  obtain ⟨hc, -⟩ := cz_entry C hy
  unfold Box.seedBox
  rw [Box.contains_cube]
  intro i
  have h2 := hc i
  have h3 := hw i
  unfold Box.relayCenter Box.seedCenter
  rw [abs_le]
  rcases le_total (C.upper i - r) (C.entry y i) with h5 | h5
  · rw [min_eq_left h5]
    rcases le_total (C.lower i + r) (C.upper i - r) with h6 | h6
    · rw [max_eq_right h6]; constructor <;> linarith [h2.1, h2.2]
    · rw [max_eq_left h6]; constructor <;> linarith [h2.1, h2.2]
  · rw [min_eq_right h5]
    rcases le_total (C.lower i + r) (C.entry y i) with h6 | h6
    · rw [max_eq_right h6]; constructor <;> linarith [h2.1, h2.2]
    · rw [max_eq_left h6]; constructor <;> linarith [h2.1, h2.2]

theorem cz_nb_inc {u v : Vertex} (h : NearestNeighbor u v) : Incidence (neighborBond u v) u v := by
  unfold neighborBond; rw [dif_pos h]; exact (LatticeGraph.neighbor_incidence h).choose_spec

theorem cz_nb_mem (B : Box) {u v : Vertex} (h : NearestNeighbor u v) (hu : B.Contains u)
    (hv : B.Contains v) : neighborBond u v ∈ B.bonds := by
  rw [Box.mem_bonds]
  rcases cz_nb_inc h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1 ▸ hu, h2 ▸ hv⟩
  · exact ⟨h1 ▸ hv, h2 ▸ hu⟩

theorem cz_box_conn_aux (B : Box) (y : Vertex) (hy : B.Contains y) :
    ∀ n : ℕ, ∀ x : Vertex, (∑ i, (x i - y i).natAbs) = n → B.Contains x →
      Relation.ReflTransGen B.Within x y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hn hx
    by_cases hxy : x = y
    · subst hxy; exact Relation.ReflTransGen.refl
    · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
        by_contra h; push_neg at h; exact hxy (funext h)
      rcases lt_or_gt_of_ne hi with hlt | hgt
      · have hx' : B.Contains (step x i) := by
          intro j; have := hx j; have := hy j
          simp only [step]; split_ifs with h <;> [subst h; skip] <;> constructor <;> omega
        refine Relation.ReflTransGen.head ⟨⟨i, Or.inl rfl⟩, hx, hx'⟩ (ih _ ?_ _ rfl hx')
        rw [← hn]
        apply Finset.sum_lt_sum
        · intro j _; simp only [step]; split_ifs with h <;> [subst h; skip] <;> omega
        · exact ⟨i, Finset.mem_univ _, by simp only [step, if_true]; omega⟩
      · have hx' : B.Contains (backstep x i) := by
          intro j; have := hx j; have := hy j
          simp only [backstep]; split_ifs with h <;> [subst h; skip] <;> constructor <;> omega
        refine Relation.ReflTransGen.head ⟨⟨i, Or.inr (step_backstep x i).symm⟩, hx, hx'⟩
          (ih _ ?_ _ rfl hx')
        rw [← hn]
        apply Finset.sum_lt_sum
        · intro j _; simp only [backstep]; split_ifs with h <;> [subst h; skip] <;> omega
        · exact ⟨i, Finset.mem_univ _, by simp only [backstep, if_true]; omega⟩

theorem cz_lift_path (G : LatticeGraph) {r : Vertex → Vertex → Prop} {s : G.Node → G.Node → Prop}
    (hmem : ∀ x y, r x y → y ∈ G.vertices)
    (hrel : ∀ (x y : G.Node), r x.1 y.1 → s x y)
    {x y : G.Node} (h : Relation.ReflTransGen r x.1 y.1) : Relation.ReflTransGen s x y := by
  have key : ∀ b, Relation.ReflTransGen r x.1 b →
      ∃ hb : b ∈ G.vertices, Relation.ReflTransGen s x ⟨b, hb⟩ := by
    intro b hb
    induction hb with
    | refl => exact ⟨x.2, Relation.ReflTransGen.refl⟩
    | @tail c b _ hcb ih =>
      obtain ⟨hc, hxc⟩ := ih
      exact ⟨hmem c b hcb, hxc.tail (hrel ⟨c, hc⟩ ⟨b, hmem c b hcb⟩ hcb)⟩
  obtain ⟨_, h'⟩ := key y.1 h
  exact h'

theorem solution (m : Model) (C : Box) (r : ℕ)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) (hC : G.ContainsBox (C.expand 1))
    {ω : m.Config} {o y : G.Node} (hy : y.1 ∈ G.entrants m C ω o)
    (hs : ∀ e ∈ C.successBits r m y.1, ω e = true) :
    ∃ v : G.Node, v.1 = C.relayCenter r y.1 ∧ G.Conn m ω o v := by
  rw [mem_entrants] at hy
  obtain ⟨hext, ho, hopen, hreach⟩ := hy
  obtain ⟨hec, hnn⟩ := cz_entry C hext
  have hseedC := C.seedBox_contained r hw y.1
  have hC1 : ∀ x, C.Contains x → (C.expand 1).Contains x := fun x hx => Box.contains_expand C 1 hx
  have hseedG : G.ContainsBox (C.seedBox r y.1) :=
    ContainsBox.mono G hC (fun x hx => hC1 x (hseedC x hx))
  have hyE : (C.expand 1).Contains y.1 := by
    intro i
    have h1 := cz_nn_close hnn i
    have h2 := hec i
    change C.lower i - 1 ≤ y.1 i ∧ y.1 i ≤ C.upper i + 1
    rw [abs_le] at h1
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have heG : C.entry y.1 ∈ G.vertices := containsBox_node G hC (hC1 _ hec)
  set e : G.Node := ⟨C.entry y.1, heG⟩ with he
  have hcen : (C.seedBox r y.1).Contains (C.relayCenter r y.1) := by
    unfold Box.seedBox; exact Box.center_mem_cube _ _
  have hcG : C.relayCenter r y.1 ∈ G.vertices := containsBox_node G hseedG hcen
  refine ⟨⟨C.relayCenter r y.1, hcG⟩, rfl, ?_⟩
  have hseedPath : Relation.ReflTransGen (C.seedBox r y.1).Within (C.entry y.1) (C.relayCenter r y.1) :=
    cz_box_conn_aux _ _ hcen _ _ rfl (cz_entry_in_seed C r hw hext)
  have hentrySeed := cz_entry_in_seed C r hw hext
  cases m
  · -- bond
    have hreach' : Relation.ReflTransGen (G.BondAdj ω) o y :=
      Relation.ReflTransGen.mono (fun u v huv => huv.2.2) _ _ hreach
    have hstep : G.BondAdj ω y e := by
      refine ⟨neighborBond y.1 (C.entry y.1), hC.2 (cz_nb_mem _ hnn hyE (hC1 _ hec)), cz_nb_inc hnn, ?_⟩
      apply hs
      simp [Box.successBits, Box.entryBit]
    have hpath : Relation.ReflTransGen (G.BondAdj ω) e ⟨C.relayCenter r y.1, hcG⟩ := by
      refine cz_lift_path G (r := (C.seedBox r y.1).Within)
        (fun u v huv => containsBox_node G hseedG huv.2.2) (fun u v huv => ?_) hseedPath
      obtain ⟨hnn', hu, hv⟩ := huv
      refine ⟨neighborBond u.1 v.1, hseedG.2 (cz_nb_mem _ hnn' hu hv), cz_nb_inc hnn', ?_⟩
      apply hs
      simp only [Box.successBits, Finset.mem_insert]
      exact Or.inr (cz_nb_mem _ hnn' hu hv)
    exact hreach'.trans (Relation.ReflTransGen.head hstep hpath)
  · -- site
    have hωy : ω y.1 = true := by
      clear hs
      induction hreach with
      | refl => exact hopen
      | tail _ huv _ => exact huv.2.2.2.2
    have hreach' : Relation.ReflTransGen (HyperedgeComparison.Site.OpenAdj G.graph (fun z => ω z.1)) o y :=
      Relation.ReflTransGen.mono (fun u v huv => huv.2.2) _ _ hreach
    have hωs : ∀ x, (C.seedBox r y.1).Contains x → ω x = true := fun x hx => hs x (by
      simp only [Box.successBits, Box.mem_vertices]; exact hx)
    have hstep : HyperedgeComparison.Site.OpenAdj G.graph (fun z => ω z.1) y e :=
      ⟨⟨neighborBond y.1 (C.entry y.1), hC.2 (cz_nb_mem _ hnn hyE (hC1 _ hec)), cz_nb_inc hnn⟩,
        hωy, hωs _ hentrySeed⟩
    have hpath : Relation.ReflTransGen (HyperedgeComparison.Site.OpenAdj G.graph (fun z => ω z.1)) e
        ⟨C.relayCenter r y.1, hcG⟩ := by
      refine cz_lift_path G (r := (C.seedBox r y.1).Within)
        (fun u v huv => containsBox_node G hseedG huv.2.2) (fun u v huv => ?_) hseedPath
      obtain ⟨hnn', hu, hv⟩ := huv
      exact ⟨⟨neighborBond u.1 v.1, hseedG.2 (cz_nb_mem _ hnn' hu hv), cz_nb_inc hnn'⟩, hωs _ hu, hωs _ hv⟩
    exact ⟨hopen, hreach'.trans (Relation.ReflTransGen.head hstep hpath)⟩

