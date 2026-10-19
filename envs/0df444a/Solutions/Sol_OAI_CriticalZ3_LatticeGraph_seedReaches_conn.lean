-- Prove2me | solution 1 for OAI.CriticalZ3.LatticeGraph.seedReaches_conn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:19:05.779979+00:00
-- url     : https://prove2.me/submissions/9a10beed-4161-446a-b56a-65df32d275b1

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
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality

open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)
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

theorem cz_cube_iff (c x : Vertex) (n : ℕ) : x ∈ cube c n ↔ (Box.cube c n).Contains x := by
  rw [mem_cube, Box.contains_cube]
  refine forall_congr' fun i => ?_
  rw [abs_le]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem cz_step_sum (z : Vertex) (k : Fin 3) : ∑ j, step z k j = ∑ j, z j + 1 := by
  simp [step, Finset.sum_add_distrib]

theorem cz_step_inj {x : Vertex} {i j : Fin 3} (h : step x i = step x j) : i = j := by
  by_contra hne
  have := congrFun h i
  simp only [step, if_neg (Ne.symm hne)] at this
  simp at this

theorem cz_step_step_ne (x : Vertex) (i k : Fin 3) : x ≠ step (step x i) k := by
  intro h
  have := congrArg (fun z : Vertex => ∑ j, z j) h
  simp only [cz_step_sum] at this
  omega

theorem cz_bondOpen_nn {ω : BondConfig} {x y : Vertex} (h : BondOpen ω x y) :
    NearestNeighbor x y ∧ ω (neighborBond x y) = true := by
  have hnn : NearestNeighbor x y := by
    rcases h with ⟨i, h1, _⟩ | ⟨i, h1, _⟩
    · exact ⟨i, Or.inl h1⟩
    · exact ⟨i, Or.inr h1⟩
  refine ⟨hnn, ?_⟩
  have hinc := cz_nb_inc hnn
  set e := neighborBond x y with he
  rcases h with ⟨i, h1, h2⟩ | ⟨i, h1, h2⟩
  · rcases hinc with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have hi : e.2 = i := by
        rw [← e1] at e2; exact cz_step_inj (e2.symm.trans h1)
      have : e = (x, i) := Prod.ext e1.symm hi
      rw [this]; exact h2
    · exfalso; rw [← e1] at e2; rw [h1] at e2; exact cz_step_step_ne x i e.2 e2
  · rcases hinc with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exfalso; rw [← e1] at e2; rw [h1] at e2; exact cz_step_step_ne y i e.2 e2
    · have hi : e.2 = i := by
        rw [← e1] at e2; exact cz_step_inj (e2.symm.trans h1)
      have : e = (y, i) := Prod.ext e1.symm hi
      rw [this]; exact h2

theorem solution {c : Vertex} {a b : ℕ} (hab : a ≤ b)
    (hB : G.ContainsBox (Box.cube c b)) (T : Set Vertex) {ω : m.Config}
    {v : G.Node} (hv : v.1 = c)
    (hO : ω ∈ allValue ((Box.cube c a).bits m) true)
    (hE : ω ∈ m.SeedReaches c a b T) : G.Meets m ω v T := by
  obtain ⟨x, hx, hxo, y, hy, hxy⟩ := hE
  have hab' : ∀ z, (Box.cube c a).Contains z → (Box.cube c b).Contains z := by
    intro z hz; rw [Box.contains_cube] at hz ⊢; intro i; have := hz i
    have : (a : ℤ) ≤ b := by exact_mod_cast hab
    linarith
  have hBv : ∀ z, (Box.cube c b).Contains z → z ∈ G.vertices := fun z hz => containsBox_node G hB hz
  have hxG : x ∈ G.vertices := hBv x (hab' x ((cz_cube_iff c x a).mp hx))
  have hyG : y ∈ G.vertices := by
    rcases Relation.ReflTransGen.cases_tail hxy with h | ⟨z, _, hz⟩
    · rw [h]; exact hxG
    · exact hBv y ((cz_cube_iff c y b).mp hz.2.1)
  have hcx : Relation.ReflTransGen (Box.cube c a).Within c x :=
    (cz_box_conn_aux _ _ ((cz_cube_iff c x a).mp hx) _ _ rfl (Box.center_mem_cube c a))
  have hopenA : ∀ e ∈ (Box.cube c a).bits m, ω e = true := fun e he => hO e he
  refine ⟨⟨y, hyG⟩, hy, ?_⟩
  cases m
  · -- bond
    have h1 : Relation.ReflTransGen (G.BondAdj ω) v ⟨x, hxG⟩ := by
      have hvc : v = ⟨c, hv ▸ v.2⟩ := Subtype.ext hv
      rw [hvc]
      refine cz_lift_path G (r := (Box.cube c a).Within)
        (fun u w huw => hBv w (hab' w huw.2.2)) (fun u w huw => ?_) hcx
      obtain ⟨hnn, hu, hw⟩ := huw
      exact ⟨neighborBond u.1 w.1, hB.2 (cz_nb_mem _ hnn (hab' _ hu) (hab' _ hw)), cz_nb_inc hnn,
        hopenA _ (cz_nb_mem _ hnn hu hw)⟩
    have h2 : Relation.ReflTransGen (G.BondAdj ω) ⟨x, hxG⟩ ⟨y, hyG⟩ := by
      refine cz_lift_path G (r := Within (cube c b) (Model.BasicAdj .bond ω))
        (fun u w huw => hBv w ((cz_cube_iff c w b).mp huw.2.1)) (fun u w huw => ?_) hxy
      obtain ⟨hu, hw, hop⟩ := huw
      obtain ⟨hnn, hω⟩ := cz_bondOpen_nn hop
      exact ⟨neighborBond u.1 w.1, hB.2 (cz_nb_mem _ hnn ((cz_cube_iff c _ b).mp hu)
        ((cz_cube_iff c _ b).mp hw)), cz_nb_inc hnn, hω⟩
    exact h1.trans h2
  · -- site
    have hωs : ∀ z, (Box.cube c a).Contains z → ω z = true := fun z hz =>
      hopenA z (by simp only [Box.bits, Box.mem_vertices]; exact hz)
    have hvc : v = ⟨c, hv ▸ v.2⟩ := Subtype.ext hv
    refine ⟨by show ω v.1 = true; rw [hv]; exact hωs c (Box.center_mem_cube c a), ?_⟩
    have h1 : Relation.ReflTransGen (HyperedgeComparison.Site.OpenAdj G.graph (fun z => ω z.1))
        v ⟨x, hxG⟩ := by
      rw [hvc]
      refine cz_lift_path G (r := (Box.cube c a).Within)
        (fun u w huw => hBv w (hab' w huw.2.2)) (fun u w huw => ?_) hcx
      obtain ⟨hnn, hu, hw⟩ := huw
      exact ⟨⟨neighborBond u.1 w.1, hB.2 (cz_nb_mem _ hnn (hab' _ hu) (hab' _ hw)), cz_nb_inc hnn⟩,
        hωs _ hu, hωs _ hw⟩
    have h2 : Relation.ReflTransGen (HyperedgeComparison.Site.OpenAdj G.graph (fun z => ω z.1))
        ⟨x, hxG⟩ ⟨y, hyG⟩ := by
      refine cz_lift_path G (r := Within (cube c b) (Model.BasicAdj .site ω))
        (fun u w huw => hBv w ((cz_cube_iff c w b).mp huw.2.1)) (fun u w huw => ?_) hxy
      obtain ⟨hu, hw, ⟨hnn, hωu, hωw⟩⟩ := huw
      exact ⟨⟨neighborBond u.1 w.1, hB.2 (cz_nb_mem _ hnn ((cz_cube_iff c _ b).mp hu)
        ((cz_cube_iff c _ b).mp hw)), cz_nb_inc hnn⟩, hωu, hωw⟩
    exact h1.trans h2

