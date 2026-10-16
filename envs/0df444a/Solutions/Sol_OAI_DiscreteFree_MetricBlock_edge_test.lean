-- Prove2me | solution 1 for OAI.DiscreteFree.MetricBlock.edge_test
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:48:35.504397+00:00
-- url     : https://prove2.me/submissions/a6259ff4-c890-4e8a-9a74-ee3486accf31

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/ScalarTests.lean:L117-L157
-- (upload_full_project.md Phase 4): solution for node OAI.DiscreteFree.MetricBlock.edge_test. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights
import Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps
import Definitions.Def_OAI_Analysis_LipschitzFree_ScalarTests
import Theorems.Thm_OAI_DiscreteFree_labelBump_sub
import Theorems.Thm_OAI_DiscreteFree_opposing_scalar_extension

-- ---- from OAI.Analysis.LipschitzFree.PortGraphs ----
namespace OAI

/-!
# Port graphs, reduced walks, and capped-distance labels
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section

namespace DiscreteFree
open scoped BigOperators Classical

namespace PortGraph
variable {X D : Type*} (G : PortGraph X D)

theorem label_witness {C : Type*} (color : X → C) (cap : ℕ) (i : C) (x : X)
    (h : G.label color cap i x < cap) :
    ∃ w : List D, w.length = G.label color cap i x ∧ color (G.walk x w) = i := by
  have hh := Nat.find_spec (show ∃ n : ℕ, n = cap ∨ ∃ w : List D,
    w.length = n ∧ color (G.walk x w) = i from ⟨cap, Or.inl rfl⟩)
  exact hh.resolve_left (Nat.ne_of_lt h)

theorem label_step_le {C : Type*} (color : X → C) (cap : ℕ) (i : C)
    (x : X) (e : D) :
    G.label color cap i x ≤ G.label color cap i (G.move x e) + 1 := by
  by_cases h : G.label color cap i (G.move x e) < cap
  · obtain ⟨w, hw, hc⟩ := G.label_witness color cap i (G.move x e) h
    have ht := G.label_le_of_walk color cap i x (e::w) hc
    simpa [hw] using ht
  · exact (G.label_le color cap i x).trans (by omega)

end PortGraph

namespace BoundedWords
variable {D : Type*}

end BoundedWords

namespace PortGraph
variable {X D : Type*} [Fintype D] (G : PortGraph X D)

end PortGraph
end DiscreteFree

end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.BoxLabels ----
namespace OAI

/-!
# Finite box labels with the supremum metric
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped Classical

namespace BoxLabel
variable {C : Type*} [Fintype C] {cap : ℕ}

theorem distance_bound (a b : BoxLabel C cap) : distance a b ≤ cap := by
  rw [distance_le_iff]
  intro i
  have ha := (a i).isLt
  have hb := (b i).isLt
  unfold Nat.dist
  omega

end BoxLabel
end DiscreteFree
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.MetricClosure ----
namespace OAI

/-!
# Integer shortest-path metrics and Lipschitz descent
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section

namespace DiscreteFree.NatMetricClosure
open scoped Classical

variable {X : Type*} (w : X → X → ℕ)

theorem lipschitz_bound {Y : Type*} [PseudoMetricSpace Y] (f : X → Y)
    (hf : ∀ x y, dist (f x) (f y) ≤ (w x y : ℝ)) (x y : X) :
    dist (f x) (f y) ≤ (distance w x y : ℝ) := by
  have hcost (u : List X) (a : X) : dist (f a) (f y) ≤ cost w a y u := by
    induction u generalizing a with
    | nil => exact hf a y
    | cons b u ih =>
      calc
        dist (f a) (f y) ≤ dist (f a) (f b) + dist (f b) (f y) := dist_triangle _ _ _
        _ ≤ (w a b : ℝ) + cost w b y u := add_le_add (hf a b) (ih b)
        _ = (cost w a y (b::u) : ℝ) := by rw [cost_cons, Nat.cast_add]
  obtain ⟨u, hu⟩ := exists_shortest w x y
  simpa [hu] using hcost u x

end DiscreteFree.NatMetricClosure

end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.MetricBlock ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# Metric blocks obtained by adjoining finite label anchors
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.MetricBlock
open scoped Classical
variable {X D C : Type*} [Fintype C] (G : PortGraph X D) (color : X → C) (cap R : ℕ)

variable [Fact (0 < R)]

theorem originalLabel_step (x : X) (e : D) :
    BoxLabel.distance (originalLabel G color cap x) (originalLabel G color cap (G.move x e)) ≤ 1 := by
  rw [BoxLabel.distance_le_iff]
  intro i
  have h₁ := G.label_step_le color cap i x e
  have h₂ := G.label_step_le color cap i (G.move x e) (G.reverse e)
  rw [G.move_reverse] at h₂
  change Nat.dist (G.label color cap i x) (G.label color cap i (G.move x e)) ≤ 1
  unfold Nat.dist
  omega

omit [Fact (0 < R)] in
theorem label_weight (u v : Point G color cap R) :
    BoxLabel.distance (label G color cap R u) (label G color cap R v) ≤ weight G color cap R u v := by
  by_cases h : u = v
  · subst v; simp
  · cases u with
    | inl x =>
      cases v with
      | inl y =>
        simp only [weight, ite_eq_right h, label]
        split_ifs with he
        · obtain ⟨e, rfl⟩ := he
          exact originalLabel_step G color cap x e
        · exact (BoxLabel.distance_bound _ _).trans (by omega)
      | inr a =>
        simp only [weight, ite_eq_right h, label]
        split_ifs with ha
        · simp [ha]
        · exact (BoxLabel.distance_bound _ _).trans (by omega)
    | inr a =>
      cases v with
      | inl x =>
        simp only [weight, ite_eq_right h, label]
        split_ifs with ha
        · simp [ha]
        · exact (BoxLabel.distance_bound _ _).trans (by omega)
      | inr b =>
        simp only [weight, ite_eq_right h, label]
        omega

theorem label_lipschitz : LipschitzWith 1 (label G color cap R) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro u v
  simp only [NNReal.coe_one, one_mul]
  exact NatMetricClosure.lipschitz_bound (weight G color cap R) (label G color cap R)
    (fun u v => by rw [BoxLabel.dist_eq]; exact_mod_cast label_weight G color cap R u v) u v

end DiscreteFree.MetricBlock
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.SignedTests ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Signed variation, scalar extension, and incidence averaging
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree

section Records

variable {D S : Type*}

theorem exceptional_of_extensions {r t : D → S → ℕ} {e f : D} {j k : S}
    (hr : ∀ g : D, g ≠ f → 1 + t g k ≤ r e j)
    (ht : ∀ g : D, g ≠ e → 1 + r g j ≤ t f k) :
    Exceptional r e j ∨ Exceptional t f k := by
  classical
  by_contra h
  obtain ⟨h₁, h₂⟩ := not_or.mp h
  simp only [Exceptional, not_forall, not_lt] at h₁ h₂
  obtain ⟨g, hge, hg⟩ := h₁
  obtain ⟨a, haf, ha⟩ := h₂
  have hrg := hr a haf
  have hta := ht g hge
  omega

end Records

section SignedTests

variable {S : Type*} [Fintype S]

end SignedTests
section

variable {N : Type*} [MetricSpace N]

end

variable {X D S : Type*} [Fintype X] [Fintype D] [Fintype S]

end DiscreteFree

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.GraphWalks ----
namespace OAI

/-!
# Matched graph walks and exceptional record estimates
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.PortGraph
open scoped Classical
variable {X D S : Type*} (G : PortGraph X D)
    (compatible : X → S → Prop) (trans : S → S → Prop)

theorem Matched.compat {x : X} {j : S} {w : List D}
    (h : G.Matched compatible trans x j w) : compatible x j := by
  cases w with
  | nil => exact h
  | cons e w => exact h.1

theorem Matched.take {x : X} {j : S} {w : List D}
    (h : G.Matched compatible trans x j w) (n : ℕ) :
    G.Matched compatible trans x j (w.take n) := by
  induction n generalizing x j w with
  | zero => exact h.compat
  | succ n ih =>
    cases w with
    | nil => exact h
    | cons e w =>
      obtain ⟨hx, k, hk, hw⟩ := h
      exact ⟨hx, k, hk, ih hw⟩

theorem Good.length_lt {n : ℕ} {x : X} (hgood : G.Good compatible trans n x)
    {j : S} {w : List D} (hr : G.Reduced w) (hm : G.Matched compatible trans x j w) :
    w.length < n := by
  by_contra h
  have hn : n ≤ w.length := Nat.le_of_not_gt h
  apply hgood j (w.take n) (by simp [List.length_take, Nat.min_eq_left hn])
    (List.IsChain.take hr n)
  exact Matched.take G compatible trans hm n

theorem record_spec (n : ℕ) (x : X) (e : D) (j : S) :
    G.RecordLength compatible trans x e j (G.record compatible trans n x e j) :=
  Nat.findGreatest_spec (Nat.zero_le n) (Or.inl rfl)

theorem le_record {n : ℕ} {x : X} (hgood : G.Good compatible trans n x)
    {e : D} {j : S} {w : List D} (hr : G.Reduced (e::w))
    (hm : G.Matched compatible trans x j (e::w)) :
    (e::w).length ≤ G.record compatible trans n x e j :=
  Nat.le_findGreatest (Nat.le_of_lt (Good.length_lt G compatible trans hgood hr hm)) (Or.inr ⟨w, rfl, hr, hm⟩)

theorem record_extension {n : ℕ} {x : X} {e g : D} {j k : S}
    (hx : G.Good compatible trans n x)
    (hc : compatible x j) (hd : compatible (G.move x e) k) (ht : trans j k)
    (hg : g ≠ G.reverse e) :
    1 + G.record compatible trans n (G.move x e) g k ≤
      G.record compatible trans n x e j := by
  rcases G.record_spec compatible trans n (G.move x e) g k with hz | ⟨w, hw, hr, hm⟩
  · rw [hz]
    exact G.le_record compatible trans hx (List.isChain_singleton e) ⟨hc, k, ht, hd⟩
  · have hr' : G.Reduced (e::g::w) := List.isChain_cons_cons.mpr ⟨hg, hr⟩
    have hm' : G.Matched compatible trans x j (e::g::w) := ⟨hc, k, ht, hm⟩
    have hh := G.le_record compatible trans hx hr' hm'
    simpa only [List.length_cons, hw, Nat.add_comm] using hh

theorem matched_exceptional_endpoint {n : ℕ} {x : X} {e : D} {j k : S}
    (hx : G.Good compatible trans n x) (hy : G.Good compatible trans n (G.move x e))
    (hc : compatible x j) (hd : compatible (G.move x e) k)
    (ht : trans j k) (ht' : trans k j) :
    Exceptional (G.record compatible trans n x) e j ∨
      Exceptional (G.record compatible trans n (G.move x e)) (G.reverse e) k := by
  apply exceptional_of_extensions
  · intro g hg
    exact G.record_extension compatible trans hx hc hd ht hg
  · intro g hg
    have h := G.record_extension compatible trans hy hd
      (show compatible (G.move (G.move x e) (G.reverse e)) j by simpa only [G.move_reverse])
      ht' (show g ≠ G.reverse (G.reverse e) by simpa only [G.reverse_involutive e])
    simpa only [G.move_reverse] using h

end DiscreteFree.PortGraph
end

noncomputable section
namespace DiscreteFree.PortGraph
open scoped Classical
variable {X D S : Type*} (G : PortGraph X D)
    (compatible : X → S → Prop) (trans : S → S → Prop)

end DiscreteFree.PortGraph
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.LabelBumps ----
namespace OAI

/-!
# Lipschitz label bumps and affine mass estimates
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M N : Type*} [MetricSpace M] [MetricSpace N]

omit [MetricSpace M] in
theorem labelBump_nonneg (h : M → N) (a : N) {L K : ℝ} (hL : 0 ≤ L) (t : M) :
    0 ≤ labelBump h a L K t := mul_nonneg hL (le_max_right _ _)

omit [MetricSpace M] in
theorem labelBump_le (h : M → N) (a : N) {L K : ℝ} (hL : 0 ≤ L) (hK : 0 < K) (t : M) :
    labelBump h a L K t ≤ L := by
  unfold labelBump
  have hm : max (1-dist a (h t)/K) 0 ≤ 1 := max_le (by have := div_nonneg (dist_nonneg : 0 ≤ dist a (h t)) hK.le; linarith) (by norm_num)
  simpa using mul_le_mul_of_nonneg_left hm hL

theorem labelBump_lipschitz (h : M → N) (hh : LipschitzWith 1 h) (a : N)
    {L K : ℝ} (hL : 0 ≤ L) (hK : 0 < K) (hLK : L ≤ K) :
    LipschitzWith 1 (labelBump h a L K) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  exact (labelBump_sub h hh a hL hK x y).trans
    (mul_le_of_le_one_left dist_nonneg ((div_le_one hK).mpr hLK))

omit [MetricSpace M] in
theorem labelBump_positive (h : M → N) (a : N) {L K : ℝ}
    (hL : 0 < L) (hK : 0 < K) {t : M} (ht : 0 < labelBump h a L K t) :
    dist a (h t) < K := by
  unfold labelBump at ht
  have hm : 0 < max (1-dist a (h t)/K) 0 := (mul_pos_iff_of_pos_left hL).mp ht
  have hs : dist a (h t)/K < 1 := by
    have hh := (lt_max_iff).mp hm
    rcases hh with hh | hh
    · linarith
    · exact False.elim (lt_irrefl (0 : ℝ) hh)
  exact (div_lt_one hK).mp hs

end DiscreteFree
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.ScalarTests ----
namespace OAI

/-!
# Finite-state records and opposing scalar Lipschitz tests
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.MetricBlock
open scoped Classical
variable {X E C : Type*} [Fintype C] [Fintype E]
    (G : PortGraph X E) (color : X → C) (cap R L K : ℕ) [Fact (0 < R)]

omit [Fintype E] in
theorem exceptional_endpoint (S : Finset (Point G color cap R)) (n : ℕ) (x : X) (e : E)
    (j k : S) (hj : Compatible G color cap R L K x j.val)
    (hk : Compatible G color cap R L K (G.move x e) k.val)
    (ht : Transition G color cap R L j.val k.val) :
    j ∈ exceptionSet G color cap R L K S n x e ∨
      k ∈ exceptionSet G color cap R L K S n (G.move x e) (G.reverse e) := by
  by_cases hx : G.Good (fun x (j : S) => Compatible G color cap R L K x j.val)
      (fun j k : S => Transition G color cap R L j.val k.val) n x
  · by_cases hy : G.Good (fun x (j : S) => Compatible G color cap R L K x j.val)
        (fun j k : S => Transition G color cap R L j.val k.val) n (G.move x e)
    · have hh := G.matched_exceptional_endpoint
        (fun x (j : S) => Compatible G color cap R L K x j.val)
        (fun j k : S => Transition G color cap R L j.val k.val) hx hy hj hk ht
        (show Transition G color cap R L k.val j.val by simpa only [Transition, dist_comm] using ht)
      exact hh.imp Or.inr Or.inr
    · exact Or.inr (Or.inl hy)
  · exact Or.inl (Or.inl hx)

omit [Fintype E] in

theorem positive_bump_compatible (hL : 0 < L) (hK : 0 < K)
    (x : X) (e : E) (j k : Point G color cap R) (hjk : dist j k < (2*L : ℕ))
    (hj : 0 < labelBump (label G color cap R) (originalLabel G color cap x) L K j) :
    Compatible G color cap R L K x j ∧ Compatible G color cap R L K (G.move x e) k := by
  have hLj : dist (originalLabel G color cap x) (label G color cap R j) < K :=
    labelBump_positive _ _ (by exact_mod_cast hL) (by exact_mod_cast hK) hj
  have hedge : dist (originalLabel G color cap (G.move x e)) (originalLabel G color cap x) ≤ 1 := by
    rw [BoxLabel.dist_eq, BoxLabel.distance_comm]
    exact_mod_cast originalLabel_step G color cap x e
  have hstates : dist (label G color cap R j) (label G color cap R k) ≤ dist j k := by
    simpa only [NNReal.coe_one, one_mul] using (label_lipschitz G color cap R).dist_le_mul j k
  constructor
  · unfold Compatible
    push_cast
    linarith [show 0 ≤ (L : ℝ) from Nat.cast_nonneg L]
  · have htri := dist_triangle (originalLabel G color cap (G.move x e))
      (originalLabel G color cap x) (label G color cap R k)
    have htri' := dist_triangle (originalLabel G color cap x)
      (label G color cap R j) (label G color cap R k)
    unfold Compatible
    push_cast at hjk ⊢
    linarith

omit [Fintype E] in

theorem edge_test (hL : 0 < L) (hK : 0 < K) (hLK : L ≤ K)
    (S : Finset (Point G color cap R)) (n : ℕ) (x : X) (e : E) :
    ∃ f : Point G color cap R → ℝ, LipschitzWith 1 f ∧ (∀ z, |f z| ≤ L) ∧
      (∀ j : S, j ∉ exceptionSet G color cap R L K S n x e →
        f j.val = labelBump (label G color cap R) (originalLabel G color cap x) L K j.val) ∧
      (∀ j : S, j ∉ exceptionSet G color cap R L K S n (G.move x e) (G.reverse e) →
        f j.val = -labelBump (label G color cap R) (originalLabel G color cap (G.move x e)) L K j.val) := by
  let E₁ := exceptionSet G color cap R L K S n x e
  let E₂ := exceptionSet G color cap R L K S n (G.move x e) (G.reverse e)
  let P : Set (Point G color cap R) := {j | ∃ hj : j ∈ S, (⟨j,hj⟩ : S) ∉ E₁}
  let Q : Set (Point G color cap R) := {j | ∃ hj : j ∈ S, (⟨j,hj⟩ : S) ∉ E₂}
  let b := labelBump (label G color cap R) (originalLabel G color cap x) (L : ℝ) (K : ℝ)
  let c := labelBump (label G color cap R) (originalLabel G color cap (G.move x e)) (L : ℝ) (K : ℝ)
  have hL' : 0 ≤ (L : ℝ) := Nat.cast_nonneg _
  have hK' : 0 < (K : ℝ) := by exact_mod_cast hK
  have hLK' : (L : ℝ) ≤ K := by exact_mod_cast hLK
  have hb (z) : 0 ≤ b z ∧ b z ≤ L := ⟨labelBump_nonneg _ _ hL' _, labelBump_le _ _ hL' hK' _⟩
  have hc (z) : 0 ≤ c z ∧ c z ≤ L := ⟨labelBump_nonneg _ _ hL' _, labelBump_le _ _ hL' hK' _⟩
  have hcross : ∀ j ∈ P, ∀ k ∈ Q, dist j k < 2*(L : ℝ) → b j = 0 ∧ c k = 0 := by
    rintro j ⟨hj,hEj⟩ k ⟨hk,hEk⟩ hd
    have hd' : dist j k < (2*L : ℕ) := by exact_mod_cast hd
    have hfalse (hcompat : Compatible G color cap R L K x j ∧
        Compatible G color cap R L K (G.move x e) k) : False := by
      have hex := exceptional_endpoint G color cap R L K S n x e ⟨j,hj⟩ ⟨k,hk⟩
        hcompat.1 hcompat.2 hd'.le
      exact hex.elim hEj hEk
    constructor
    · by_contra hne
      exact hfalse (positive_bump_compatible G color cap R L K hL hK x e j k hd'
        (lt_of_le_of_ne (hb j).1 (Ne.symm hne)))
    · by_contra hne
      have hcomp := positive_bump_compatible G color cap R L K hL hK (G.move x e) (G.reverse e) k j
        (by simpa only [dist_comm] using hd') (lt_of_le_of_ne (hc k).1 (Ne.symm hne))
      rw [G.move_reverse] at hcomp
      exact hfalse hcomp.symm
  obtain ⟨f,hf,hbound,hfP,hfQ⟩ := opposing_scalar_extension P Q b c L hL'
    (labelBump_lipschitz _ (label_lipschitz G color cap R) _ hL' hK' hLK')
    (labelBump_lipschitz _ (label_lipschitz G color cap R) _ hL' hK' hLK') hb hc hcross
  exact ⟨f,hf,hbound,fun j hj => hfP ⟨j.property,hj⟩,fun j hj => hfQ ⟨j.property,hj⟩⟩

end DiscreteFree.MetricBlock
end

end

end OAI

-- ---- platform node ----
open OAI OAI.DiscreteFree OAI.DiscreteFree.MetricBlock
open scoped BigOperators ENNReal
open scoped Classical


theorem solution : type_of% @_root_.OAI.DiscreteFree.MetricBlock.edge_test := @_root_.OAI.DiscreteFree.MetricBlock.edge_test
