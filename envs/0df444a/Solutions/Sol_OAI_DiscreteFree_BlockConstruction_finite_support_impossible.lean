-- Prove2me | solution 1 for OAI.DiscreteFree.BlockConstruction.finite_support_impossible
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T11:01:05.486832+00:00
-- url     : https://prove2.me/submissions/9c2282ab-4483-4427-bece-34ebd873cd15

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/BlockObstruction.lean:L102-L174
-- (upload_full_project.md Phase 4): solution for node OAI.DiscreteFree.BlockConstruction.finite_support_impossible. The node keeps its source
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
import Definitions.Def_OAI_Analysis_LipschitzFree_FiniteQuotients
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphGirth
import Definitions.Def_OAI_Analysis_LipschitzFree_ColorCounting
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphColoring
import Definitions.Def_OAI_Analysis_LipschitzFree_BlockObstruction
import Theorems.Thm_OAI_DiscreteFree_BlockParameters_bump_loss
import Theorems.Thm_OAI_DiscreteFree_GraphProducer_exists_rare_component
import Theorems.Thm_OAI_DiscreteFree_MetricBlock_edge_test
import Theorems.Thm_OAI_DiscreteFree_MetricBlock_transition_card
import Theorems.Thm_OAI_DiscreteFree_PortGraph_label_support_le
import Theorems.Thm_OAI_DiscreteFree_affineWeights_pairing
import Theorems.Thm_OAI_DiscreteFree_affine_bump_mass
import Theorems.Thm_OAI_DiscreteFree_affine_difference_bound
import Theorems.Thm_OAI_DiscreteFree_opposing_pairing_lower
import Theorems.Thm_OAI_DiscreteFree_signed_incidence_obstruction

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

theorem card_succ [Fintype D] (n : ℕ) :
    Fintype.card (BoundedWords D (n+1)) =
      1 + Fintype.card D * Fintype.card (BoundedWords D n) := by
  simpa using Fintype.card_congr (succEquiv (D := D) n)

theorem card_lt_pow [Fintype D] (hD : 2 ≤ Fintype.card D) (n : ℕ) :
    Fintype.card (BoundedWords D n) < Fintype.card D ^ (n+1) := by
  induction n with
  | zero => simpa using (show 1 < Fintype.card D from hD)
  | succ n ih =>
    rw [card_succ, pow_succ]
    have hi : Fintype.card (BoundedWords D n) + 1 ≤ Fintype.card D ^ (n+1) := ih
    nlinarith

end BoundedWords

namespace PortGraph
variable {X D : Type*} [Fintype D] (G : PortGraph X D)

end PortGraph
end DiscreteFree

end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.Parameters ----
namespace OAI

/-!
# Quantitative block parameters and strict variation bounds
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree.BlockParameters

theorem K_pos {p : ℕ} (hp : 1 ≤ p) : 0 < K p := by dsimp [K]; positivity

theorem small_radius {p : ℕ} (hp : 1 ≤ p) : 2*L p < R p := by dsimp [R]; have := L_pos hp; omega

theorem L_le_K (p : ℕ) : L p ≤ K p := by
  dsimp [L,K]
  have : 1 ≤ R p+1 := by omega
  exact Nat.le_mul_of_pos_right _ this

theorem compatibility_cap (p : ℕ) : K p+2*L p+1 < D p := by dsimp [D]; omega

theorem degree_ge (p : ℕ) : 4 ≤ degree p := by dsimp [degree,generators]; omega

theorem degree_variation (p : ℕ) : 20*V p < degree p := by dsimp [degree,generators]; omega

theorem Q_pos (p : ℕ) : 0 < Q p := by dsimp [Q]; exact pow_pos (by have := degree_ge p; omega) _

theorem H_pos (p : ℕ) : 0 < H p := by dsimp [H]; exact pow_pos (by have := degree_ge p; omega) _

theorem colors_large (p : ℕ) : 2*degree p*Q p*H p < colors p := by dsimp [colors]; omega

end DiscreteFree.BlockParameters

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

theorem cast_nat_dist (m n : ℕ) : (Nat.dist m n : ℝ) = |(m : ℝ) - n| := by
  unfold Nat.dist
  rcases le_total m n with h | h
  · have h' : (m : ℝ) ≤ n := by exact_mod_cast h
    rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h, abs_of_nonpos (sub_nonpos.mpr h')]
    ring
  · have h' : (n : ℝ) ≤ m := by exact_mod_cast h
    rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr h')]

theorem real_coord_le (a b : BoxLabel C cap) (i : C) :
    |((a i).val : ℝ) - (b i).val| ≤ dist a b := by
  rw [← cast_nat_dist, dist_eq]
  exact_mod_cast coord_le a b i

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

theorem dist_eq (u v : Point G color cap R) : dist u v =
    (NatMetricClosure.distance (weight G color cap R) u v : ℝ) := rfl

theorem weight_bound (u v : Point G color cap R) : weight G color cap R u v ≤ 4*R+cap := by
  have hR : 0 < R := Fact.out
  by_cases h : u = v
  · simp [h]
  · cases u <;> cases v <;> simp only [weight, ite_eq_right h]
    · split_ifs <;> omega
    · split_ifs <;> omega
    · split_ifs <;> omega
    · exact (Nat.add_le_add_left (BoxLabel.distance_bound _ _) _).trans (by omega)

theorem diameter_bound (u v : Point G color cap R) : dist u v ≤ (4*R+cap : ℕ) := by
  rw [dist_eq]
  exact_mod_cast (NatMetricClosure.distance_le _ u v).trans (weight_bound G color cap R u v)

theorem source_edge (x : X) (e : D) :
    dist (ofVertex G color cap R x) (ofVertex G color cap R (G.move x e)) ≤ 1 := by
  rw [dist_eq]
  unfold ofVertex
  have hn : NatMetricClosure.distance (weight G color cap R) (Sum.inl x) (Sum.inl (G.move x e)) ≤ 1 := by
    apply (NatMetricClosure.distance_le _ _ _).trans
    simp only [weight]
    split_ifs with h₁ h₂
    · exact Nat.zero_le _
    · exact le_rfl
    · exact False.elim (h₂ ⟨e, rfl⟩)
  exact_mod_cast hn

theorem attachment (x : X) :
    dist (ofVertex G color cap R x) (ofAnchor G color cap R (anchorOf G color cap x)) ≤ R := by
  rw [dist_eq]
  unfold ofVertex ofAnchor
  exact_mod_cast (NatMetricClosure.distance_le (weight G color cap R)
    (Sum.inl x) (Sum.inr (anchorOf G color cap x))).trans_eq (by simp [weight, anchorOf])

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

-- ---- from OAI.Analysis.LipschitzFree.Attachment ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Attachment-length estimates and label compatibility
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped Classical
namespace PortGraph
variable {X D : Type*} (G : PortGraph X D)
end PortGraph

namespace MetricBlock
variable {X D C : Type*} [Fintype C] (G : PortGraph X D) (color : X → C) (cap R : ℕ)

variable [Fintype D]

variable [Fact (0 < R)]

omit [Fact (0 < R)] [Fintype C] [Fintype D] in

theorem label_occurs (u : Point G color cap R) :
    ∃ x, label G color cap R u = originalLabel G color cap x := by
  cases u with
  | inl x => exact ⟨x, rfl⟩
  | inr a => exact a.property.imp (fun _ h => h.symm)

omit [Fact (0 < R)] in
theorem label_support_card (u : Point G color cap R) :
    Nat.card {i : C // (label G color cap R u i).val < cap} ≤
      Fintype.card (BoundedWords D cap) := by
  obtain ⟨x, hx⟩ := label_occurs G color cap R u
  rw [hx]
  exact G.label_support_le color cap x

omit [Fact (0 < R)] [Fintype D] in

theorem color_in_support (x : X) (u : Point G color cap R)
    (h : dist (originalLabel G color cap x) (label G color cap R u) < cap) :
    (label G color cap R u (color x)).val < cap := by
  have hc := BoxLabel.real_coord_le (originalLabel G color cap x) (label G color cap R u) (color x)
  simp only [originalLabel, G.label_own_color, Nat.cast_zero, zero_sub, abs_neg,
    Nat.abs_cast] at hc
  exact_mod_cast hc.trans_lt h

end MetricBlock
end DiscreteFree
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

theorem exceptional_unique {r : D → S → ℕ} {e f : D} {j : S}
    (he : Exceptional r e j) (hf : Exceptional r f j) : e = f := by
  by_contra h
  exact (Nat.lt_asymm (he f (Ne.symm h)) (hf e h))

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

-- ---- from OAI.Analysis.LipschitzFree.Coordinates ----
namespace OAI

/-!
# Signed evaluation coefficients and finite-support projections
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)

theorem dualPairing_bound (f : Lip0 o) (u : FreeSpace o) : |dualPairing o f u| ≤ ‖u‖ * ‖f‖ :=
  u.val.le_opNorm f

namespace Lip0
theorem center_norm_le (g : M → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hg : ∀ x y, |g x - g y| ≤ L * dist x y) : ‖center o g L hL hg‖ ≤ L := by
  apply (norm_le_iff _ hL).mpr
  intro x y
  simpa using hg x y
end Lip0

variable (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y)

end DiscreteFree
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.AffineWeights ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

/-!
# Affine signed coefficients and quantitative pairing bounds
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)
    (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y) (S : Finset M) (ho : o ∈ S)

theorem affineWeights_variation (u : FreeSpace o)
    (hu : supportProjection o sep S u = u) :
    totalVariation (affineWeights o sep S ho u) ≤ 1 + 2*‖u‖ := by
  let μ := affineWeights o sep S ho u
  let g : M → ℝ := fun x => if hx : x ∈ S then
    (if 0 ≤ μ ⟨x,hx⟩ then 1 else -1) else 0
  have hb (x : M) : -1 ≤ g x ∧ g x ≤ 1 := by
    dsimp [g]
    split_ifs <;> norm_num
  have hg (x y : M) : |g x - g y| ≤ 2 * dist x y := by
    convert bounded_test_lipschitz sep hb x y using 1; norm_num
  have hid : pairing μ (fun j : S => g j.val) = totalVariation μ := by
    unfold pairing totalVariation
    apply Finset.sum_congr rfl
    intro j _
    dsimp [g]
    rw [dite_eq_left j.property]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]
  have ha := affineWeights_pairing o sep S ho u hu g 2 (by norm_num) hg
  change pairing μ (fun j : S => g j.val) = _ at ha
  rw [hid] at ha
  have hn := Lip0.center_norm_le o g 2 (by norm_num) hg
  have hp := (dualPairing_bound o (Lip0.center o g 2 (by norm_num) hg) u).trans
    (mul_le_mul_of_nonneg_left hn (norm_nonneg u))
  have hle := (le_abs_self (dualPairing o (Lip0.center o g 2 (by norm_num) hg) u)).trans hp
  linarith [(hb o).2]

theorem affineWeights_operator_variation (T : FreeSpace o →L[ℝ] FreeSpace o)
    (hfixed : ∀ u, supportProjection o sep S (T u) = T u)
    (p B : ℝ) (hp : 0 ≤ p) (hn : ‖T‖ ≤ 2*p) (hb : ∀ x, dist x o ≤ B) (x : M) :
    totalVariation (affineWeights o sep S ho (T (delta o x))) ≤ 1 + 4*p*B := by
  have h := affineWeights_variation o sep S ho (T (delta o x)) (hfixed _)
  have hu : ‖T (delta o x)‖ ≤ (2*p)*B := by
    exact (T.le_opNorm _).trans (mul_le_mul hn (by simpa using hb x) (norm_nonneg _) (by positivity))
  nlinarith

end DiscreteFree
end

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)
    (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y) (S : Finset M) (ho : o ∈ S)

end DiscreteFree
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

omit [Fact (0 < R)] in
theorem supportColors_card (j : Point G color cap R) :
    (supportColors G color cap R j).card ≤ Fintype.card (BoundedWords E cap) := by
  have h := label_support_card G color cap R j
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, supportColors] using h

omit [Fintype E] [Fact (0 < R)] in
theorem compatible_color (hcap : K+2*L+1 < cap) (x : X) (j : Point G color cap R)
    (h : Compatible G color cap R L K x j) : color x ∈ supportColors G color cap R j := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, color_in_support G color cap R x j ?_⟩
  exact h.trans_lt (by exact_mod_cast hcap)

omit [Fintype E] in
theorem exceptional_unique_good (S : Finset (Point G color cap R)) (n : ℕ) (x : X)
    (hx : G.Good (fun x (j : S) => Compatible G color cap R L K x j.val)
      (fun j k : S => Transition G color cap R L j.val k.val) n x)
    (j : S) (e f : E) (he : j ∈ exceptionSet G color cap R L K S n x e)
    (hf : j ∈ exceptionSet G color cap R L K S n x f) : e = f := by
  exact exceptional_unique (he.resolve_left (not_not.mpr hx)) (hf.resolve_left (not_not.mpr hx))

end DiscreteFree.MetricBlock
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.BlockObstruction ----
namespace OAI

/-!
# Signed finite-rank obstruction on countable bounded metric blocks
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.BlockConstruction
open scoped Classical BigOperators
open BlockParameters

theorem attached_mem (p : ℕ) (x : Vertices p) :
    MetricBlock.ofAnchor (graph p) (color p) (D p) (R p)
      (MetricBlock.anchorOf (graph p) (color p) (D p) x) ∈ anchors p :=
  Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩

variable (p : ℕ) [Fact (0 < R p)]

theorem diameter (x y : Block p) : dist x y ≤ (B p : ℝ) :=
  MetricBlock.diameter_bound (graph p) (color p) (D p) (R p) x y

omit [Fact (0 < R p)] in
theorem support_colors_bound (j : Block p) :
    (MetricBlock.supportColors (graph p) (color p) (D p) (R p) j).card ≤ H p := by
  apply (MetricBlock.supportColors_card (graph p) (color p) (D p) (R p) j).trans
  have hd : 2 ≤ Fintype.card (Ports p) := by rw [card_ports]; have := degree_ge p; omega
  simpa only [card_ports,H] using (BoundedWords.card_lt_pow (D := Ports p) hd (D p)).le

theorem transition_bound (hp : 1 ≤ p) (S : Finset (Block p)) (j : S) :
    Fintype.card {k : S // MetricBlock.Transition (graph p) (color p) (D p) (R p) (L p) j.val k.val} ≤ Q p := by
  apply (MetricBlock.transition_card (graph p) (color p) (D p) (R p) (L p) (small_radius hp) S j).trans
  have hd : 2 ≤ Fintype.card (Ports p) := by rw [card_ports]; have := degree_ge p; omega
  simpa only [card_ports,Q] using (BoundedWords.card_lt_pow (D := Ports p) hd (2*L p)).le

theorem bump_mass (hp : 1 ≤ p) (S : Finset (Block p)) (ho : base p ∈ S)
    (T : FreeSpace (base p) →L[ℝ] FreeSpace (base p))
    (hn : ‖T‖ ≤ 2*(p : ℝ))
    (hfixed : ∀ u, supportProjection (base p) (separation p) S (T u) = T u)
    (he : ∀ a ∈ anchors p, ‖T (delta (base p) a) - delta (base p) a‖ < 1)
    (x : Vertices p) :
    3*(L p : ℝ)/4 ≤
      pairing (affineWeights (base p) (separation p) S ho
        (T (delta (base p) (MetricBlock.ofVertex (graph p) (color p) (D p) (R p) x))))
      (fun j : S => labelBump (MetricBlock.label (graph p) (color p) (D p) (R p))
        (MetricBlock.originalLabel (graph p) (color p) (D p) x) (L p) (K p) j.val) := by
  let vx := MetricBlock.ofVertex (graph p) (color p) (D p) (R p) x
  let ax := MetricBlock.ofAnchor (graph p) (color p) (D p) (R p)
    (MetricBlock.anchorOf (graph p) (color p) (D p) x)
  have hh := affine_bump_mass (base p) (separation p) S ho T hfixed
    (MetricBlock.label (graph p) (color p) (D p) (R p))
    (MetricBlock.label_lipschitz (graph p) (color p) (D p) (R p)) vx ax rfl
    (L p) (K p) p (R p) (Nat.cast_nonneg _) (by exact_mod_cast K_pos hp)
    (Nat.cast_nonneg _) hn (MetricBlock.attachment (graph p) (color p) (D p) (R p) x)
    (he ax (attached_mem p x))
  have hl := bump_loss hp
  change (L p : ℝ) - (L p : ℝ)/(K p : ℝ)*(2*(p : ℝ)*(R p : ℝ)+1) ≤
    pairing _ (fun j : S => labelBump (MetricBlock.label (graph p) (color p) (D p) (R p))
      (MetricBlock.originalLabel (graph p) (color p) (D p) x) (L p) (K p) j.val) at hh
  linarith

theorem finite_support_impossible (hp : 1 ≤ p) (S : Finset (Block p)) (ho : base p ∈ S)
    (T : FreeSpace (base p) →L[ℝ] FreeSpace (base p))
    (hn : ‖T‖ ≤ 2*(p : ℝ))
    (hfixed : ∀ u, supportProjection (base p) (separation p) S (T u) = T u)
    (he : ∀ a ∈ anchors p, ‖T (delta (base p) a) - delta (base p) a‖ < 1) : False := by
  let compatible : Vertices p → S → Prop := fun x j =>
    MetricBlock.Compatible (graph p) (color p) (D p) (R p) (L p) (K p) x j.val
  let trans : S → S → Prop := fun j k =>
    MetricBlock.Transition (graph p) (color p) (D p) (R p) (L p) j.val k.val
  let P : S → Finset (Colors p) := fun j =>
    MetricBlock.supportColors (graph p) (color p) (D p) (R p) j.val
  have hcolor : ∀ x j, compatible x j → color p x ∈ P j := by
    intro x j hj
    exact MetricBlock.compatible_color (graph p) (color p) (D p) (R p) (L p) (K p)
      (compatibility_cap p) x j.val hj
  obtain ⟨n,_,hnrare⟩ := GraphProducer.exists_rare_component (Generators p) (Colors p) S
    (Q p) (H p) (V p) (Q_pos p) (H_pos p) (by rw [nat_card_ports]; have := degree_ge p; omega)
    (by simpa only [nat_card_ports,nat_card_colors] using colors_large p)
    compatible trans P (fun j => support_colors_bound p j.val) hcolor (transition_bound p hp S)
  let X := (GraphProducer.Cayley (Generators p) n → Colors p) × GraphProducer.Cayley (Generators p) n
  let G := GraphProducer.allColoringsGraph (Generators p) (Colors p) n
  let i : X → Vertices p := GraphProducer.intoSequence (Generators p) (Colors p) n
  let v : X → Block p := fun x => MetricBlock.ofVertex (graph p) (color p) (D p) (R p) (i x)
  let μ : X → S → ℝ := fun x => affineWeights (base p) (separation p) S ho (T (delta (base p) (v x)))
  let E : X → Ports p → Set S := fun x e =>
    MetricBlock.exceptionSet (graph p) (color p) (D p) (R p) (L p) (K p) S n (i x) e
  let bad : Finset X := Finset.univ.filter (fun x => ¬ (graph p).Good compatible trans n (i x))
  have hbad : 20*(V p)*(bad.card) < Fintype.card X := by
    have hc : bad.card = Nat.card {x : X // ¬ (graph p).Good compatible trans n (i x)} := by
      rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
    rw [hc,← Nat.card_eq_fintype_card]
    exact hnrare
  have hrealV : (V p : ℝ) = 1+4*(p : ℝ)*(B p : ℝ) := by simp [V]
  have hTV (x : X) : totalVariation (μ x) ≤ (V p : ℝ) := by
    rw [hrealV]
    exact affineWeights_operator_variation (base p) (separation p) S ho T hfixed p (B p)
      (Nat.cast_nonneg _) hn (fun z => diameter p z (base p)) (v x)
  have hgood (x : X) (hx : x ∉ bad) (j : S) (e f : Ports p)
      (he : j ∈ E x e) (hf : j ∈ E x f) : e = f := by
    have hx' : (graph p).Good compatible trans n (i x) := by
      simpa only [bad,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hx
    exact MetricBlock.exceptional_unique_good (graph p) (color p) (D p) (R p) (L p) (K p)
      S n (i x) hx' j e f he hf
  apply signed_incidence_obstruction μ E bad G.incidenceReverse (p : ℝ) (V p : ℝ)
    (by exact_mod_cast (show 0 < p by omega)) (Nat.cast_nonneg _) hTV hgood
    (by rw [card_ports]; exact_mod_cast degree_variation p) (by exact_mod_cast hbad)
  rintro ⟨x,e⟩
  change 3*(10*(p : ℝ))/2 - 2*(10*(p : ℝ)) *
    (variationOn (μ x) (E x e) + variationOn (μ (G.move x e)) (E (G.move x e) (G.reverse e))) ≤ 2*(p : ℝ)
  obtain ⟨f,hf,hbound,hfx,hfy⟩ := MetricBlock.edge_test (graph p) (color p) (D p) (R p) (L p) (K p)
    (L_pos hp) (K_pos hp) (L_le_K p) S n (i x) e
  let b : S → ℝ := fun j => labelBump (MetricBlock.label (graph p) (color p) (D p) (R p))
    (MetricBlock.originalLabel (graph p) (color p) (D p) (i x)) (L p) (K p) j.val
  let c : S → ℝ := fun j => labelBump (MetricBlock.label (graph p) (color p) (D p) (R p))
    (MetricBlock.originalLabel (graph p) (color p) (D p) (i (G.move x e))) (L p) (K p) j.val
  have hb (j : S) : 0 ≤ b j ∧ b j ≤ (L p : ℝ) :=
    ⟨labelBump_nonneg _ _ (Nat.cast_nonneg _) _,labelBump_le _ _ (Nat.cast_nonneg _) (by exact_mod_cast K_pos hp) _⟩
  have hc (j : S) : 0 ≤ c j ∧ c j ≤ (L p : ℝ) :=
    ⟨labelBump_nonneg _ _ (Nat.cast_nonneg _) _,labelBump_le _ _ (Nat.cast_nonneg _) (by exact_mod_cast K_pos hp) _⟩
  have hlower := opposing_pairing_lower (μ x) (μ (G.move x e)) (fun j : S => f j.val) b c
    (E x e) (E (G.move x e) (G.reverse e)) (L p) (fun j => hbound j.val) hb hc hfx hfy
  have hxmass : 3*(L p : ℝ)/4 ≤ pairing (μ x) b := bump_mass p hp S ho T hn hfixed he (i x)
  have hymass : 3*(L p : ℝ)/4 ≤ pairing (μ (G.move x e)) c := bump_mass p hp S ho T hn hfixed he (i (G.move x e))
  have hdiff := affine_difference_bound (base p) (separation p) S ho T hfixed (2*(p : ℝ)) hn
    f hf (v x) (v (G.move x e))
  have hdist : dist (v x) (v (G.move x e)) ≤ 1 :=
    MetricBlock.source_edge (graph p) (color p) (D p) (R p) (i x) e
  have hupper : pairing (μ x) (fun j : S => f j.val) - pairing (μ (G.move x e)) (fun j : S => f j.val) ≤ 2*(p : ℝ) := by
    apply (le_abs_self _).trans (hdiff.trans _)
    simpa using mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ 2*(p : ℝ))
  have hL : (L p : ℝ) = 10*(p : ℝ) := by simp [L]
  rw [hL] at hxmass hymass hlower
  linarith

end DiscreteFree.BlockConstruction

namespace DiscreteFree

end DiscreteFree
end

end

end OAI

-- ---- platform node ----
open OAI OAI.DiscreteFree OAI.DiscreteFree.BlockConstruction
open scoped BigOperators ENNReal
open scoped Classical BigOperators
open BlockParameters


theorem solution : type_of% @_root_.OAI.DiscreteFree.BlockConstruction.finite_support_impossible := @_root_.OAI.DiscreteFree.BlockConstruction.finite_support_impossible
