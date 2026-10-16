-- Prove2me | solution 1 for OAI.DiscreteFree.real_l1_quantitative_renorming
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T12:40:44.768406+00:00
-- url     : https://prove2.me/submissions/42401664-629f-4939-9fdf-e1409c521c2a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/Renorming.lean:L41-L88
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.DiscreteFree.real_l1_quantitative_renorming.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_DiscreteFree_real_l1_quantitative_renorming) verbatim and is proved by it.
import Mathlib
import Definitions.Def_RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Model__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Coefficients
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Words__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_ScalarTests__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_FiniteQuotients__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphGirth__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_ColorCounting__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphColoring__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_BlockObstruction__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Functor__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_Wedge__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_RetainedWedge__RealL1Renorming
import Definitions.Def_OAI_Analysis_LipschitzFree_WedgeApproximation__RealL1Renorming

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

namespace Lip0
theorem center_norm_le (g : M → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hg : ∀ x y, |g x - g y| ≤ L * dist x y) : ‖center o g L hL hg‖ ≤ L := by
  apply (norm_le_iff _ hL).mpr
  intro x y
  simpa using hg x y
end Lip0

variable (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y)

theorem supportProjection_delta (F : Finset M) (x : M) :
    supportProjection o sep F (delta o x) = if x ∈ F then delta o x else 0 := by
  rw [supportProjection_apply]
  by_cases hx : x = o
  · subst x
    simp
  · simp only [coordinate_delta, ite_smul, one_smul, zero_smul]
    rw [sum_point_test]
    simp [hx]

theorem supportProjection_bound (F : Finset M) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, dist x o ≤ B) : ‖supportProjection o sep F‖ ≤ 2*B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [supportProjection_apply]
  calc
    ‖∑ j ∈ F, coordinate o sep j u • delta o j‖ ≤
        ∑ j ∈ F, ‖coordinate o sep j u • delta o j‖ := norm_sum_le _ _
    _ = ∑ j ∈ F, |coordinate o sep j u| * dist j o := by simp only [norm_smul, Real.norm_eq_abs, delta_norm]
    _ ≤ ∑ j ∈ F, |coordinate o sep j u| * B := by gcongr with j hj; exact hb j
    _ = (∑ j ∈ F, |coordinate o sep j u|) * B := (Finset.sum_mul ..).symm
    _ ≤ (2 * ‖u‖) * B := mul_le_mul_of_nonneg_right (sum_abs_coordinate_le o sep F u) hB
    _ = (2*B) * ‖u‖ := by ring

end DiscreteFree
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.Coefficients ----
namespace OAI

/-!
# Absolutely summable coefficients of bounded separated Lipschitz-free spaces
-/

noncomputable section
open scoped BigOperators ENNReal Classical

namespace DiscreteFree

namespace Coefficients

variable {ι M : Type*} [MetricSpace M] (o : M)
variable (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y)
variable (e : ι ≃ {x : M // x ≠ o})

variable (B : ℝ) (hb : ∀ x, dist x o ≤ B)
include hb

theorem equiv_bounds (c : L1 ι) :
    (1 / 2 : ℝ) * ‖c‖ ≤ ‖equiv o sep e B hb c‖ ∧
    ‖equiv o sep e B hb c‖ ≤ B * ‖c‖ := by
  constructor
  · have h := analysis_bound o sep e (synthesis o e B hb c)
    change ‖analysis o sep e (synthesis o e B hb c)‖ ≤
      2 * ‖synthesis o e B hb c‖ at h
    rw [analysis_synthesis] at h
    change (1 / 2 : ℝ) * ‖c‖ ≤ ‖synthesis o e B hb c‖
    linarith
  · exact synthesis_bound o e B hb c

end Coefficients

end DiscreteFree
end

end OAI

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

theorem walk_append (x : X) (u v : List D) :
    G.walk x (u ++ v) = G.walk (G.walk x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih _

theorem near_self (n : ℕ) (x : X) : G.Near n x x := ⟨[], by simp, rfl⟩

theorem near_mono {n m : ℕ} {x y : X} (hnm : n ≤ m) (h : G.Near n x y) :
    G.Near m x y := by
  obtain ⟨w, hw, rfl⟩ := h
  exact ⟨w, hw.trans hnm, rfl⟩

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

theorem near_finite (n : ℕ) (x : X) : {y : X | G.Near n x y}.Finite := by
  have h : {y : X | G.Near n x y} = Set.range
      (fun w : BoundedWords D n => G.walk x w.val) := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
    · rintro ⟨⟨w, hw⟩, rfl⟩
      exact ⟨w, hw, rfl⟩
  rw [h]
  exact Set.finite_range _

theorem label_support_le {C : Type*} [Fintype C] (color : X → C) (cap : ℕ)
    (x : X) : Nat.card {i : C // G.label color cap i x < cap} ≤
      Fintype.card (BoundedWords D cap) := by
  classical
  let f : {i : C // G.label color cap i x < cap} → BoundedWords D cap := fun i =>
    let w := (G.label_witness color cap i.val x i.property).choose
    ⟨w, by
      rw [(G.label_witness color cap i.val x i.property).choose_spec.1]
      exact G.label_le color cap i.val x⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    have hi := (G.label_witness color cap i.val x i.property).choose_spec.2
    have hj := (G.label_witness color cap j.val x j.property).choose_spec.2
    have he := congrArg (fun w : BoundedWords D cap => color (G.walk x w.val)) hij
    exact hi.symm.trans (he.trans hj)
  simpa only [Nat.card_eq_fintype_card] using Nat.card_le_card_of_injective f hf

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

theorem L_pos {p : ℕ} (hp : 1 ≤ p) : 0 < L p := by dsimp [L]; omega

theorem R_pos {p : ℕ} (hp : 1 ≤ p) : 0 < R p := by dsimp [R]; exact Nat.mul_pos (by omega) (L_pos hp)

theorem K_pos {p : ℕ} (hp : 1 ≤ p) : 0 < K p := by dsimp [K]; positivity

theorem small_radius {p : ℕ} (hp : 1 ≤ p) : 2*L p < R p := by dsimp [R]; have := L_pos hp; omega

theorem L_le_K (p : ℕ) : L p ≤ K p := by
  dsimp [L,K]
  have : 1 ≤ R p+1 := by omega
  exact Nat.le_mul_of_pos_right _ this

theorem compatibility_cap (p : ℕ) : K p+2*L p+1 < D p := by dsimp [D]; omega

theorem B_formula (p : ℕ) : (B p : ℝ) = blockBound p := by
  norm_num [B,D,K,R,L,blockBound]
  ring

theorem degree_ge (p : ℕ) : 4 ≤ degree p := by dsimp [degree,generators]; omega

theorem degree_variation (p : ℕ) : 20*V p < degree p := by dsimp [degree,generators]; omega

theorem Q_pos (p : ℕ) : 0 < Q p := by dsimp [Q]; exact pow_pos (by have := degree_ge p; omega) _

theorem H_pos (p : ℕ) : 0 < H p := by dsimp [H]; exact pow_pos (by have := degree_ge p; omega) _

theorem colors_large (p : ℕ) : 2*degree p*Q p*H p < colors p := by dsimp [colors]; omega

theorem bump_loss {p : ℕ} (hp : 1 ≤ p) :
    (L p : ℝ)/(K p : ℝ)*(2*(p : ℝ)*(R p : ℝ)+1) ≤ (L p : ℝ)/4 := by
  have hp' : 1 ≤ (p : ℝ) := by exact_mod_cast hp
  have hR : 0 ≤ (R p : ℝ) := Nat.cast_nonneg _
  have hpR : 0 ≤ (p : ℝ)*(R p : ℝ) := mul_nonneg (by positivity) hR
  have hK : 0 < (K p : ℝ) := by exact_mod_cast K_pos hp
  have hKn : (K p : ℝ) = 10*(p : ℝ)*((R p : ℝ)+1) := by simp [K]
  have hnum : 4*(2*(p : ℝ)*(R p : ℝ)+1) ≤ (K p : ℝ) := by rw [hKn]; nlinarith
  have hL : 0 ≤ (L p : ℝ) := Nat.cast_nonneg _
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_le_iff₀ hK).mpr
  nlinarith [mul_le_mul_of_nonneg_left hnum hL]

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

theorem path_relation (P : ℕ → X → X → Prop)
    (hedge : ∀ x y, P (w x y) x y)
    (htrans : ∀ a b x y z, P a x y → P b y z → P (a+b) x z)
    (x y : X) : P (distance w x y) x y := by
  have hcost (u : List X) (a : X) : P (cost w a y u) a y := by
    induction u generalizing a with
    | nil => exact hedge a y
    | cons b u ih => exact htrans _ _ _ _ _ (hedge a b) (ih b)
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
theorem near_trans {m n : ℕ} {x y z : X} (hxy : G.Near m x y) (hyz : G.Near n y z) :
    G.Near (m+n) x z := by
  obtain ⟨u, hu, rfl⟩ := hxy
  obtain ⟨v, hv, rfl⟩ := hyz
  exact ⟨u++v, by simpa only [List.length_append] using Nat.add_le_add hu hv, G.walk_append _ _ _⟩
end PortGraph

namespace MetricBlock
variable {X D C : Type*} [Fintype C] (G : PortGraph X D) (color : X → C) (cap R : ℕ)

omit [Fintype C] in
theorem short_self (n : ℕ) (u : Point G color cap R) : ShortRelation G color cap R n u u := by
  cases u with
  | inl x => exact G.near_self n x
  | inr a => rfl

omit [Fintype C] in
theorem short_trans {m n : ℕ} {u v w : Point G color cap R}
    (huv : ShortRelation G color cap R m u v) (hvw : ShortRelation G color cap R n v w) :
    ShortRelation G color cap R (m+n) u w := by
  cases u <;> cases v <;> cases w <;> simp only [ShortRelation] at *
  · exact G.near_trans huv hvw
  · exact huv.trans hvw

theorem short_edge (hR : 0 < R) (u v : Point G color cap R)
    (h : weight G color cap R u v < R) :
    ShortRelation G color cap R (weight G color cap R u v) u v := by
  by_cases he : u = v
  · subst v
    exact short_self G color cap R _ u
  · cases u with
    | inl x =>
      cases v with
      | inl y =>
        simp only [weight, ite_eq_right he] at h ⊢
        split_ifs at h ⊢ with ha
        · obtain ⟨e, rfl⟩ := ha
          exact ⟨[e], by simp, rfl⟩
        · omega
      | inr a =>
        simp only [weight, ite_eq_right he] at h
        split_ifs at h <;> omega
    | inr a =>
      cases v with
      | inl x =>
        simp only [weight, ite_eq_right he] at h
        split_ifs at h <;> omega
      | inr b =>
        simp only [weight, ite_eq_right he] at h
        omega

theorem short_distance (hR : 0 < R) (u v : Point G color cap R)
    (h : NatMetricClosure.distance (weight G color cap R) u v < R) :
    ShortRelation G color cap R (NatMetricClosure.distance (weight G color cap R) u v) u v := by
  have hp := NatMetricClosure.path_relation (weight G color cap R)
    (fun n x y => n < R → ShortRelation G color cap R n x y)
    (fun x y => short_edge G color cap R hR x y)
    (by
      intro a b x y z hxy hyz hab
      exact short_trans G color cap R (hxy (by omega)) (hyz (by omega))) u v
  exact hp h

omit [Fintype C] in
theorem short_mono {m n : ℕ} (hmn : m ≤ n) {u v : Point G color cap R}
    (h : ShortRelation G color cap R m u v) : ShortRelation G color cap R n u v := by
  cases u <;> cases v <;> simp only [ShortRelation] at *
  · exact G.near_mono hmn h
  · exact h

variable [Fintype D]

omit [Fintype C] in
theorem short_finite (n : ℕ) (u : Point G color cap R) :
    {v | ShortRelation G color cap R n u v}.Finite := by
  cases u with
  | inl x =>
    apply ((G.near_finite n x).image (Sum.inl : X → Point G color cap R)).subset
    rintro (y|a) hy
    · exact ⟨y, hy, rfl⟩
    · exact False.elim hy
  | inr a =>
    apply (Set.finite_singleton (Sum.inr a : Point G color cap R)).subset
    rintro (x|b) hb
    · exact False.elim hb
    · exact Set.mem_singleton_iff.mpr (congrArg Sum.inr hb.symm)

omit [Fintype C] in
theorem short_card_le (n : ℕ) (u : Point G color cap R) :
    Nat.card {v : Point G color cap R // ShortRelation G color cap R n u v} ≤
      Fintype.card (BoundedWords D n) := by
  cases u with
  | inl x =>
    let f : BoundedWords D n → {v : Point G color cap R // ShortRelation G color cap R n (Sum.inl x) v} :=
      fun w => ⟨Sum.inl (G.walk x w.val), w.val, w.property, rfl⟩
    have hf : Function.Surjective f := by
      rintro ⟨(_|a), h⟩
      · obtain ⟨w, hw, rfl⟩ := h
        exact ⟨⟨w, hw⟩, rfl⟩
      · exact False.elim h
    simpa only [Nat.card_eq_fintype_card] using Nat.card_le_card_of_surjective f hf
  | inr a =>
    let f : BoundedWords D n → {v : Point G color cap R // ShortRelation G color cap R n (Sum.inr a) v} :=
      fun _ => ⟨Sum.inr a, rfl⟩
    have hf : Function.Surjective f := by
      rintro ⟨(x|b), h⟩
      · exact False.elim h
      · change a = b at h
        subst b
        exact ⟨⟨[], by simp⟩, rfl⟩
    simpa only [Nat.card_eq_fintype_card] using Nat.card_le_card_of_surjective f hf

variable [Fact (0 < R)]

theorem closedBall_finite (n : ℕ) (hn : n < R) (u : Point G color cap R) :
    (Metric.closedBall u (n : ℝ)).Finite := by
  apply (short_finite G color cap R n u).subset
  intro v hv
  have hv' : NatMetricClosure.distance (weight G color cap R) u v ≤ n := by
    have hv' := Metric.mem_closedBall.mp hv
    rw [dist_comm, dist_eq] at hv'
    exact_mod_cast hv'
  exact short_mono G color cap R hv' (short_distance G color cap R Fact.out u v (hv'.trans_lt hn))

theorem closedBall_card_le (n : ℕ) (hn : n < R) (u : Point G color cap R) :
    Nat.card (Metric.closedBall u (n : ℝ)) ≤ Fintype.card (BoundedWords D n) := by
  let f : Metric.closedBall u (n : ℝ) → {v : Point G color cap R // ShortRelation G color cap R n u v} :=
    fun v => ⟨v.val, by
      have hv : NatMetricClosure.distance (weight G color cap R) u v.val ≤ n := by
        have hv' := Metric.mem_closedBall.mp v.property
        rw [dist_comm, dist_eq] at hv'
        exact_mod_cast hv'
      exact short_mono G color cap R hv (short_distance G color cap R Fact.out u v.val (hv.trans_lt hn))⟩
  have : Finite {v : Point G color cap R // ShortRelation G color cap R n u v} :=
    (short_finite G color cap R n u).to_subtype
  exact (Nat.card_le_card_of_injective f (by intro v w h; exact Subtype.ext (congrArg (fun z => z.val) h))).trans
    (short_card_le G color cap R n u)

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

-- ---- from OAI.Analysis.LipschitzFree.StatePaths ----
namespace OAI

/-!
# Counting finite-state paths with bounded transitions
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section

namespace DiscreteFree.StatePaths
open scoped BigOperators Classical

universe u
variable {S : Type u} (r : S → S → Prop)

theorem card_based_le [Fintype S] (Q : ℕ)
    (hQ : ∀ j, Fintype.card {k : S // r j k} ≤ Q) (j : S) (n : ℕ) :
    Fintype.card (Based r j n) ≤ Q ^ n := by
  induction n generalizing j with
  | zero =>
    change Fintype.card PUnit ≤ 1
    exact Fintype.card_unique.le
  | succ n ih =>
    change Fintype.card (Σ k : {k : S // r j k}, Based r k.val n) ≤ _
    rw [Fintype.card_sigma]
    calc
      (∑ k : {k : S // r j k}, Fintype.card (Based r k.val n)) ≤
          ∑ _k : {k : S // r j k}, Q ^ n := Finset.sum_le_sum (fun k _ => ih k.val)
      _ = Fintype.card {k : S // r j k} * Q ^ n := by simp
      _ ≤ Q * Q ^ n := Nat.mul_le_mul_right _ (hQ j)
      _ = Q ^ (n+1) := (pow_succ' _ _).symm

theorem card_path_le [Fintype S] (Q : ℕ)
    (hQ : ∀ j, Fintype.card {k : S // r j k} ≤ Q) (n : ℕ) :
    Fintype.card (Path r n) ≤ Fintype.card S * Q ^ n := by
  change Fintype.card (Σ j : S, Based r j n) ≤ _
  rw [Fintype.card_sigma]
  simpa using Finset.sum_le_sum (s := (Finset.univ : Finset S))
    (fun j _ => card_based_le r Q hQ j n)

end DiscreteFree.StatePaths

end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.SignedTests ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
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

theorem pairing_error_le (μ f b : S → ℝ) (E : Set S) (C : ℝ)
    (heq : ∀ j, j ∉ E → f j = b j)
    (hbound : ∀ j, |f j - b j| ≤ C) :
    |pairing μ f - pairing μ b| ≤ C * variationOn μ E := by
  classical
  unfold pairing variationOn
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  calc
    |∑ j, (μ j * f j - μ j * b j)| ≤
        ∑ j, |μ j * f j - μ j * b j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, C * (if j ∈ E then |μ j| else 0) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j ∈ E
      · rw [ite_eq_left hj, ← mul_sub, abs_mul, mul_comm C]
        exact mul_le_mul_of_nonneg_left (hbound j) (abs_nonneg _)
      · simp [hj, heq j hj]

theorem opposing_pairing_lower (μ ν f b c : S → ℝ) (E F : Set S) (L : ℝ)
    (hf : ∀ j, |f j| ≤ L)
    (hb : ∀ j, 0 ≤ b j ∧ b j ≤ L) (hc : ∀ j, 0 ≤ c j ∧ c j ≤ L)
    (he : ∀ j, j ∉ E → f j = b j)
    (hF : ∀ j, j ∉ F → f j = -c j) :
    pairing μ b + pairing ν c - 2 * L * (variationOn μ E + variationOn ν F) ≤
      pairing μ f - pairing ν f := by
  have h₁ := pairing_error_le μ f b E (2 * L) he (fun j => by
    have := abs_sub (f j) (b j)
    rw [abs_of_nonneg (hb j).1] at this
    linarith [hf j, (hb j).2])
  have h₂ := pairing_error_le ν f (fun j => -c j) F (2 * L) hF
    (fun j => by
      have := abs_sub (f j) (-c j)
      rw [abs_neg, abs_of_nonneg (hc j).1] at this
      linarith [hf j, (hc j).2])
  have hneg : pairing ν (fun j => -c j) = -pairing ν c := by
    simp [pairing, Finset.sum_neg_distrib]
  rw [hneg] at h₂
  have h₁' := (abs_le.mp h₁).1
  have h₂' := (abs_le.mp h₂).2
  nlinarith

end SignedTests
section

variable {N : Type*} [MetricSpace N]

theorem bounded_scalar_extension (P : Set N) (v : N → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hv : LipschitzOnWith 1 v P) (hvb : ∀ j ∈ P, |v j| ≤ L) :
    ∃ f : N → ℝ, LipschitzWith 1 f ∧ (∀ z, |f z| ≤ L) ∧ Set.EqOn f v P := by
  obtain ⟨F, hF, hFV⟩ := hv.extend_real
  refine ⟨fun z => max (-L) (min L (F z)), ?_, ?_, ?_⟩
  · exact (hF.const_min L).const_max (-L)
  · intro z
    apply abs_le.mpr
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  · intro z hz
    change max (-L) (min L (F z)) = v z
    rw [← hFV hz]
    obtain ⟨hl, hu⟩ := abs_le.mp (hvb z hz)
    rw [min_eq_right hu, max_eq_right hl]

theorem opposing_scalar_extension (P Q : Set N) (b c : N → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hbLip : LipschitzWith 1 b) (hcLip : LipschitzWith 1 c)
    (hb : ∀ j, 0 ≤ b j ∧ b j ≤ L) (hc : ∀ j, 0 ≤ c j ∧ c j ≤ L)
    (hcross : ∀ j ∈ P, ∀ k ∈ Q, dist j k < 2 * L → b j = 0 ∧ c k = 0) :
    ∃ f : N → ℝ, LipschitzWith 1 f ∧ (∀ z, |f z| ≤ L) ∧
      Set.EqOn f b P ∧ Set.EqOn f (fun z => -c z) Q := by
  classical
  have hzero : ∀ j ∈ P ∩ Q, b j = 0 ∧ c j = 0 := by
    intro j hj
    by_cases hpos : 0 < L
    · exact hcross j hj.1 j hj.2 (by simp; linarith)
    · have hz : L = 0 := le_antisymm (le_of_not_gt hpos) hL
      constructor <;> linarith [(hb j).1, (hb j).2, (hc j).1, (hc j).2]
  let v : N → ℝ := fun j => if j ∈ P then b j else -c j
  have hvP : Set.EqOn v b P := fun j hj => ite_eq_left hj
  have hvQ : Set.EqOn v (fun z => -c z) Q := by
    intro j hj
    by_cases hp : j ∈ P
    · have hz := hzero j ⟨hp, hj⟩
      simp [v, hp, hz.1, hz.2]
    · exact ite_eq_right hp
  have hcross' : ∀ j ∈ P, ∀ k ∈ Q, |b j - -c k| ≤ dist j k := by
    intro j hj k hk
    by_cases hd : dist j k < 2 * L
    · obtain ⟨hz, hz'⟩ := hcross j hj k hk hd
      simp [hz, hz', dist_nonneg]
    · rw [sub_neg_eq_add, abs_of_nonneg (add_nonneg (hb j).1 (hc k).1)]
      linarith [(hb j).2, (hc k).2, le_of_not_gt hd]
  have hvLip : LipschitzOnWith 1 v (P ∪ Q) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro j hj k hk
    simp only [NNReal.coe_one, one_mul, Real.dist_eq]
    rcases hj with hj | hj <;> rcases hk with hk | hk
    · rw [hvP hj, hvP hk]
      simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using hbLip.dist_le_mul j k
    · rw [hvP hj, hvQ hk]
      exact hcross' j hj k hk
    · rw [hvQ hj, hvP hk, abs_sub_comm, dist_comm]
      exact hcross' k hk j hj
    · rw [hvQ hj, hvQ hk]
      have := hcLip.dist_le_mul j k
      simpa only [NNReal.coe_one, one_mul, Real.dist_eq, neg_sub_neg, abs_sub_comm] using this
  have hvBound : ∀ j ∈ P ∪ Q, |v j| ≤ L := by
    intro j hj
    rcases hj with hj | hj
    · rw [hvP hj, abs_of_nonneg (hb j).1]
      exact (hb j).2
    · rw [hvQ hj, abs_neg, abs_of_nonneg (hc j).1]
      exact (hc j).2
  obtain ⟨f, hf, hfB, hfv⟩ := bounded_scalar_extension (P ∪ Q) v L hL hvLip hvBound
  exact ⟨f, hf, hfB, fun j hj => (hfv (Or.inl hj)).trans (hvP hj),
    fun j hj => (hfv (Or.inr hj)).trans (hvQ hj)⟩

end

variable {X D S : Type*} [Fintype X] [Fintype D] [Fintype S]

theorem sum_variationOn_le (μ : S → ℝ) (E : D → Set S)
    (hunique : ∀ j e f, j ∈ E e → j ∈ E f → e = f) :
    (∑ e, variationOn μ (E e)) ≤ totalVariation μ := by
  classical
  unfold variationOn totalVariation
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : ∃ e, j ∈ E e
  · obtain ⟨e, he⟩ := hj
    rw [Finset.sum_eq_single e]
    · simp only [ite_eq_left he, le_refl]
    · intro f _ hfe
      exact ite_eq_right (fun hf => hfe (hunique j f e hf he))
    · simp
  · have hnone : ∀ e, j ∉ E e := by simpa using hj
    simp only [ite_eq_right (hnone _), Finset.sum_const_zero]
    exact abs_nonneg _

theorem variationOn_le (μ : S → ℝ) (E : Set S) : variationOn μ E ≤ totalVariation μ := by
  classical
  unfold variationOn totalVariation
  apply Finset.sum_le_sum
  intro j _
  split_ifs <;> simp [abs_nonneg]

theorem signed_incidence_obstruction [Nonempty X] [Nonempty D]
    (μ : X → S → ℝ) (E : X → D → Set S) (bad : Finset X)
    (rev : (X × D) ≃ (X × D)) (p V : ℝ)
    (hp : 0 < p) (hV : 0 ≤ V)
    (hTV : ∀ x, totalVariation (μ x) ≤ V)
    (hgood : ∀ x, x ∉ bad → ∀ j e f, j ∈ E x e → j ∈ E x f → e = f)
    (hdegree : 20 * V < (Fintype.card D : ℝ))
    (hbad : 20 * V * (bad.card : ℝ) < (Fintype.card X : ℝ))
    (hedge : ∀ e : X × D,
      3 * (10 * p) / 2 - 2 * (10 * p) *
        (variationOn (μ e.1) (E e.1 e.2) +
         variationOn (μ (rev e).1) (E (rev e).1 (rev e).2)) ≤ 2 * p) : False := by
  classical
  let err : X × D → ℝ := fun e => variationOn (μ e.1) (E e.1 e.2)
  let a : ℝ := Fintype.card X
  let d : ℝ := Fintype.card D
  let b : ℝ := bad.card
  have ha : 0 < a := by dsimp [a]; exact_mod_cast Fintype.card_pos (α := X)
  have hd : 0 < d := by dsimp [d]; exact_mod_cast Fintype.card_pos (α := D)
  have hb : 0 ≤ b := by positivity
  have hvtx : ∀ x, (∑ e, err (x, e)) ≤ V + if x ∈ bad then d * V else 0 := by
    intro x
    by_cases hx : x ∈ bad
    · simp only [ite_eq_left hx]
      have hsum : (∑ e, err (x, e)) ≤ d * V := by
        calc
          _ ≤ ∑ _e : D, V := Finset.sum_le_sum (fun e _ =>
            (variationOn_le (μ x) (E x e)).trans (hTV x))
          _ = _ := by simp [d]
      linarith
    · simp only [ite_eq_right hx, add_zero]
      exact (sum_variationOn_le (μ x) (E x) (hgood x hx)).trans (hTV x)
  have hsum : (∑ e, err e) ≤ a * V + b * (d * V) := by
    calc
      _ = ∑ x, ∑ e, err (x, e) := Fintype.sum_prod_type _
      _ ≤ ∑ x, (V + if x ∈ bad then d * V else 0) :=
        Finset.sum_le_sum (fun x _ => hvtx x)
      _ = _ := by simp [Finset.sum_add_distrib, a, b]
  have hsmall : 10 * (∑ e, err e) < a * d := by
    have hd' : 20 * V < d := hdegree
    have hb' : 20 * V * b < a := hbad
    have h₁ := mul_lt_mul_of_pos_left hd' ha
    have h₂ := mul_lt_mul_of_pos_left hb' hd
    nlinarith
  have hreverse : (∑ e, err (rev e)) = ∑ e, err e := Equiv.sum_comp rev err
  have hsumedge := Finset.sum_le_sum (s := (Finset.univ : Finset (X × D)))
    (fun e _ => hedge e)
  change (∑ e, (3 * (10 * p) / 2 - 2 * (10 * p) *
      (err e + err (rev e)))) ≤ ∑ _e : X × D, 2 * p at hsumedge
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum] at hsumedge
  rw [hreverse] at hsumedge
  have hcard : (Fintype.card (X × D) : ℝ) = a * d := by simp [a, d]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard] at hsumedge
  have hap : 0 < a * d := mul_pos ha hd
  have h₃ := mul_lt_mul_of_pos_left hsmall hp
  nlinarith

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

theorem Matched.exists_based {x : X} {j : S} {w : List D}
    (h : G.Matched compatible trans x j w) :
    ∃ p : StatePaths.Based trans j w.length, ∀ i : Fin (w.length+1),
      compatible (G.walk x (w.take i.val)) (StatePaths.vertex trans j p i) := by
  induction w generalizing x j with
  | nil =>
    refine ⟨PUnit.unit, fun i => ?_⟩
    simpa [StatePaths.vertex, PortGraph.Matched] using h
  | cons e w ih =>
    obtain ⟨hc, k, hk, hm⟩ := h
    obtain ⟨p, hp⟩ := ih hm
    refine ⟨⟨⟨k, hk⟩, p⟩, fun i => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · change compatible x j
      exact hc
    · change compatible (G.walk (G.move x e) (w.take i.val)) (StatePaths.vertex trans k p i)
      exact hp i

end DiscreteFree.PortGraph
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.CompactApproximation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Compact-uniform approximation on bounded separated spaces
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)

theorem evaluation_span_dense : Dense (Submodule.span ℝ (Set.range (delta o)) : Set (FreeSpace o)) := by
  let S := Submodule.span ℝ (Set.range (delta o))
  have hu : ∀ u : FreeSpace o, u ∈ S.topologicalClosure :=
    freeSpace_induction (fun u => u ∈ S.topologicalClosure)
      (Submodule.isClosed_topologicalClosure S) S.topologicalClosure.zero_mem
      (fun _ _ => S.topologicalClosure.add_mem)
      (fun c _ h => S.topologicalClosure.smul_mem c h)
      (fun x => Submodule.le_topologicalClosure S (Submodule.subset_span ⟨x, rfl⟩))
  intro u
  exact hu u

variable (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y)

theorem supportProjection_range (F : Finset M) :
    LinearMap.range (supportProjection o sep F).toLinearMap ≤
      Submodule.span ℝ ((delta o) '' (F : Set M)) := by
  rintro u ⟨v, rfl⟩
  change supportProjection o sep F v ∈ _
  rw [supportProjection_apply]
  exact Submodule.sum_mem _ (fun j hj => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨j, hj, rfl⟩))

theorem supportProjection_finiteRank (F : Finset M) :
    Module.Finite ℝ (LinearMap.range (supportProjection o sep F).toLinearMap) :=
  (Submodule.fg_iff_finiteDimensional _).mp
    ((Submodule.fg_span (F.finite_toSet.image (delta o))).of_le (supportProjection_range o sep F))

theorem span_eventually_fixed {u : FreeSpace o}
    (hu : u ∈ Submodule.span ℝ (Set.range (delta o))) :
    ∃ F : Finset M, ∀ G : Finset M, F ⊆ G → supportProjection o sep G u = u := by
  induction hu using Submodule.span_induction with
  | mem u h =>
    obtain ⟨x, rfl⟩ := h
    refine ⟨{x}, fun G hG => ?_⟩
    rw [supportProjection_delta, ite_eq_left (hG (Finset.mem_singleton_self _))]
  | zero => exact ⟨∅, fun _ _ => map_zero _⟩
  | add u v hu hv ihu ihv =>
    obtain ⟨F, hF⟩ := ihu
    obtain ⟨G, hG⟩ := ihv
    refine ⟨F ∪ G, fun K hK => ?_⟩
    rw [map_add, hF K (Finset.Subset.trans Finset.subset_union_left hK),
      hG K (Finset.Subset.trans Finset.subset_union_right hK)]
  | smul c u hu ih =>
    obtain ⟨F, hF⟩ := ih
    exact ⟨F, fun G hG => by rw [map_smul, hF G hG]⟩

variable (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x, dist x o ≤ B)

include hB hb in
theorem projection_error_bound (F : Finset M) (u : FreeSpace o) :
    ‖supportProjection o sep F u - u‖ ≤ (2*B+1)*‖u‖ := by
  calc
    _ ≤ ‖supportProjection o sep F u‖ + ‖u‖ := norm_sub_le _ _
    _ ≤ (2*B)*‖u‖ + ‖u‖ := add_le_add
      ((supportProjection o sep F).le_opNorm u |>.trans
        (mul_le_mul_of_nonneg_right (supportProjection_bound o sep F B hB hb) (norm_nonneg u))) le_rfl
    _ = _ := by ring

include hB hb in

theorem projection_pointwise (u : FreeSpace o) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset M, ∀ G : Finset M, F ⊆ G → ‖supportProjection o sep G u - u‖ < ε := by
  have hK : 0 < 2*B+1 := by positivity
  obtain ⟨v, hv, huv⟩ := Metric.mem_closure_iff.mp (evaluation_span_dense o u) _ (div_pos hε hK)
  obtain ⟨F, hF⟩ := span_eventually_fixed o sep hv
  refine ⟨F, fun G hG => ?_⟩
  calc
    ‖supportProjection o sep G u - u‖ =
        ‖supportProjection o sep G (u-v) - (u-v)‖ := by rw [map_sub, hF G hG]; congr 1; abel
    _ ≤ (2*B+1)*‖u-v‖ := projection_error_bound o sep B hB hb G (u-v)
    _ < ε := by
      rw [dist_eq_norm] at huv
      exact (lt_div_iff₀' hK).mp huv

include hB hb in

theorem projection_compact (C : Set (FreeSpace o)) (hC : IsCompact C) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset M, ∀ G : Finset M, F ⊆ G → ∀ u ∈ C,
      ‖supportProjection o sep G u - u‖ < ε := by
  have hK : 0 < 2*B+1 := by positivity
  obtain ⟨t, _, ht, hcover⟩ := hC.finite_cover_balls (e := ε/(2*(2*B+1))) (by positivity)
  choose F hF using (fun z : FreeSpace o => projection_pointwise o sep B hB hb z (ε/2) (by positivity))
  refine ⟨ht.toFinset.biUnion F, fun G hG u hu => ?_⟩
  obtain ⟨z, hz, huz⟩ := Set.mem_iUnion₂.mp (hcover hu)
  have hzF : F z ⊆ G := (Finset.subset_biUnion_of_mem F (ht.mem_toFinset.mpr hz)).trans hG
  have hze := hF z G hzF
  have huz' : ‖u-z‖ < ε/(2*(2*B+1)) := by simpa only [Metric.mem_ball, dist_eq_norm] using huz
  have hsmall : (2*B+1)*‖u-z‖ < ε/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2*(2*B+1))).mp huz'
    nlinarith
  calc
    ‖supportProjection o sep G u - u‖ =
      ‖(supportProjection o sep G (u-z) - (u-z)) + (supportProjection o sep G z - z)‖ := by
        rw [map_sub]; congr 1; abel
    _ ≤ ‖supportProjection o sep G (u-z) - (u-z)‖ + ‖supportProjection o sep G z - z‖ := norm_add_le _ _
    _ ≤ (2*B+1)*‖u-z‖ + ‖supportProjection o sep G z - z‖ :=
      add_le_add (projection_error_bound o sep B hB hb G (u-z)) le_rfl
    _ < ε := by linarith

include sep hB hb in

theorem bounded_separated_hasBAP : HasBAP (FreeSpace o) (2*B) := by
  intro C hC ε hε
  obtain ⟨F, hF⟩ := projection_compact o sep B hB hb C hC (ε/2) (by positivity)
  exact ⟨supportProjection o sep F, supportProjection_finiteRank o sep F,
    supportProjection_bound o sep F B hB hb, ε/2, by linarith,
    fun u hu => (hF F le_rfl u hu).le⟩

end DiscreteFree
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.SupportReduction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Finite-rank operators admit finite-support perturbations
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)
    (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y)

theorem projection_span_fixed (F : Finset M) {u : FreeSpace o}
    (hu : u ∈ Submodule.span ℝ ((delta o) '' (F : Set M))) :
    supportProjection o sep F u = u := by
  induction hu using Submodule.span_induction with
  | mem u h =>
    obtain ⟨x, hx, rfl⟩ := h
    rw [supportProjection_delta, ite_eq_left (show x ∈ F from hx)]
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy]
  | smul c x hx ih => rw [map_smul, ih]

theorem projection_idempotent (F : Finset M) (u : FreeSpace o) :
    supportProjection o sep F (supportProjection o sep F u) = supportProjection o sep F u :=
  projection_span_fixed o sep F (supportProjection_range o sep F ⟨u, rfl⟩)

theorem projection_comp_finiteRank (F : Finset M) (T : FreeSpace o →L[ℝ] FreeSpace o) :
    Module.Finite ℝ (LinearMap.range ((supportProjection o sep F).comp T).toLinearMap) := by
  have := supportProjection_finiteRank o sep F
  exact Module.Finite.of_injective
    (Submodule.inclusion (LinearMap.range_comp_le_range T.toLinearMap (supportProjection o sep F).toLinearMap))
    (Submodule.inclusion_injective _)

theorem projection_finiteRank_approx (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x, dist x o ≤ B)
    (T : FreeSpace o →L[ℝ] FreeSpace o)
    (hT : Module.Finite ℝ (LinearMap.range T.toLinearMap)) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset M, ∀ G : Finset M, F ⊆ G → ‖(supportProjection o sep G).comp T - T‖ < ε := by
  let Y := LinearMap.range T.toLinearMap
  let J : Y →L[ℝ] FreeSpace o := Y.subtypeL
  let C : Set (FreeSpace o) := J '' Metric.closedBall (0 : Y) ‖T‖
  have hC : IsCompact C := (isCompact_closedBall (0 : Y) ‖T‖).image J.continuous
  obtain ⟨F, hF⟩ := projection_compact o sep B hB hb C hC (ε/2) (by positivity)
  refine ⟨F, fun G hG => ?_⟩
  have hnorm : ‖(supportProjection o sep G).comp T - T‖ ≤ ε/2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro u hu
    have hTu : T u ∈ C := by
      refine ⟨⟨T u, ⟨u, rfl⟩⟩, ?_, rfl⟩
      change dist (T u) 0 ≤ ‖T‖
      simpa only [dist_zero_right, hu, mul_one] using T.le_opNorm u
    exact (hF G hG (T u) hTu).le
  linarith

theorem finite_support_reduction (B p : ℝ) (hB : 0 ≤ B) (hp : 1 ≤ p)
    (hb : ∀ x, dist x o ≤ B) (A : Finset M)
    (T₀ : FreeSpace o →L[ℝ] FreeSpace o)
    (hfinite : Module.Finite ℝ (LinearMap.range T₀.toLinearMap)) (hnorm : ‖T₀‖ ≤ p)
    (hanchor : ∀ a ∈ A, ‖T₀ (delta o a) - delta o a‖ < 1/2) :
    ∃ (S : Finset M) (T : FreeSpace o →L[ℝ] FreeSpace o), o ∈ S ∧
      Module.Finite ℝ (LinearMap.range T.toLinearMap) ∧ ‖T‖ ≤ 2*p ∧
      (∀ u, supportProjection o sep S (T u) = T u) ∧
      ∀ a ∈ A, ‖T (delta o a) - delta o a‖ < 1 := by
  let ε := min p (1/(2*(B+1)))
  have hε : 0 < ε := lt_min (by linarith) (by positivity)
  obtain ⟨F, hF⟩ := projection_finiteRank_approx o sep B hB hb T₀ hfinite ε hε
  let S := insert o F
  let T := (supportProjection o sep S).comp T₀
  have hdiff : ‖T-T₀‖ < ε := hF S (Finset.subset_insert _ _)
  have hn : ‖T‖ ≤ 2*p := by
    have hs := norm_add_le (T-T₀) T₀
    rw [sub_add_cancel] at hs
    have hεp : ε ≤ p := min_le_left _ _
    linarith
  refine ⟨S, T, Finset.mem_insert_self _ _, projection_comp_finiteRank o sep S T₀,
    hn, fun u => projection_idempotent o sep S (T₀ u), fun a ha => ?_⟩
  have hda := delta_norm o a
  have he : ‖(T-T₀) (delta o a)‖ ≤ ε*B := by
    calc
      _ ≤ ‖T-T₀‖ * ‖delta o a‖ := (T-T₀).le_opNorm _
      _ ≤ ε * B := mul_le_mul hdiff.le (by simpa using hb a) (norm_nonneg _) hε.le
  have hfrac : ε*B < 1/2 := by
    have hh : ε ≤ 1/(2*(B+1)) := min_le_right _ _
    have hden : 0 < 2*(B+1) := by positivity
    have hmul := (le_div_iff₀ hden).mp hh
    nlinarith
  calc
    ‖T (delta o a) - delta o a‖ =
      ‖(T-T₀) (delta o a) + (T₀ (delta o a) - delta o a)‖ := by
        simp only [sub_apply]; congr 1; abel
    _ ≤ ‖(T-T₀) (delta o a)‖ + ‖T₀ (delta o a) - delta o a‖ := norm_add_le _ _
    _ < 1 := by linarith [hanchor a ha]

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

theorem affineWeights_pairing (u : FreeSpace o)
    (hu : supportProjection o sep S u = u) (g : M → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ x y, |g x - g y| ≤ C * dist x y) :
    pairing (affineWeights o sep S ho u) (fun j : S => g j.val) =
      dualPairing o (Lip0.center o g C hC hg) u + g o := by
  have he : dualPairing o (Lip0.center o g C hC hg) u =
      ∑ j : S, coordinate o sep j.val u * (g j.val - g o) := by
    conv_lhs => rw [← hu]
    rw [supportProjection_apply]
    simp only [map_sum, map_smul, dualPairing_delta, Lip0.center_apply, smul_eq_mul]
    exact (Finset.sum_coe_sort S _).symm
  rw [he]
  simp only [pairing, affineWeights, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

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

theorem affine_difference_bound (T : FreeSpace o →L[ℝ] FreeSpace o)
    (hfixed : ∀ u, supportProjection o sep S (T u) = T u)
    (c : ℝ) (hn : ‖T‖ ≤ c)
    (g : M → ℝ) (hg : LipschitzWith 1 g) (x y : M) :
    |pairing (affineWeights o sep S ho (T (delta o x))) (fun j : S => g j.val) -
      pairing (affineWeights o sep S ho (T (delta o y))) (fun j : S => g j.val)| ≤
        c * dist x y := by
  have hgl (s t : M) : |g s - g t| ≤ 1 * dist s t := by
    simpa only [Real.dist_eq, NNReal.coe_one] using hg.dist_le_mul s t
  let f := Lip0.center o g 1 (by norm_num) hgl
  have hf : ‖f‖ ≤ 1 := Lip0.center_norm_le o g 1 (by norm_num) hgl
  rw [affineWeights_pairing o sep S ho _ (hfixed _) g 1 (by norm_num) hgl,
    affineWeights_pairing o sep S ho _ (hfixed _) g 1 (by norm_num) hgl]
  rw [show dualPairing o (Lip0.center o g 1 (by norm_num) hgl) (T (delta o x)) + g o -
      (dualPairing o (Lip0.center o g 1 (by norm_num) hgl) (T (delta o y)) + g o) =
      dualPairing o f (T (delta o x - delta o y)) by rw [map_sub, map_sub]; ring]
  calc
    _ ≤ ‖T (delta o x - delta o y)‖ * ‖f‖ := dualPairing_bound o f _
    _ ≤ ‖T (delta o x - delta o y)‖ := mul_le_of_le_one_right (norm_nonneg _) hf
    _ ≤ ‖T‖ * ‖delta o x - delta o y‖ := T.le_opNorm _
    _ ≤ c * dist x y := by rw [delta_sub_norm]; exact mul_le_mul_of_nonneg_right hn dist_nonneg

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

omit [MetricSpace M] in
theorem labelBump_self (h : M → N) (a : N) {L K : ℝ} {t : M} (ht : h t = a) :
    labelBump h a L K t = L := by simp [labelBump, ht]

theorem labelBump_sub (h : M → N) (hh : LipschitzWith 1 h) (a : N)
    {L K : ℝ} (hL : 0 ≤ L) (hK : 0 < K) (x y : M) :
    |labelBump h a L K x - labelBump h a L K y| ≤ (L/K) * dist x y := by
  unfold labelBump
  rw [← mul_sub, abs_mul, abs_of_nonneg hL]
  have hh' : dist (h x) (h y) ≤ dist x y := by simpa using hh.dist_le_mul x y
  calc
    _ ≤ L * |(1-dist a (h x)/K) - (1-dist a (h y)/K)| :=
      mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs _ _ 0) hL
    _ = (L/K) * |dist a (h x) - dist a (h y)| := by
      rw [show (1-dist a (h x)/K) - (1-dist a (h y)/K) =
        -(dist a (h x)-dist a (h y))/K by ring, abs_div, abs_neg, abs_of_pos hK]
      ring
    _ ≤ (L/K) * dist x y := mul_le_mul_of_nonneg_left
      ((show |dist a (h x) - dist a (h y)| ≤ dist (h x) (h y) by simpa only [dist_comm] using abs_dist_sub_le (h x) (h y) a).trans hh') (div_nonneg hL hK.le)

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

theorem affine_bump_mass (o : M)
    (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y) (S : Finset M) (ho : o ∈ S)
    (T : FreeSpace o →L[ℝ] FreeSpace o)
    (hfixed : ∀ u, supportProjection o sep S (T u) = T u)
    (h : M → N) (hh : LipschitzWith 1 h) (x a : M) (ha : h a = h x)
    (L K p R : ℝ) (hL : 0 ≤ L) (hK : 0 < K) (hp : 0 ≤ p)
    (hn : ‖T‖ ≤ 2*p) (hR : dist x a ≤ R) (he : ‖T (delta o a) - delta o a‖ < 1) :
    L - (L/K)*(2*p*R+1) ≤
      pairing (affineWeights o sep S ho (T (delta o x)))
        (fun j : S => labelBump h (h x) L K j.val) := by
  let b := labelBump h (h x) L K
  have hb (s t : M) : |b s - b t| ≤ (L/K)*dist s t := labelBump_sub h hh (h x) hL hK s t
  let f := Lip0.center o b (L/K) (div_nonneg hL hK.le) hb
  have hfn : ‖f‖ ≤ L/K := Lip0.center_norm_le o b _ _ hb
  have hda : ‖T (delta o x) - delta o a‖ ≤ 2*p*R+1 := by
    calc
      _ = ‖T (delta o x - delta o a) + (T (delta o a) - delta o a)‖ := by rw [map_sub]; congr 1; abel
      _ ≤ ‖T (delta o x - delta o a)‖ + ‖T (delta o a) - delta o a‖ := norm_add_le _ _
      _ ≤ (2*p)*R + 1 := add_le_add
        ((T.le_opNorm _).trans (mul_le_mul hn (by simpa using hR) (norm_nonneg _) (by positivity))) he.le
  have heq := affineWeights_pairing o sep S ho (T (delta o x)) (hfixed _) b (L/K)
    (div_nonneg hL hK.le) hb
  have hba : b a = L := labelBump_self h (h x) ha
  have hpair : pairing (affineWeights o sep S ho (T (delta o x))) (fun j : S => b j.val) - L =
      dualPairing o f (T (delta o x) - delta o a) := by
    rw [heq, map_sub, dualPairing_delta]
    change _ = _ - (b a - b o)
    rw [hba]
    ring
  have heval := (dualPairing_bound o f (T (delta o x) - delta o a)).trans
    (mul_le_mul hda hfn (norm_nonneg _) ((norm_nonneg _).trans hda))
  rw [← hpair] at heval
  have hh := (abs_le.mp heval).1
  change L - _ ≤ pairing _ (fun j : S => b j.val)
  nlinarith

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

theorem transition_card (hR : 2*L < R) (S : Finset (Point G color cap R)) (j : S) :
    Fintype.card {k : S // Transition G color cap R L j.val k.val} ≤
      Fintype.card (BoundedWords E (2*L)) := by
  have hf := closedBall_finite G color cap R (2*L) hR j.val
  have : Finite (Metric.closedBall j.val ((2*L : ℕ) : ℝ)) := hf.to_subtype
  let f : {k : S // Transition G color cap R L j.val k.val} →
      Metric.closedBall j.val ((2*L : ℕ) : ℝ) := fun k => ⟨k.val.val, by
        rw [Metric.mem_closedBall, dist_comm]
        exact k.property⟩
  have hfi : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z => z.val) huv
  have hh := (Nat.card_le_card_of_injective f hfi).trans
    (closedBall_card_le G color cap R (2*L) hR j.val)
  simpa only [Nat.card_eq_fintype_card] using hh

omit [Fintype E] in
theorem exceptional_unique_good (S : Finset (Point G color cap R)) (n : ℕ) (x : X)
    (hx : G.Good (fun x (j : S) => Compatible G color cap R L K x j.val)
      (fun j k : S => Transition G color cap R L j.val k.val) n x)
    (j : S) (e f : E) (he : j ∈ exceptionSet G color cap R L K S n x e)
    (hf : j ∈ exceptionSet G color cap R L K S n x f) : e = f := by
  exact exceptional_unique (he.resolve_left (not_not.mpr hx)) (hf.resolve_left (not_not.mpr hx))

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

-- ---- from OAI.Analysis.LipschitzFree.FiniteQuotients ----
namespace OAI

/-!
# Finite permutation representations of balls in free groups
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree.GraphProducer

variable (A : Type*) [Finite A] [DecidableEq A]

theorem ballPerm_apply (N : ℕ) (a : A) (g : WordBall A N)
    (h : FreeGroup.norm (FreeGroup.of a * g.val) ≤ N) :
    (ballPerm A N a g).val = FreeGroup.of a * g.val :=
  (exists_ball_perm A N a).choose_spec g h

theorem ballPerm_inv_apply (N : ℕ) (a : A) (g : WordBall A N)
    (h : FreeGroup.norm ((FreeGroup.of a)⁻¹ * g.val) ≤ N) :
    ((ballPerm A N a)⁻¹ g).val = (FreeGroup.of a)⁻¹ * g.val := by
  let y : WordBall A N := ⟨(FreeGroup.of a)⁻¹ * g.val, h⟩
  have hy : FreeGroup.norm (FreeGroup.of a * y.val) ≤ N := by
    simpa [y] using g.property
  have heq : ballPerm A N a y = g := by
    apply Subtype.ext
    simpa [y] using ballPerm_apply A N a y hy
  have hh : (ballPerm A N a)⁻¹ g = y := (ballPerm A N a).symm_apply_eq.mpr heq.symm
  exact congrArg Subtype.val hh

omit [Finite A] [DecidableEq A] in
lemma mk_cons_letter (a : A) (b : Bool) (l : List (A × Bool)) :
    FreeGroup.mk ((a,b) :: l) =
      (if b then FreeGroup.of a else (FreeGroup.of a)⁻¹) * FreeGroup.mk l := by
  cases b <;> rfl

theorem ballRep_word (N : ℕ) (l : List (A × Bool)) (hl : l.length ≤ N) :
    (ballRep A N (FreeGroup.mk l) (ballOne A N)).val = FreeGroup.mk l := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    obtain ⟨a, b⟩ := c
    have hlt : l.length ≤ N := by simpa using (Nat.le_of_succ_le hl)
    have hv := ih hlt
    have hm : FreeGroup.norm (FreeGroup.mk ((a,b)::l)) ≤ N :=
      FreeGroup.norm_mk_le.trans hl
    rw [mk_cons_letter] at hm ⊢
    rw [map_mul]
    change ((ballRep A N (if b then FreeGroup.of a else (FreeGroup.of a)⁻¹))
      (ballRep A N (FreeGroup.mk l) (ballOne A N))).val = _
    change (ballRep A N (FreeGroup.mk l) (ballOne A N)).val = FreeGroup.mk l at hv
    change (FreeGroup.lift (ballPerm A N) (FreeGroup.mk l) (ballOne A N)).val = FreeGroup.mk l at hv
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, map_inv, ballRep,
        FreeGroup.lift_apply_of]
      rw [ballPerm_inv_apply]
      · rw [hv]
      · rw [hv]
        exact hm
    · simp only [↓reduceIte, ballRep, FreeGroup.lift_apply_of]
      rw [ballPerm_apply]
      · rw [hv]
      · rw [hv]
        exact hm

theorem ballRep_apply_one (N : ℕ) (g : FreeGroup A) (hg : FreeGroup.norm g ≤ N) :
    (ballRep A N g (ballOne A N)).val = g := by
  simpa only [FreeGroup.mk_toWord] using ballRep_word A N g.toWord hg

theorem ballRep_injective_on (N : ℕ) :
    Set.InjOn (ballRep A N) {g | FreeGroup.norm g ≤ N} := by
  intro g hg h hh heq
  have := congrArg (fun σ : Equiv.Perm (WordBall A N) => (σ (ballOne A N)).val) heq
  simpa [ballRep_apply_one A N g hg, ballRep_apply_one A N h hh] using this

theorem prefixes_injective (N : ℕ) (l : List (A × Bool))
    (hl : FreeGroup.IsReduced l) (hlen : l.length ≤ N)
    (x : Equiv.Perm (WordBall A N)) :
    Function.Injective (fun i : Fin (l.length + 1) =>
      x * ballRep A N (FreeGroup.mk (l.take i.val))) := by
  intro i j hij
  have ht (t : ℕ) : FreeGroup.norm (FreeGroup.mk (l.take t)) ≤ N :=
    FreeGroup.norm_mk_le.trans (by
      rw [List.length_take]
      exact (min_le_right _ _).trans hlen)
  have heq := ballRep_injective_on A N (ht i.val) (ht j.val) (mul_left_cancel hij)
  have hi : FreeGroup.IsReduced (l.take i.val) := hl.take _
  have hj : FreeGroup.IsReduced (l.take j.val) := hl.take _
  have he := congrArg (fun g : FreeGroup A => g.toWord.length) heq
  simp only [FreeGroup.toWord_mk, hi.reduce_eq, hj.reduce_eq, List.length_take] at he
  apply Fin.ext
  simpa [Nat.min_eq_left (Nat.le_of_lt_succ i.isLt),
    Nat.min_eq_left (Nat.le_of_lt_succ j.isLt)] using he

end DiscreteFree.GraphProducer

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.GraphGirth ----
namespace OAI

/-!
# Cayley graphs with injective bounded reduced walks
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.GraphProducer
open scoped Classical
variable (A : Type*) [Finite A] [DecidableEq A]

theorem cayley_walk (N : ℕ) (x : Cayley A N) (w : List (A × Bool)) :
    (cayleyGraph A N).walk x w = x * ballRep A N (FreeGroup.mk w) := by
  induction w generalizing x with
  | nil =>
    change x = x * ballRep A N 1
    rw [map_one, mul_one]
  | cons e w ih =>
    rcases e with ⟨a,b⟩
    rw [PortGraph.walk_cons, ih, mk_cons_letter, map_mul, ← mul_assoc]
    rfl

theorem cayley_reduced (N : ℕ) (w : List (A × Bool)) :
    (cayleyGraph A N).Reduced w ↔ FreeGroup.IsReduced w := by
  have he : (fun e f : A × Bool => f ≠ invertPort A e) =
      (fun e f : A × Bool => e.1 = f.1 → e.2 = f.2) := by
    funext e f
    apply propext
    rcases e with ⟨a,b⟩
    rcases f with ⟨c,d⟩
    cases b <;> cases d <;> simp [invertPort, eq_comm]
  change w.IsChain (fun e f => f ≠ invertPort A e) ↔ _
  rw [he]
  rfl

theorem cayley_prefix_injective (N : ℕ) (x : Cayley A N) (w : List (A × Bool))
    (hw : (cayleyGraph A N).Reduced w) (hN : w.length ≤ N) :
    Function.Injective (fun i : Fin (w.length+1) => (cayleyGraph A N).walk x (w.take i.val)) := by
  simp only [cayley_walk]
  exact prefixes_injective A N w ((cayley_reduced A N w).mp hw) hN x

theorem allColorings_walk (C : Type*) (N : ℕ)
    (x : (Cayley A N → C) × Cayley A N) (w : List (A × Bool)) :
    (allColoringsGraph A C N).walk x w = (x.1, (cayleyGraph A N).walk x.2 w) := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih => exact ih _

end DiscreteFree.GraphProducer
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.ColorCounting ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Counting colorings subject to vertex constraints
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree.ColorCounting
open scoped BigOperators Classical

variable {X I C : Type*}

theorem cardinal_identity [Fintype X] [Fintype I] [Fintype C]
    (f : I → X) (hf : Function.Injective f) (P : I → Finset C) :
    Fintype.card {c : X → C // ∀ i, c (f i) ∈ P i} *
        Fintype.card C ^ Fintype.card I =
      (∏ i, (P i).card) * Fintype.card (X → C) := by
  classical
  have hg := Fintype.card_congr (goodColoringEquiv f hf (fun i c => c ∈ P i))
  have hp := Fintype.card_congr
    (Equiv.subtypePiEquivPi (p := fun i c => c ∈ P i))
  simp only [Fintype.card_pi, Fintype.card_coe] at hp
  simp only [Fintype.card_prod, hp, Fintype.card_fun] at hg
  have ht := Fintype.card_congr (coloringEquiv (C := C) f hf)
  simp only [Fintype.card_prod, Fintype.card_fun] at ht
  rw [hg, Fintype.card_fun, ht]
  ring

theorem cardinal_bound [Fintype X] [Fintype I] [Fintype C]
    (f : I → X) (hf : Function.Injective f) (P : I → Finset C)
    (H : ℕ) (hH : ∀ i, (P i).card ≤ H) :
    Fintype.card {c : X → C // ∀ i, c (f i) ∈ P i} *
        Fintype.card C ^ Fintype.card I ≤
      H ^ Fintype.card I * Fintype.card (X → C) := by
  classical
  rw [cardinal_identity f hf P]
  apply Nat.mul_le_mul_right
  simpa using Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    (fun index (_ : index ∈ (Finset.univ : Finset I)) => hH index)

end DiscreteFree.ColorCounting

noncomputable section
namespace DiscreteFree.ColorCounting
open scoped BigOperators Classical

theorem union_bound {X P : Type*} [Fintype X] [Fintype P] (r : P → X → Prop) :
    Fintype.card {x : X // ∃ p, r p x} ≤ ∑ p, Fintype.card {x : X // r p x} := by
  let f : (Σ p : P, {x : X // r p x}) → {x : X // ∃ p, r p x} :=
    fun z => ⟨z.2.val, z.1, z.2.property⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, p, hp⟩
    exact ⟨⟨p, x, hp⟩, rfl⟩
  simpa only [Fintype.card_sigma] using Fintype.card_le_of_surjective f hf

theorem weighted_union_bound {X P : Type*} [Fintype X] [Fintype P]
    (r : P → X → Prop) (a b : ℕ)
    (h : ∀ p, Fintype.card {x : X // r p x} * a ≤ b) :
    Fintype.card {x : X // ∃ p, r p x} * a ≤ Fintype.card P * b := by
  calc
    _ ≤ (∑ p, Fintype.card {x : X // r p x}) * a :=
      Nat.mul_le_mul_right _ (union_bound r)
    _ = ∑ p, Fintype.card {x : X // r p x} * a := Finset.sum_mul _ _ _
    _ ≤ ∑ _p : P, b := Finset.sum_le_sum (fun p _ => h p)
    _ = _ := by simp

theorem many_walks_bound {X W I S C : Type*}
    [Fintype X] [Fintype W] [Fintype I] [Fintype S] [Fintype C]
    (f : W → I → X) (hf : ∀ w, Function.Injective (f w))
    (P : S → I → Finset C) (H : ℕ) (hH : ∀ s i, (P s i).card ≤ H) :
    Fintype.card {c : X → C // ∃ w s, ∀ i, c (f w i) ∈ P s i} *
        Fintype.card C ^ Fintype.card I ≤
      Fintype.card W * Fintype.card S * H ^ Fintype.card I * Fintype.card (X → C) := by
  have h := weighted_union_bound
    (fun ws : W × S => fun c : X → C => ∀ i, c (f ws.1 i) ∈ P ws.2 i)
    (Fintype.card C ^ Fintype.card I) (H ^ Fintype.card I * Fintype.card (X → C))
    (fun ws => by
      convert cardinal_bound (f ws.1) (hf ws.1) (P ws.2) H (hH ws.2) using 1
      simp only [← Nat.card_eq_fintype_card])
  simp only [Prod.exists, Fintype.card_prod] at h
  exact h.trans_eq (by ring)

theorem colored_roots_bound {X W I S C : Type*}
    [Fintype X] [Fintype W] [Fintype I] [Fintype S] [Fintype C]
    (f : X → W → I → X) (hf : ∀ x w, Function.Injective (f x w))
    (P : S → I → Finset C) (H : ℕ) (hH : ∀ s i, (P s i).card ≤ H) :
    Fintype.card {z : (X → C) × X // ∃ w s, ∀ i, z.1 (f z.2 w i) ∈ P s i} *
        Fintype.card C ^ Fintype.card I ≤
      Fintype.card W * Fintype.card S * H ^ Fintype.card I * Fintype.card ((X → C) × X) := by
  let e : {z : (X → C) × X // ∃ w s, ∀ i, z.1 (f z.2 w i) ∈ P s i} ≃
      Σ x : X, {c : X → C // ∃ w s, ∀ i, c (f x w i) ∈ P s i} :=
    { toFun := fun z => ⟨z.val.2, z.val.1, z.property⟩
      invFun := fun z => ⟨(z.2.val, z.1), z.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma, Finset.sum_mul]
  calc
    _ ≤ ∑ _x : X, Fintype.card W * Fintype.card S * H ^ Fintype.card I *
        Fintype.card (X → C) :=
      Finset.sum_le_sum (fun x _ => many_walks_bound (f x) (hf x) P H hH)
    _ = _ := by simp; ring

end DiscreteFree.ColorCounting
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.GraphColoring ----
namespace OAI

/-!
# Rare matched walks and the fixed all-colorings graph sequence
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.GraphProducer
open scoped Classical
variable (A : Type*) [Fintype A] [DecidableEq A]
    (C S : Type*) [Fintype C] [Fintype S]

theorem rare_matched_bound (n N Q H : ℕ) (hnN : n ≤ N)
    (compatible : ((Cayley A N → C) × Cayley A N) → S → Prop)
    (trans : S → S → Prop) (P : S → Finset C)
    (hP : ∀ j, (P j).card ≤ H)
    (hcolor : ∀ z j, compatible z j → z.1 z.2 ∈ P j)
    (hQ : ∀ j, Fintype.card {k : S // trans j k} ≤ Q) :
    Nat.card {z : (Cayley A N → C) × Cayley A N //
        ¬ (allColoringsGraph A C N).Good compatible trans n z} * Nat.card C ^ (n+1) ≤
      Nat.card (A × Bool) ^ n * (Nat.card S * Q ^ n) * H ^ (n+1) *
        Nat.card ((Cayley A N → C) × Cayley A N) := by
  let W := {w : Words (A × Bool) n // (cayleyGraph A N).Reduced w.val}
  let f : Cayley A N → W → Fin (n+1) → Cayley A N :=
    fun x w i => (cayleyGraph A N).walk x (w.val.val.take i.val)
  have hf : ∀ x w, Function.Injective (f x w) := by
    intro x w i j h
    have hi : i.val < w.val.val.length+1 := by rw [w.val.property]; exact i.isLt
    have hj : j.val < w.val.val.length+1 := by rw [w.val.property]; exact j.isLt
    have hw : w.val.val.length ≤ N := by rw [w.val.property]; exact hnN
    have hh := cayley_prefix_injective A N x w.val.val w.property hw
      (show (cayleyGraph A N).walk x (w.val.val.take (⟨i.val, hi⟩ : Fin (w.val.val.length+1)).val) =
        (cayleyGraph A N).walk x (w.val.val.take (⟨j.val, hj⟩ : Fin (w.val.val.length+1)).val) from h)
    exact Fin.ext (congrArg (fun t : Fin (w.val.val.length+1) => t.val) hh)
  let PC : StatePaths.Path trans n → Fin (n+1) → Finset C :=
    fun p i => P (StatePaths.Path.vertex trans p i)
  let B := {z : (Cayley A N → C) × Cayley A N //
    ¬ (allColoringsGraph A C N).Good compatible trans n z}
  let E := {z : (Cayley A N → C) × Cayley A N //
    ∃ w p, ∀ i, z.1 (f z.2 w i) ∈ PC p i}
  have hBE : Nat.card B ≤ Nat.card E := by
    let emb : B → E := fun z => ⟨z.val, by
      have hz := z.property
      simp only [PortGraph.Good, not_forall, not_not] at hz
      obtain ⟨j, w, hw, hr, hm⟩ := hz
      obtain ⟨p, hp⟩ := PortGraph.Matched.exists_based (allColoringsGraph A C N)
        compatible trans hm
      subst n
      refine ⟨⟨⟨w, rfl⟩, hr⟩, ⟨j, p⟩, fun i => ?_⟩
      have hpi := hp i
      rw [allColorings_walk] at hpi
      exact hcolor _ _ hpi⟩
    exact Nat.card_le_card_of_injective emb (by
      intro x y h
      exact Subtype.ext (congrArg (fun z : E => z.val) h))
  have hcount := ColorCounting.colored_roots_bound f hf PC H (fun p i => hP (StatePaths.Path.vertex trans p i))
  simp only [← Nat.card_eq_fintype_card, Nat.card_fin] at hcount
  have hW : Nat.card W ≤ Nat.card (A × Bool) ^ n := by
    have hh := Fintype.card_le_of_injective (fun w : W => w.val) Subtype.val_injective
    rw [Words.card] at hh
    simpa only [← Nat.card_eq_fintype_card] using hh
  have hS := StatePaths.card_path_le trans Q hQ n
  simp only [← Nat.card_eq_fintype_card] at hS
  calc
    _ ≤ Nat.card E * Nat.card C ^ (n+1) := Nat.mul_le_mul_right _ hBE
    _ ≤ Nat.card W * Nat.card (StatePaths.Path trans n) * H ^ (n+1) *
        Nat.card ((Cayley A N → C) × Cayley A N) := hcount
    _ ≤ _ := by gcongr

end DiscreteFree.GraphProducer
end

noncomputable section
namespace DiscreteFree.GraphProducer
open scoped Classical
variable (A C : Type*) [Fintype A] [DecidableEq A] [Fintype C]

variable {S : Type*}

omit [Fintype C] in

theorem sequence_matched (compatible : Vertex A C → S → Prop) (trans : S → S → Prop)
    (N : ℕ) (z : (Cayley A N → C) × Cayley A N) (j : S) (w : List (A × Bool)) :
    (sequenceGraph A C).Matched compatible trans (intoSequence A C N z) j w ↔
      (allColoringsGraph A C N).Matched (fun z => compatible (intoSequence A C N z)) trans z j w := by
  induction w generalizing z j with
  | nil => rfl
  | cons e w ih =>
    simp only [PortGraph.Matched, sequence_move, ih]

omit [Fintype C] in
theorem sequence_good (compatible : Vertex A C → S → Prop) (trans : S → S → Prop)
    (n N : ℕ) (z : (Cayley A N → C) × Cayley A N) :
    (sequenceGraph A C).Good compatible trans n (intoSequence A C N z) ↔
      (allColoringsGraph A C N).Good (fun z => compatible (intoSequence A C N z)) trans n z := by
  simp only [PortGraph.Good, sequence_matched]
  rfl

end DiscreteFree.GraphProducer
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.GraphSequence ----
namespace OAI

/-!
# Good-vertex density in the all-colorings sequence
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.GraphProducer
open scoped Classical
variable (A C S : Type*) [Fintype A] [DecidableEq A] [Fintype C] [Nonempty C] [Fintype S]

theorem exists_rare_component (Q H V : ℕ) (hQpos : 0 < Q) (hHpos : 0 < H)
    (hDpos : 0 < Nat.card (A × Bool))
    (hk : 2 * Nat.card (A × Bool) * Q * H < Nat.card C)
    (compatible : Vertex A C → S → Prop) (trans : S → S → Prop) (P : S → Finset C)
    (hP : ∀ j, (P j).card ≤ H)
    (hcolor : ∀ z j, compatible z j → sequenceColor A C z ∈ P j)
    (hQ : ∀ j, Fintype.card {k : S // trans j k} ≤ Q) :
    ∃ n : ℕ, 2 ≤ n ∧
      20 * V * Nat.card {z : (Cayley A n → C) × Cayley A n //
        ¬ (sequenceGraph A C).Good compatible trans n (intoSequence A C n z)} <
      Nat.card ((Cayley A n → C) × Cayley A n) := by
  let d := Nat.card (A × Bool)
  let k := Nat.card C
  let s := Nat.card S
  let q := d*Q*H
  have hq : 0 < q := Nat.mul_pos (Nat.mul_pos hDpos hQpos) hHpos
  have hk' : 2*q < k := by simpa only [q, d, k, Nat.mul_assoc] using hk
  have hkp : 0 < k := lt_trans (by omega) hk'
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (20*V*s*H) (by norm_num : 1 < (2 : ℕ))
  let n := m+2
  have hn : 20*V*s*H < 2^n := hm.trans_le (Nat.pow_le_pow_right (by omega) (by dsimp [n]; omega))
  have hcoeff : 20*V*(d^n*(s*Q^n)*H^(n+1)) < k^(n+1) := by
    calc
      _ = (20*V*s*H) * q^n := by dsimp [q]; simp only [mul_pow, pow_succ]; ring
      _ < 2^n * q^n := Nat.mul_lt_mul_of_pos_right hn (pow_pos hq n)
      _ = (2*q)^n := (mul_pow ..).symm
      _ ≤ k^n := Nat.pow_le_pow_left hk'.le n
      _ ≤ k^(n+1) := Nat.pow_le_pow_right hkp (Nat.le_succ _)
  have hcount := rare_matched_bound A C S n n Q H le_rfl
    (fun z => compatible (intoSequence A C n z)) trans P hP
    (fun z j hj => hcolor _ _ hj) hQ
  have heq : {z : (Cayley A n → C) × Cayley A n //
      ¬ (allColoringsGraph A C n).Good (fun z => compatible (intoSequence A C n z)) trans n z} =
      {z : (Cayley A n → C) × Cayley A n //
      ¬ (sequenceGraph A C).Good compatible trans n (intoSequence A C n z)} := by
    congr 1
    funext z
    exact propext (not_congr (sequence_good A C compatible trans n n z).symm)
  rw [heq] at hcount
  change _ * k^(n+1) ≤ d^n*(s*Q^n)*H^(n+1)*_ at hcount
  have hroot : 0 < Nat.card ((Cayley A n → C) × Cayley A n) := Nat.card_pos
  refine ⟨n, by dsimp [n]; omega, ?_⟩
  by_contra h
  have hh := Nat.mul_le_mul_right (k^(n+1)) (Nat.le_of_not_gt h)
  have hc := Nat.mul_le_mul_left (20*V) hcount
  have hf := Nat.mul_lt_mul_of_pos_right hcoeff hroot
  nlinarith

end DiscreteFree.GraphProducer
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

theorem obstruction (hp : 1 ≤ p)
    (T : FreeSpace (base p) →L[ℝ] FreeSpace (base p))
    (hfin : Module.Finite ℝ (LinearMap.range T.toLinearMap)) (hn : ‖T‖ ≤ (p : ℝ)) :
    ∃ a ∈ anchors p, (1/2 : ℝ) ≤ ‖T (delta (base p) a) - delta (base p) a‖ := by
  by_contra h
  have he : ∀ a ∈ anchors p, ‖T (delta (base p) a) - delta (base p) a‖ < 1/2 := by
    simpa only [not_exists,not_and,not_le] using h
  obtain ⟨S,T₁,ho,_,hT,hfixed,hanchor⟩ := finite_support_reduction (base p) (separation p)
    (B p) p (Nat.cast_nonneg _) (by exact_mod_cast hp) (fun x => diameter p x (base p))
    (anchors p) T hfin hn he
  exact finite_support_impossible p hp S ho T₁ hT hfixed hanchor

end DiscreteFree.BlockConstruction

namespace DiscreteFree

end DiscreteFree
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.BlockBAP ----
namespace OAI

/-!
# Finite anchor obstructions exclude bounded approximation constants
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree

theorem not_hasBAP_of_finite_obstruction {M : Type*} [MetricSpace M] (o : M)
    (A : Finset M) (p ε : ℝ) (hε : 0 < ε)
    (hobs : ∀ T : FreeSpace o →L[ℝ] FreeSpace o,
      Module.Finite ℝ (LinearMap.range T.toLinearMap) → ‖T‖ ≤ p →
        ∃ a ∈ A, ε ≤ ‖T (delta o a) - delta o a‖)
    (Λ : ℝ) (hΛ : Λ ≤ p) : ¬ HasBAP (FreeSpace o) Λ := by
  intro h
  let C := (delta o) '' (A : Set M)
  have hC : IsCompact C := (A.finite_toSet.image (delta o)).isCompact
  obtain ⟨T,hT,hTnorm,η,hη,he⟩ := h C hC ε hε
  obtain ⟨a,ha,herr⟩ := hobs T hT (hTnorm.trans hΛ)
  have herror := he (delta o a) ⟨a,ha,rfl⟩
  linarith

namespace BlockConstruction
open BlockParameters
variable (p : ℕ) [Fact (0 < R p)]

theorem noBAP (hp : 1 ≤ p) (Λ : ℝ) (hΛ : Λ ≤ (p : ℝ)) :
    ¬ HasBAP (FreeSpace (base p)) Λ :=
  not_hasBAP_of_finite_obstruction (base p) (anchors p) p (1/2) (by norm_num)
    (fun T => obstruction p hp T) Λ hΛ

end BlockConstruction
end DiscreteFree
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.WedgeApproximation ----
namespace OAI

/-!
# Compact-uniform approximation on wedges and contractive BAP inheritance
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped Classical BigOperators

section OperatorTools
variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem contraction_norm (T : E →L[ℝ] F) (hT : ‖T‖ ≤ 1) (u : E) : ‖T u‖ ≤ ‖u‖ := by
  exact (T.le_opNorm u).trans (by simpa using mul_le_mul_of_nonneg_right hT (norm_nonneg u))

theorem finiteRank_sandwich (I : G →L[ℝ] H) (T : F →L[ℝ] G) (P : E →L[ℝ] F)
    (hT : Module.Finite ℝ (LinearMap.range T.toLinearMap)) :
    Module.Finite ℝ (LinearMap.range ((I.comp T).comp P).toLinearMap) := by
  have hfg := ((Submodule.fg_iff_finiteDimensional _).mpr hT).map I.toLinearMap
  apply (Submodule.fg_iff_finiteDimensional _).mp
  apply hfg.of_le
  rintro v ⟨u,rfl⟩
  exact ⟨T (P u),⟨P u,rfl⟩,rfl⟩

theorem hasBAP_of_contractive_retract (I : E →L[ℝ] F) (P : F →L[ℝ] E)
    (hI : ‖I‖ ≤ 1) (hP : ‖P‖ ≤ 1) (hPI : P.comp I = ContinuousLinearMap.id ℝ E)
    (Λ : ℝ) (h : HasBAP F Λ) : HasBAP E Λ := by
  intro C hC ε hε
  obtain ⟨U,hU,hn,η,hη,he⟩ := h (I '' C) (hC.image I.continuous) ε hε
  let T := (P.comp U).comp I
  refine ⟨T,finiteRank_sandwich P U I hU,?_,η,hη,?_⟩
  · apply le_trans _ hn
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg U)
    intro u
    calc
      ‖T u‖ ≤ ‖U (I u)‖ := contraction_norm P hP _
      _ ≤ ‖U‖ * ‖I u‖ := U.le_opNorm _
      _ ≤ ‖U‖ * ‖u‖ := mul_le_mul_of_nonneg_left (contraction_norm I hI u) (norm_nonneg U)
  · intro u hu
    have hpu : P (I u) = u := congrArg (fun A : E →L[ℝ] E => A u) hPI
    calc
      ‖T u-u‖ = ‖P (U (I u)-I u)‖ := by dsimp [T]; rw [map_sub,hpu]
      _ ≤ ‖U (I u)-I u‖ := contraction_norm P hP _
      _ ≤ η := he _ ⟨u,hu,rfl⟩
end OperatorTools

namespace MetricWedge
universe u
variable (M : ℕ → Type u) [∀ n, MetricSpace (M n)] (o : ∀ n, M n)

end MetricWedge
end DiscreteFree
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.Renorming ----
namespace OAI

/-!
# Equivalent complete norms on real ℓ¹ with quantitative BAP obstructions
-/

noncomputable section
open scoped BigOperators ENNReal Classical

namespace DiscreteFree

theorem hasBAP_of_linearIsometryEquiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (I : E ≃ₗᵢ[ℝ] F) (Λ : ℝ) (h : HasBAP F Λ) : HasBAP E Λ := by
  exact hasBAP_of_contractive_retract
    I.toLinearIsometry.toContinuousLinearMap I.symm.toLinearIsometry.toContinuousLinearMap
    I.toLinearIsometry.norm_toContinuousLinearMap_le
    I.symm.toLinearIsometry.norm_toContinuousLinearMap_le
    (by ext u; exact I.symm_apply_apply u) Λ h

theorem hasBAP_linearIsometryEquiv_iff {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (I : E ≃ₗᵢ[ℝ] F) (Λ : ℝ) : HasBAP E Λ ↔ HasBAP F Λ :=
  ⟨hasBAP_of_linearIsometryEquiv I.symm Λ, hasBAP_of_linearIsometryEquiv I Λ⟩

end DiscreteFree
end

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree

theorem real_l1_quantitative_renorming : RealL1RenormingStatement := by
  intro p hp
  let : Fact (0 < BlockParameters.R p) := ⟨BlockParameters.R_pos hp⟩
  let o := BlockConstruction.base p
  let sep := BlockConstruction.separation p
  have hb (x : BlockConstruction.Block p) : dist x o ≤ blockBound p := by
    simpa only [BlockParameters.B_formula] using BlockConstruction.diameter p x o
  have hB : 0 ≤ blockBound p := by dsimp [blockBound]; positivity
  let α := {x : BlockConstruction.Block p // x ≠ o}
  let : Infinite α := (Set.finite_singleton o).infinite_compl.to_subtype
  let : Encodable α := Encodable.ofCountable α
  let : Denumerable α := Denumerable.ofEncodableOfInfinite α
  let e : ℕ ≃ α := (Denumerable.eqv α).symm
  let J : RealL1 ≃L[ℝ] FreeSpace o := Coefficients.equiv o sep e (blockBound p) hb
  let A : RealL1 ≃ₗ[ℝ] FreeSpace o := J.toLinearEquiv
  let m : Module ℝ RealL1 := inferInstance
  let N : AddGroupNorm RealL1 :=
    { toFun := fun c => ‖J c‖
      map_zero' := by simp
      add_le' := fun c d => by simpa only [map_add] using norm_add_le (J c) (J d)
      neg' := fun c => by simp
      eq_zero_of_map_eq_zero' := fun c hc => J.injective (by simpa using hc) }
  refine ⟨N, ?_, ?_, ?_⟩
  · intro r c
    change ‖J (r • c)‖ = |r| * ‖J c‖
    rw [map_smul, norm_smul, Real.norm_eq_abs]
  · exact Coefficients.equiv_bounds o sep e (blockBound p) hb
  · let : NormedAddCommGroup RealL1 := N.toNormedAddCommGroup
    let s : NormedSpace ℝ RealL1 :=
      { toModule := m
        norm_smul_le := fun r c => by
          change ‖J (r • c)‖ ≤ ‖r‖ * ‖J c‖
          rw [map_smul, norm_smul] }
    refine ⟨s, rfl, ?_⟩
    let := s
    let I : RealL1 ≃ₗᵢ[ℝ] FreeSpace o :=
      { toLinearEquiv := A
        norm_map' := fun _ => rfl }
    have hgood : HasBAP (FreeSpace o) (2 * blockBound p) :=
      bounded_separated_hasBAP o sep (blockBound p) hB hb
    have hbad : ¬ HasBAP (FreeSpace o) (p : ℝ) :=
      BlockConstruction.noBAP p hp p le_rfl
    have hnewbad : ¬ HasBAP RealL1 (p : ℝ) := fun h =>
      hbad ((hasBAP_linearIsometryEquiv_iff I p).mp h)
    refine ⟨I.toIsometryEquiv.completeSpace,
      (hasBAP_linearIsometryEquiv_iff I _).mpr hgood, hnewbad, ?_⟩
    intro hp1
    simpa only [hp1, Nat.cast_one] using hnewbad

end DiscreteFree
end

end OAI

-- ---- mission target ----
open OAI OAI.DiscreteFree
open scoped BigOperators ENNReal
variable {M : Type*} [MetricSpace M]
open scoped BigOperators ENNReal

theorem solution : RealL1RenormingStatement := by
  first
    | exact OAI.DiscreteFree.real_l1_quantitative_renorming
    | (apply OAI.DiscreteFree.real_l1_quantitative_renorming <;> assumption)
    | (intros; apply OAI.DiscreteFree.real_l1_quantitative_renorming <;> assumption)
