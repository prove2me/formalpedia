-- Prove2me | solution 1 for OAI.CompactBanach.main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:36:41.914979+00:00
-- url     : https://prove2.me/submissions/8d426b9d-d1c3-4a12-a748-40caee838d48

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/CompactBanach.lean:L20-L89
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.CompactBanach.main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_CompactBanach_main) verbatim and is proved by it.
import Mathlib
import Definitions.Def_CompactBanach
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
import Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings
import Definitions.Def_OAI_Geometry_DoublingHilbert_Doubling
import Definitions.Def_OAI_Geometry_DoublingHilbert_CoordinateSupport
import Definitions.Def_OAI_Geometry_DoublingHilbert_CoordinateMap
import Definitions.Def_OAI_Geometry_DoublingHilbert_IntrinsicCovers
import Definitions.Def_OAI_Geometry_DoublingHilbert_ClusterScales
import Theorems.Thm_OAI_CompactBanach_ambient_doubling_clusters
import Theorems.Thm_OAI_CompactBanach_ambient_iterated_cover
import Theorems.Thm_OAI_CompactBanach_compact_shrinking_union
import Theorems.Thm_OAI_CompactBanach_doubling_iff_ambient
import Theorems.Thm_OAI_CompactBanach_exists_auerbach_vectors
import Theorems.Thm_OAI_CompactBanach_finite_placement
import Theorems.Thm_OAI_DoublingHilbert_constructedSet_cover
import Theorems.Thm_OAI_DoublingHilbert_no_scaled_embedding

-- ---- from OAI.Geometry.DoublingHilbert.FiniteCompactness ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

open Set Metric
noncomputable section
namespace CompactBanach

theorem normalized_embedding_of_finite
    {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [ProperSpace E]
    (o : X) {A : ℝ} (hA : 0 ≤ A)
    (hfinite : ∀ s : Finset X, ∃ f : s → E, ∀ x y : s,
      dist x y ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ A * dist x y) :
    ∃ f : X → E, ∀ x y : X,
      dist x y ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ A * dist x y := by
  classical
  let Q : Set (X → E) := {f | ∀ x, f x ∈ closedBall 0 (A * dist o x)}
  have hQ : IsCompact Q := isCompact_pi_infinite fun x => isCompact_closedBall _ _
  let C : X × X → Set (X → E) := fun p => {f |
    dist p.1 p.2 ≤ dist (f p.1) (f p.2) ∧
      dist (f p.1) (f p.2) ≤ A * dist p.1 p.2}
  have hC (p : X × X) : IsClosed (C p) :=
    (isClosed_le continuous_const ((continuous_apply p.1).dist (continuous_apply p.2))).inter
      (isClosed_le ((continuous_apply p.1).dist (continuous_apply p.2)) continuous_const)
  have hFIP (u : Finset (X × X)) : (Q ∩ ⋂ p ∈ u, C p).Nonempty := by
    let s : Finset X := insert o (u.image Prod.fst ∪ u.image Prod.snd)
    have ho : o ∈ s := by simp [s]
    obtain ⟨f, hf⟩ := hfinite s
    let g : X → E := fun x => if hx : x ∈ s then f ⟨x, hx⟩ - f ⟨o, ho⟩ else 0
    refine ⟨g, ?_, ?_⟩
    · intro x
      by_cases hx : x ∈ s
      · simp only [g, dite_eq_left hx, mem_closedBall, dist_zero_right]
        simpa only [dist_eq_norm, Subtype.dist_eq, dist_comm o x] using (hf ⟨x, hx⟩ ⟨o, ho⟩).2
      · simp only [g, dite_eq_right hx, mem_closedBall, dist_self]
        exact mul_nonneg hA dist_nonneg
    · simp only [mem_iInter]
      intro p hp
      have hx : p.1 ∈ s := by simp [s, Finset.mem_image_of_mem _ hp]
      have hy : p.2 ∈ s := by simp [s, Finset.mem_image_of_mem _ hp]
      change dist p.1 p.2 ≤ dist (g p.1) (g p.2) ∧
        dist (g p.1) (g p.2) ≤ A * dist p.1 p.2
      simpa only [g, dite_eq_left hx, dite_eq_left hy, dist_sub_right, Subtype.dist_eq] using
        hf ⟨p.1, hx⟩ ⟨p.2, hy⟩
  obtain ⟨f, _, hf⟩ := hQ.inter_iInter_nonempty C hC hFIP
  refine ⟨f, fun x y => ?_⟩
  exact mem_iInter.mp hf (x, y)

                                                                
theorem normalized_embedding_of_scaled
    {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → E} {a A : ℝ} (ha : 0 < a)
    (hf : ∀ x y, a * dist x y ≤ dist (f x) (f y) ∧
      dist (f x) (f y) ≤ A * a * dist x y) :
    ∃ g : X → E, ∀ x y,
      dist x y ≤ dist (g x) (g y) ∧ dist (g x) (g y) ≤ A * dist x y := by
  let g : X → E := fun x => a⁻¹ • f x
  have hd (x y : X) : dist (g x) (g y) = a⁻¹ * dist (f x) (f y) := by
    simp only [g, dist_smul₀, Real.norm_eq_abs, abs_inv, abs_of_pos ha]
  refine ⟨g, fun x y => ?_⟩
  rw [hd]
  constructor
  · calc
      dist x y = a⁻¹ * (a * dist x y) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hf x y).1 (inv_nonneg.mpr ha.le)
  · calc
      a⁻¹ * dist (f x) (f y) ≤ a⁻¹ * (A * a * dist x y) :=
        mul_le_mul_of_nonneg_left (hf x y).2 (inv_nonneg.mpr ha.le)
      _ = A * dist x y := by field_simp

                                                                                 
                                                          
theorem finite_witness_of_no_embedding
    {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] (o : X) {A : ℝ} (hA : 0 ≤ A)
    (hno : ¬ ∃ f : X → E, ∀ x y,
      dist x y ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ A * dist x y) :
    ∃ s : Finset X, ¬ ∃ f : s → E, ∃ a : ℝ, 0 < a ∧
      ∀ x y : s, a * dist x y ≤ dist (f x) (f y) ∧
        dist (f x) (f y) ≤ A * a * dist x y := by
  classical
  by_contra! h
  apply hno
  apply normalized_embedding_of_finite o hA
  intro s
  obtain ⟨f, a, ha, hf⟩ := h s
  exact normalized_embedding_of_scaled ha hf

end CompactBanach
end

end OAI

-- ---- from OAI.Geometry.DoublingHilbert.FiniteWitness ----
namespace OAI

open Set Metric
noncomputable section
namespace CompactBanach

theorem finite_witness (k : ℕ) {A : ℝ} (hA : 1 ≤ A) :
    ∃ s : Finset DoublingHilbert.constructedSet,
      ¬ ∃ f : s → EuclideanSpace ℝ (Fin k), ∃ a : ℝ, 0 < a ∧
        ∀ x y : s, a * dist x y ≤ dist (f x) (f y) ∧
          dist (f x) (f y) ≤ A * a * dist x y := by
  let o : DoublingHilbert.constructedSet :=
    ⟨DoublingHilbert.point 0 0, DoublingHilbert.point_mem _ _ (DoublingHilbert.admissible_zero _)⟩
  apply finite_witness_of_no_embedding o (le_trans zero_le_one hA)
  rintro ⟨f, hf⟩
  apply DoublingHilbert.no_scaled_embedding f (a := 1) zero_lt_one hA
  simpa only [one_mul, mul_one] using hf

                                                                          
                                       
theorem finite_witness_card (k : ℕ) {A : ℝ} (hA : 1 ≤ A) :
    ∃ s : Finset DoublingHilbert.constructedSet, 2 ≤ s.card ∧
      ¬ ∃ f : s → EuclideanSpace ℝ (Fin k), ∃ a : ℝ, 0 < a ∧
        ∀ x y : s, a * dist x y ≤ dist (f x) (f y) ∧
          dist (f x) (f y) ≤ A * a * dist x y := by
  classical
  obtain ⟨s, hs⟩ := finite_witness k hA
  refine ⟨s, ?_, hs⟩
  by_contra! hc
  have hc' : s.card ≤ 1 := by omega
  apply hs
  refine ⟨fun _ => 0, 1, zero_lt_one, fun x y => ?_⟩
  have hxy : x = y := Subtype.ext (Finset.card_le_one.mp hc' x x.property y y.property)
  simp [hxy]

end CompactBanach
end

end OAI

-- ---- from OAI.Geometry.DoublingHilbert.CoverTransfer ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open Set Metric
open scoped BigOperators
noncomputable section
namespace CompactBanach

theorem intrinsic_doubling_of_distortion36
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] {S : Set X} {L : ℕ}
    (hS : AmbientDoubling S L) (p : Y → X) (hp : ∀ y, p y ∈ S)
    {a : ℝ} (ha : 0 < a)
    (hd : ∀ y z, a * dist (p y) (p z) ≤ dist y z ∧
      dist y z ≤ 36 * a * dist (p y) (p z)) :
    ∀ x : Y, ∀ r : ℝ, 0 < r →
      ∃ centers : Finset Y, centers.card ≤ L ^ 8 ∧
        ∀ y : Y, dist y x < r → ∃ c ∈ centers, dist y c < r / 2 := by
  classical
  intro x r hr
  obtain ⟨c, _, hcard, hcov⟩ := ambient_iterated_cover hS 8 (hp x) (div_pos hr ha)
  let meets (z : c) : Prop := ∃ y : Y, dist y x < r ∧
    dist (p y) z.val < r / a / (2 : ℝ) ^ 8
  let chooseCenter (z : c) : Y := if hz : meets z then hz.choose else x
  let cs := c.attach.image chooseCenter
  refine ⟨cs, Finset.card_image_le.trans (by simpa using hcard), ?_⟩
  intro y hy
  have hy' : dist (p y) (p x) < r / a := (lt_div_iff₀ ha).mpr (by
    have h := (hd y x).1
    nlinarith)
  obtain ⟨z, hz, hyz⟩ := hcov (p y) (hp y) hy'
  have hm : meets ⟨z, hz⟩ := ⟨y, hy, hyz⟩
  have hc : dist (p (chooseCenter ⟨z, hz⟩)) z < r / a / (2 : ℝ) ^ 8 := by
    simp only [chooseCenter, dite_eq_left hm]
    exact hm.choose_spec.2
  refine ⟨chooseCenter ⟨z, hz⟩,
    Finset.mem_image.mpr ⟨⟨z, hz⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
  have htri := dist_triangle (p y) z (p (chooseCenter ⟨z, hz⟩))
  rw [dist_comm z] at htri
  have hbound : a * dist (p y) (p (chooseCenter ⟨z, hz⟩)) < r / 128 := by
    calc
      _ ≤ a * (dist (p y) z + dist (p (chooseCenter ⟨z, hz⟩)) z) :=
        mul_le_mul_of_nonneg_left htri ha.le
      _ < a * (r / a / (2 : ℝ) ^ 8 + r / a / (2 : ℝ) ^ 8) :=
        mul_lt_mul_of_pos_left (add_lt_add hyz hc) ha
      _ = r / 128 := by field_simp; ring
  have hu := (hd y (chooseCenter ⟨z, hz⟩)).2
  linarith

theorem range_doubling_of_distortion36
    {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] {S : Set X} {L : ℕ}
    (hS : AmbientDoubling S L) (p : Z → X) (hp : ∀ z, p z ∈ S)
    (f : Z → Y) {a : ℝ} (ha : 0 < a)
    (hd : ∀ z w, a * dist (p z) (p w) ≤ dist (f z) (f w) ∧
      dist (f z) (f w) ≤ 36 * a * dist (p z) (p w)) :
    DoublingAtMost (Set.range f) (L ^ 8) := by
  classical
  let q : Set.range f → Z := fun y => y.property.choose
  have hq (y : Set.range f) : f (q y) = y.val := y.property.choose_spec
  apply intrinsic_doubling_of_distortion36 hS (p ∘ q) (fun y => hp (q y)) ha
  intro y z
  simpa only [Function.comp_apply, hq, Subtype.dist_eq] using hd (q y) (q z)

end CompactBanach
end

end OAI

-- ---- from OAI.Geometry.DoublingHilbert.ClusterPlacement ----
namespace OAI

open Set Metric
open scoped BigOperators
noncomputable section
namespace CompactBanach
open DoublingHilbert

theorem cluster_placement {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (hB : ¬ FiniteDimensional ℝ B)
    (hS : AmbientDoubling constructedSet 76800)
    (s : Finset constructedSet) (v : B) {r : ℝ} (hr : 0 < r) :
    ∃ f : s → B, (∀ x, dist (f x) (r • v) ≤ r / 100) ∧
      DoublingAtMost (Set.range f) (76800 ^ 8) ∧
      ∃ a : ℝ, 0 < a ∧ ∀ x y : s,
        a * dist x y ≤ dist (f x) (f y) ∧
          dist (f x) (f y) ≤ 36 * a * dist x y := by
  classical
  let X : Finset RealL2 := s.image Subtype.val
  have hX : ∀ z ∈ X, z ∈ constructedSet := by
    intro z hz
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    exact x.property
  obtain ⟨T, hT⟩ := finite_placement hB X hX
  let M : ℝ := 1 + ∑ x : s, ‖T x.val.val‖
  have hM : 0 < M := by dsimp [M]; positivity
  have hxM (x : s) : ‖T x.val.val‖ ≤ M := by
    have ht := Finset.single_le_sum (fun (y : s) _ => norm_nonneg (T y.val.val))
      (Finset.mem_univ x)
    exact ht.trans (le_add_of_nonneg_left zero_le_one)
  let ρ : ℝ := r / (100 * M)
  have hρ : 0 < ρ := div_pos hr (mul_pos (by norm_num) hM)
  have hρM : ρ * M = r / 100 := by dsimp [ρ]; field_simp [ne_of_gt hM]
  let f : s → B := fun x => r • v + ρ • T x.val.val
  have hf (x y : s) : dist (f x) (f y) = ρ * dist (T x.val.val) (T y.val.val) := by
    dsimp [f]
    rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hρ]
  have hTs (x y : s) : dist x y / 6 ≤ dist (T x.val.val) (T y.val.val) ∧
      dist (T x.val.val) (T y.val.val) ≤ 6 * dist x y := by
    apply hT
    · exact Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩
    · exact Finset.mem_image.mpr ⟨y.val, y.property, rfl⟩
  have hd (x y : s) : (ρ / 6) * dist x y ≤ dist (f x) (f y) ∧
      dist (f x) (f y) ≤ 36 * (ρ / 6) * dist x y := by
    rw [hf]
    constructor
    · have hh := mul_le_mul_of_nonneg_left (hTs x y).1 hρ.le
      nlinarith
    · have hh := mul_le_mul_of_nonneg_left (hTs x y).2 hρ.le
      nlinarith
  refine ⟨f, ?_, ?_, ρ / 6, by positivity, hd⟩
  · intro x
    dsimp [f]
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    exact (mul_le_mul_of_nonneg_left (hxM x) hρ.le).trans_eq hρM
  · exact range_doubling_of_distortion36 hS (fun x : s => x.val.val)
      (fun x => x.val.property) f (by positivity : 0 < ρ / 6) hd

end CompactBanach
end

end OAI

-- ---- from OAI.Geometry.DoublingHilbert.ClusterScales ----
namespace OAI

open Set Metric
open scoped BigOperators
open Filter
open scoped Topology
noncomputable section
namespace CompactBanach

theorem clusterScale_pos (j : ℕ) : 0 < clusterScale j := by
  unfold clusterScale
  positivity

theorem clusterScale_tendsto : Tendsto clusterScale atTop (𝓝 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  exact h.comp (tendsto_add_atTop_nat 1)

                                            
theorem cluster_norm_bound {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {v z : B} (hv : ‖v‖ = 1) {j : ℕ}
    (hz : dist z (clusterScale j • v) ≤ clusterScale j / 100) :
    ‖z‖ ≤ (101 / 100 : ℝ) * clusterScale j := by
  have hcent : dist (clusterScale j • v) 0 = clusterScale j := by
    simp [dist_zero_right, norm_smul, hv, Real.norm_eq_abs, abs_of_pos (clusterScale_pos j)]
  have ht := dist_triangle z (clusterScale j • v) 0
  rw [dist_zero_right, hcent] at ht
  linarith

                                                                               
                                                                           
                                                                             
end CompactBanach
end

end OAI

-- ---- from OAI.Geometry.DoublingHilbert.ClusterCover ----
namespace OAI

open Set Metric
open scoped BigOperators
open Filter
open scoped Topology
noncomputable section
namespace CompactBanach

                                                                            
                                                                          
                                                                                
theorem compact_doubling_clusters
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (C : ℕ → Finset B) {v : B} (hv : ‖v‖ = 1)
    (hloc : ∀ j z, z ∈ C j → dist z (clusterScale j • v) ≤ clusterScale j / 100)
    {L : ℕ} (hC : ∀ j, DoublingAtMost (C j : Set B) L) :
    IsCompact ({0} ∪ ⋃ j : ℕ, (C j : Set B)) ∧
      DoublingAtMost ({0} ∪ ⋃ j : ℕ, (C j : Set B)) (1 + 5 * L ^ 2) := by
  refine ⟨compact_shrinking_union 0 C ?_,
    doubling_iff_ambient.mpr (ambient_doubling_clusters C hv hloc
      (fun j => doubling_iff_ambient.mp (hC j)))⟩
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (clusterScale_tendsto.eventually
      (gt_mem_nhds (show (0 : ℝ) < ε * (100 / 101) by positivity)))
  refine ⟨N, fun j hj z hz => ?_⟩
  rw [dist_zero_right]
  have hn := cluster_norm_bound hv (hloc j z hz)
  have ht := hN j hj
  linarith

end CompactBanach
end

end OAI

-- ---- from OAI.Geometry.DoublingHilbert.FiniteTargets ----
namespace OAI

open Set Metric
open scoped BigOperators
open Filter
open scoped Topology
noncomputable section
namespace CompactBanach

theorem euclidean_embedding_of_finite_dimensional
    {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : X → E) {a D : ℝ} (ha : 0 < a) (hD : 1 ≤ D)
    (hf : ∀ x y, a * dist x y ≤ dist (f x) (f y) ∧
      dist (f x) (f y) ≤ D * a * dist x y) :
    ∃ g : X → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
      ∃ b : ℝ, 0 < b ∧ ∃ A : ℝ, 1 ≤ A ∧ ∀ x y,
        b * dist x y ≤ dist (g x) (g y) ∧
          dist (g x) (g y) ≤ A * b * dist x y := by
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean
  let U : ℝ := ‖e.toContinuousLinearMap‖ + 1
  let V : ℝ := ‖e.symm.toContinuousLinearMap‖ + 1
  have hU : 1 ≤ U := le_add_of_nonneg_left (norm_nonneg _)
  have hV : 1 ≤ V := le_add_of_nonneg_left (norm_nonneg _)
  have hVp : 0 < V := lt_of_lt_of_le zero_lt_one hV
  have hUp : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hu (x y : E) : dist (e x) (e y) ≤ U * dist x y := by
    have h := e.toContinuousLinearMap.lipschitz.dist_le_mul x y
    calc
      _ ≤ ‖e.toContinuousLinearMap‖ * dist x y := h
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [U]; linarith) dist_nonneg
  have hl (x y : E) : dist x y ≤ V * dist (e x) (e y) := by
    have h := e.symm.toContinuousLinearMap.lipschitz.dist_le_mul (e x) (e y)
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at h
    calc
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * dist (e x) (e y) := h
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [V]; linarith) dist_nonneg
  have hDU : 1 ≤ D * U := by nlinarith
  have hA : 1 ≤ D * U * V := by nlinarith
  refine ⟨e ∘ f, a / V, div_pos ha hVp, D * U * V, hA, ?_⟩
  intro x y
  dsimp only [Function.comp_apply]
  constructor
  · have hh := (hf x y).1.trans (hl (f x) (f y))
    calc
      _ = (a * dist x y) / V := by ring
      _ ≤ _ := (div_le_iff₀ hVp).mpr (by nlinarith only [hh])
  · calc
      _ ≤ U * dist (f x) (f y) := hu _ _
      _ ≤ U * (D * a * dist x y) := mul_le_mul_of_nonneg_left (hf x y).2 hUp.le
      _ = (D * U * V) * (a / V) * dist x y := by field_simp

end CompactBanach
end

end OAI

-- ---- from OAI.Geometry.DoublingHilbert.CompactBanach ----
namespace OAI

open Set Metric
open scoped BigOperators
open Filter
open scoped Topology
noncomputable section
universe u v
namespace CompactBanach

theorem main : ∃ Λ : ℕ, ∀ (B : Type u) [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B], ¬ FiniteDimensional ℝ B →
    ∃ K : Set B, IsCompact K ∧ DoublingAtMost K Λ ∧
      ∀ (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E], ¬ AdmitsBiLipschitzEmbedding K E := by
  classical
  refine ⟨1 + 5 * (76800 ^ 8) ^ 2, ?_⟩
  intro B _ _ _ hB
  have hS : AmbientDoubling DoublingHilbert.constructedSet 76800 :=
    doubling_iff_ambient.mp (fun x r hr => DoublingHilbert.constructedSet_cover x hr)
                                                                                     
  have hw (j : ℕ) := finite_witness_card (Nat.unpair j).1
    (A := ((Nat.unpair j).2 : ℝ) + 1) (le_add_of_nonneg_left (Nat.cast_nonneg _))
  choose X hXcard hX using hw
  obtain ⟨v, hv, hvcoord⟩ := exists_auerbach_vectors (ι := Unit) hB
  have hvunit : ‖v ()‖ = 1 := by
    apply le_antisymm (hv ())
    simpa using hvcoord (fun _ => 1) ()
  have hp (j : ℕ) := cluster_placement hB hS (X j) (v ()) (clusterScale_pos j)
  choose f hloc hdoubling a ha hd using hp
  let C : ℕ → Finset B := fun j => Finset.univ.image (f j)
  have hCset (j : ℕ) : (C j : Set B) = Set.range (f j) := by
    ext z
    simp [C]
  have hCloc : ∀ j z, z ∈ C j →
      dist z (clusterScale j • v ()) ≤ clusterScale j / 100 := by
    intro j z hz
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    exact hloc j x
  have hCdouble : ∀ j, DoublingAtMost (C j : Set B) (76800 ^ 8) := by
    intro j
    rw [hCset]
    exact hdoubling j
  let K : Set B := {0} ∪ ⋃ j : ℕ, (C j : Set B)
  obtain ⟨hcompact, hdouble⟩ := compact_doubling_clusters C hvunit hCloc hCdouble
  refine ⟨K, hcompact, hdouble, ?_⟩
  intro E _ _ _ hF
  obtain ⟨F, b, hb, D, hD, hF⟩ := hF
  obtain ⟨g, c, hc, A, hA, hg⟩ := euclidean_embedding_of_finite_dimensional F hb hD hF
  obtain ⟨n, hn⟩ := exists_nat_gt (36 * A)
  let j : ℕ := Nat.pair (Module.finrank ℝ E) n
  have hjdim : (Nat.unpair j).1 = Module.finrank ℝ E := by simp [j]
  have hjn : (Nat.unpair j).2 = n := by simp [j]
  let intoK : X j → K := fun x =>
    ⟨f j x, Or.inr (Set.mem_iUnion.mpr ⟨j,
      Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩)⟩
  have hbad := hX j
  rw [hjdim, hjn] at hbad
  apply hbad
  refine ⟨g ∘ intoK, c * a j, mul_pos hc (ha j), ?_⟩
  intro x y
  have hgg := hg (intoK x) (intoK y)
  change c * dist (f j x) (f j y) ≤ dist (g (intoK x)) (g (intoK y)) ∧
    dist (g (intoK x)) (g (intoK y)) ≤ A * c * dist (f j x) (f j y) at hgg
  dsimp only [Function.comp_apply]
  constructor
  · calc
      _ = c * (a j * dist x y) := by ring
      _ ≤ c * dist (f j x) (f j y) := mul_le_mul_of_nonneg_left (hd j x y).1 hc.le
      _ ≤ _ := hgg.1
  · have hApos : 0 ≤ A := le_trans zero_le_one hA
    have hn' : 36 * A ≤ (n : ℝ) + 1 := by linarith
    calc
      _ ≤ A * c * dist (f j x) (f j y) := hgg.2
      _ ≤ A * c * (36 * a j * dist x y) :=
        mul_le_mul_of_nonneg_left (hd j x y).2 (mul_nonneg hApos hc.le)
      _ = (36 * A) * (c * a j) * dist x y := by ring
      _ ≤ ((n : ℝ) + 1) * (c * a j) * dist x y :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hn' (mul_nonneg hc.le (ha j).le)) dist_nonneg

end CompactBanach
end

end OAI

-- ---- mission target ----
open OAI OAI.CompactBanach
universe u v
open Set Metric
open scoped BigOperators
open Filter
open scoped Topology

theorem solution : ∃ Λ : ℕ, ∀ (B : Type u) [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B], ¬ FiniteDimensional ℝ B →
    ∃ K : Set B, IsCompact K ∧ DoublingAtMost K Λ ∧
      ∀ (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E], ¬ AdmitsBiLipschitzEmbedding K E := by
  first
    | exact OAI.CompactBanach.main
    | (apply OAI.CompactBanach.main <;> assumption)
    | (intros; apply OAI.CompactBanach.main <;> assumption)
