-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.neighborhood_packing
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:53:38.585166+00:00
-- url     : https://prove2.me/submissions/59847d58-189b-483a-984a-2e7b2548b756

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/Packing.lean:L17-L128
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.neighborhood_packing. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_edgeMass_restrict
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_edgeMass_smul

-- ---- from OAI.Combinatorics.CliqueFree.WeightedGraph ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

omit [Fintype V] in
lemma mass_nonneg {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (A : Finset V) :
    0 ≤ mass w A := sum_nonneg fun v _ ↦ hw v

lemma crossMass_factor (G : SimpleGraph V) (w : V → ℝ) (A B : Finset V) :
    crossMass G w A B = ∑ u ∈ A, w u * mass w (B ∩ neighbors G u) := by
  classical
  unfold crossMass mass
  apply sum_congr rfl
  intro u _
  rw [← filter_mem_eq_inter]
  simp only [sum_filter, mem_neighbors, mul_sum, mul_ite, mul_zero]

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.Lottery ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence
universe u
namespace Lottery
variable {α β : Type u}

lemma expect_append (L K : Law α) (f : α → ℝ) : expect (L++K) f = expect L f + expect K f := by
  simp [expect]

lemma expect_mul (L : Law α) (a : ℝ) (f : α → ℝ) :
    expect L (fun z ↦ a*f z) = a * expect L f := by
  induction L with
  | nil => simp
  | cons z L ih =>
    rcases z with ⟨p,a⟩
    simp only [expect_cons,ih]
    ring

lemma expect_transform (p : ℝ) (f : α → β) (L : Law α) (g : β → ℝ) :
    expect (transform p f L) g = p * expect L (g ∘ f) := by
  induction L with
  | nil => simp [transform]
  | cons z L ih =>
    rcases z with ⟨q,a⟩
    simp only [transform,List.map_cons,expect_cons,Function.comp_apply] at *
    rw [ih]
    ring

lemma total_transform (p : ℝ) (f : α → β) (L : Law α) :
    total (transform p f L) = p * total L := expect_transform _ _ _ _

lemma positive_transform {p : ℝ} (hp : 0 ≤ p) (f : α → β) {L : Law α} (hL : Positive L) :
    Positive (transform p f L) := by
  intro z hz
  obtain ⟨y,hy,rfl⟩ := List.mem_map.1 hz
  exact mul_nonneg hp (hL y hy)

lemma positive_append {L K : Law α} (hL : Positive L) (hK : Positive K) : Positive (L++K) := by
  intro z hz
  rcases List.mem_append.1 hz with hz | hz
  · exact hL z hz
  · exact hK z hz

end Lottery

end CliqueFreeIndependence

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.MultiplierLaw ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence
universe u
namespace WeightedGraph
open Lottery
variable {V : Type u} [Fintype V]

lemma crossMass_restrict (G : SimpleGraph V) (w : V → ℝ) (A : Finset V) :
    crossMass G w A A = ∑ v ∈ A, w v * mass w (A ∩ neighbors G v) := crossMass_factor G w A A

lemma edgeMass_restrict_le (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (A : Finset V) {t : ℝ} (hA : ∀ v ∈ A, mass w (A ∩ neighbors G v) ≤ t) :
    edgeMass G (restrict A w) ≤ t * mass w A / 2 := by
  rw [edgeMass_restrict,crossMass_restrict]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ ≤ ∑ v ∈ A, w v*t := sum_le_sum fun v hv ↦ mul_le_mul_of_nonneg_left (hA v hv) (hw v)
    _ = _ := by rw [← sum_mul]; exact mul_comm _ _

lemma expectedEdges_transform (G : SimpleGraph V) (w : V → ℝ) (L : Law (V → ℝ)) (p k : ℝ) :
    expectedEdges G w (transform p (fun m v ↦ k*m v) L) = p*k^2*expectedEdges G w L := by
  unfold expectedEdges
  rw [expect_transform]
  have he (m : V → ℝ) : edgeMass G (fun v ↦ w v*(k*m v)) = k^2*edgeMass G (fun v ↦ w v*m v) := by
    convert edgeMass_smul G (fun v ↦ w v*m v) k using 2
    ext v
    ring
  change p * expect L (fun m ↦ edgeMass G (fun v ↦ w v*(k*m v))) = _
  simp_rw [he]
  rw [expect_mul]
  ring

omit [Fintype V] in
lemma mean_transform (L : Law (V → ℝ)) (p k : ℝ) (v : V) :
    expect (transform p (fun m v ↦ k*m v) L) (fun m ↦ m v) = p*k*expect L (fun m ↦ m v) := by
  rw [expect_transform]
  change p * expect L (fun m ↦ k*m v) = _
  rw [expect_mul]
  ring

omit [Fintype V] in
lemma bounded_transform {L : Law (V → ℝ)} {A : Finset V} {b B k : ℝ}
    (hL : BoundedOn L A b) (hk : 0 ≤ k) (hkb : k*b ≤ B) (p : ℝ) :
    BoundedOn (transform p (fun m v ↦ k*m v) L) A B := by
  intro z hz
  obtain ⟨y,hy,rfl⟩ := List.mem_map.1 hz
  obtain ⟨hby,hsy⟩ := hL y hy
  exact ⟨fun v ↦ ⟨mul_nonneg hk (hby v).1,(mul_le_mul_of_nonneg_left (hby v).2 hk).trans hkb⟩,
    fun v hv ↦ by simp [hsy v hv]⟩

omit [Fintype V] in
lemma bounded_append {L K : Law (V → ℝ)} {A B S : Finset V} {b : ℝ}
    (hL : BoundedOn L A b) (hK : BoundedOn K B b) (hA : A ⊆ S) (hB : B ⊆ S) :
    BoundedOn (L++K) S b := by
  intro z hz
  rcases List.mem_append.1 hz with hz | hz
  · exact ⟨(hL z hz).1,fun v hv ↦ (hL z hz).2 v (fun h ↦ hv (hA h))⟩
  · exact ⟨(hK z hz).1,fun v hv ↦ (hK z hz).2 v (fun h ↦ hv (hB h))⟩

end WeightedGraph
end CliqueFreeIndependence

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.Packing ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph
open Lottery
universe u
variable {V : Type u} [Fintype V]

/-- Greedy disjoint-neighborhood packing, with a subprobability lottery. The additional
zero outcome is inserted only at the end. -/
lemma neighborhood_packing (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 < w v)
    (A : Finset V) {s η b B : ℝ} (hs : 0 < s) (hη : 0 < η) (hb : 0 ≤ b)
    (hB : 2 ≤ B) (hbig : 2/η*b ≤ B) (_hAs : mass w A ≤ s)
    (hlocal : ∀ (R : Finset V), R ⊆ A → ∀ v ∈ R,
      η*s < mass w (R ∩ neighbors G v) →
      ∃ L : Law (V → ℝ), IsProb L ∧ BoundedOn L (R ∩ neighbors G v) b ∧
        (∀ u, expect L (fun m ↦ m u) = if u ∈ R ∩ neighbors G v then 1 else 0) ∧
        expectedEdges G w L ≤ η * (mass w (R ∩ neighbors G v))^2) :
    ∃ L : Law (V → ℝ), Positive L ∧ total L ≤ 1/2+mass w A/(2*s) ∧
      BoundedOn L A B ∧
      (∀ u, expect L (fun m ↦ m u) = if u ∈ A then 1 else 0) ∧
      expectedEdges G w L ≤ 2*η*s*mass w A := by
  classical
  have hw0 := fun v ↦ (hw v).le
  suffices hpack : ∀ R : Finset V, R ⊆ A →
      ∃ L : Law (V → ℝ), Positive L ∧ total L ≤ 1/2+mass w R/(2*s) ∧
        BoundedOn L R B ∧
        (∀ u, expect L (fun m ↦ m u) = if u ∈ R then 1 else 0) ∧
        expectedEdges G w L ≤ 2*η*s*mass w R by exact hpack A Subset.rfl
  intro R
  refine Finset.strongInductionOn R ?_
  intro R ih hRA
  by_cases hsmall : ∀ v ∈ R, mass w (R ∩ neighbors G v) ≤ η*s
  · let m : V → ℝ := restrict R (fun _ ↦ 2)
    let L : Law (V → ℝ) := [(1/2,m)]
    refine ⟨L,?_,?_,?_,?_,?_⟩
    · intro z hz
      have hz' : z = (1/2,m) := by simpa [L] using hz
      rw [hz']; norm_num
    · have hr := div_nonneg (mass_nonneg hw0 R) (by positivity : 0 ≤ 2*s)
      simp only [L,total,expect_singleton,mul_one]
      linarith
    · intro z hz
      have hz' : z = (1/2,m) := by simpa [L] using hz
      rw [hz']
      refine ⟨?_,?_⟩
      · intro v
        dsimp [m,restrict]
        split_ifs <;> constructor <;> linarith
      · intro v hv
        simp [m,restrict,hv]
    · intro v
      simp [L,m,restrict]
    · have he := edgeMass_restrict_le G hw0 R hsmall
      have heq : (fun v ↦ w v*m v) = fun v ↦ 2*restrict R w v := by
        funext v
        by_cases hv : v ∈ R <;> simp [m,restrict,hv,mul_comm]
      simp only [L,expectedEdges,expect_singleton,heq,edgeMass_smul]
      have hn := mul_nonneg (mul_nonneg hη.le hs.le) (mass_nonneg hw0 R)
      nlinarith
  · push Not at hsmall
    obtain ⟨v,hv,hvlarge⟩ := hsmall
    let D := R ∩ neighbors G v
    have hDR : D ⊆ R := inter_subset_left
    have hDpos : 0 < mass w D := (mul_pos hη hs).trans hvlarge
    have hDne : D.Nonempty := by
      by_contra hn
      have he : D = ∅ := not_nonempty_iff_eq_empty.1 hn
      simp [he,mass] at hDpos
    obtain ⟨L,hLp,hLb,hLm,hLe⟩ := hlocal R hRA v hv hvlarge
    obtain ⟨K,hKp,hKt,hKb,hKm,hKe⟩ := ih (R \ D) (sdiff_ssubset hDR hDne) (sdiff_subset.trans hRA)
    let p := mass w D / (2*s)
    have hp : 0 < p := div_pos hDpos (by positivity)
    have hpη : η/2 < p := by
      apply (lt_div_iff₀ (by positivity : 0 < 2*s)).2
      nlinarith only [hvlarge]
    have hik : (1/p)*b ≤ B := by
      have hi : 1/p ≤ 2/η := by
        apply (div_le_div_iff₀ hp hη).2
        linarith
      exact (mul_le_mul_of_nonneg_right hi hb).trans hbig
    let J := transform p (fun m u ↦ (1/p)*m u) L
    have hJp : Positive J := positive_transform hp.le _ hLp.1
    have hJb : BoundedOn J D B := bounded_transform hLb (one_div_nonneg.2 hp.le) hik p
    have hpart : mass w (R \ D) + mass w D = mass w R := by
      exact sum_sdiff hDR
    have hJt : total J = p := by
      rw [total_transform,hLp.2,mul_one]
    have hJm (u : V) : expect J (fun m ↦ m u) = if u ∈ D then 1 else 0 := by
      rw [mean_transform,hLm,mul_one_div_cancel hp.ne',one_mul]
    have hJe : expectedEdges G w J ≤ 2*η*s*mass w D := by
      rw [expectedEdges_transform]
      have he := mul_le_mul_of_nonneg_left hLe (by positivity : 0 ≤ p*(1/p)^2)
      have hid : p*(1/p)^2*(η*(mass w D)^2) = 2*η*s*mass w D := by
        dsimp [p]
        field_simp
      exact he.trans_eq hid
    refine ⟨J++K,positive_append hJp hKp,?_,bounded_append hJb hKb hDR sdiff_subset,?_,?_⟩
    · change expect (J++K) (fun _ ↦ 1) ≤ _
      rw [expect_append]
      change total J + total K ≤ _
      rw [hJt]
      dsimp [p]
      have hparts : mass w D/(2*s) + mass w (R \ D)/(2*s) = mass w R/(2*s) := by
        rw [← add_div]
        congr 1
        linarith only [hpart]
      linarith only [hKt,hparts]
    · intro u
      rw [expect_append,hJm,hKm]
      by_cases hu : u ∈ D
      · have huR := hDR hu
        simp [hu,huR]
      · by_cases huR : u ∈ R <;> simp [hu,huR]
    · change expect (J++K) _ ≤ _
      rw [expect_append]
      change expectedEdges G w J + expectedEdges G w K ≤ _
      calc
        _ ≤ 2*η*s*mass w D + 2*η*s*mass w (R \ D) := add_le_add hJe hKe
        _ = _ := by rw [← mul_add,add_comm (mass w D),hpart]

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Lottery


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.neighborhood_packing.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.neighborhood_packing.{u}
