-- Prove2me | solution 1 for OAI.IndependentProducts.bounded_tree_no_equivalent_auc
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T03:58:04.824543+00:00
-- url     : https://prove2.me/submissions/a0e9347c-f57d-4998-9e59-2733bce0c227

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/TreeObstruction.lean:L162-L239
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.bounded_tree_no_equivalent_auc. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Theorems.Thm_OAI_IndependentProducts_oneSided_pos_subspace
import Theorems.Thm_OAI_IndependentProducts_seminorm_radial_growth
import Theorems.Thm_OAI_IndependentProducts_weaklyNull_approx_cofinite

-- ---- from OAI.Analysis.ProductSpaces.TreeObstruction ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uX

namespace IndependentProducts

section AbstractObstruction

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

end AbstractObstruction
end IndependentProducts

namespace IndependentProducts
section RadialGrowth
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma seminorm_normalize (N : Seminorm ℝ X) {x : X} (hx : 0 < N x) :
    N ((N x)⁻¹ • x) = 1 := by
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx)]
  exact inv_mul_cancel₀ hx.ne'

lemma seminorm_unit_subspace_growth (N : Seminorm ℝ X) {x : X} (hx : N x = 1)
    (F : Submodule ℝ X) {t γ : ℝ} (ht : 0 < t) (hγ : 0 ≤ γ)
    (hg : ∀ w ∈ F, N w = 1 → 1 + γ ≤ N (x + t • w))
    {z : X} (hz : z ∈ F) (hNz : t ≤ N z) : 1 + γ ≤ N (x + z) := by
  have hzp : 0 < N z := ht.trans_le hNz
  have hw := hg ((N z)⁻¹ • z) (F.smul_mem _ hz) (seminorm_normalize N hzp)
  have hr := seminorm_radial_growth N hx ht hNz hγ hw
  simpa only [smul_smul, mul_inv_cancel₀ hzp.ne', one_smul] using hr

lemma oneSided_pos_local_growth (N : Seminorm ℝ X) {t : ℝ} (ht : 0 < t)
    (hδ : 0 < oneSidedModulus X N t) {x : X} (hx : 0 < N x) :
    ∃ F ∈ CofiniteSubspaces X, ∀ z ∈ F, t * N x ≤ N z →
      (1 + oneSidedModulus X N t / 2) * N x ≤ N (x + z) := by
  obtain ⟨F, hF, hg⟩ := oneSided_pos_subspace N hδ (seminorm_normalize N hx)
  refine ⟨F, hF, ?_⟩
  intro z hz hNz
  have hnz' : t ≤ N ((N x)⁻¹ • z) := by
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx)]
    exact (le_inv_mul_iff₀ hx).mpr (by simpa [mul_comm] using hNz)
  have hh := seminorm_unit_subspace_growth N (seminorm_normalize N hx) F ht
    (by linarith : 0 ≤ oneSidedModulus X N t / 2) hg (F.smul_mem (N x)⁻¹ hz) hnz'
  have hm := mul_le_mul_of_nonneg_right hh hx.le
  rw [← smul_add, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx)] at hm
  simpa only [mul_assoc, mul_left_comm (N x)⁻¹, inv_mul_cancel₀ hx.ne', mul_one] using hm

end RadialGrowth
end IndependentProducts

namespace IndependentProducts
section TreeObstruction
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The complete deterministic branch-growth obstruction. Its hypotheses concern the tree,
not the existence or nonexistence of any renorming. -/
theorem bounded_tree_no_equivalent_auc (P : Vertex → X) (hP : ∀ v, ‖P v‖ = 1)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hsize : ∀ v n, ‖P (child v n) - P v‖ = ρ)
    (hweak : ∀ v, WeaklyNull (fun n => P (child v n) - P v)) :
    ∀ N : Seminorm ℝ X, IsEquivalentNorm X N → ¬ IsAUC X N := by
  intro N hN hauc
  obtain ⟨a, b, ha, hab, hbound⟩ := hN
  have hb : 0 < b := ha.trans_le hab
  have hPa : ∀ v, a ≤ N (P v) := fun v => by
    simpa only [hP, mul_one] using (hbound (P v)).1
  have hPb : ∀ v, N (P v) ≤ b := fun v => by
    simpa only [hP, mul_one] using (hbound (P v)).2
  let t : ℝ := a * ρ / (2 * b)
  have ht : 0 < t := div_pos (mul_pos ha hρ) (by positivity)
  let δ := oneSidedModulus X N t
  have hδ : 0 < δ := hauc t ht
  have hstep : ∀ v, ∃ n, (1 + δ / 4) * N (P v) ≤ N (P (child v n)) := by
    intro v
    have hv : 0 < N (P v) := ha.trans_le (hPa v)
    obtain ⟨F, hF, hg⟩ := oneSided_pos_local_growth N ht hδ hv
    let ε := min (a * ρ / (2 * b)) (δ * N (P v) / (4 * b))
    have hε : 0 < ε := lt_min ht (div_pos (mul_pos hδ hv) (by positivity))
    obtain ⟨n, z, hz, herr⟩ := (weaklyNull_approx_cofinite (hweak v) F hF hε).exists
    let D := P (child v n) - P v
    have herr' : ‖D - z‖ < ε := herr
    have herr₁ : b * ‖D - z‖ < a * ρ / 2 := by
      calc
        b * ‖D - z‖ < b * (a * ρ / (2 * b)) :=
          mul_lt_mul_of_pos_left (herr'.trans_le (min_le_left _ _)) hb
        _ = a * ρ / 2 := by field_simp
    have herr₂ : b * ‖D - z‖ < δ * N (P v) / 4 := by
      calc
        b * ‖D - z‖ < b * (δ * N (P v) / (4 * b)) :=
          mul_lt_mul_of_pos_left (herr'.trans_le (min_le_right _ _)) hb
        _ = δ * N (P v) / 4 := by field_simp
    have hD : a * ρ ≤ N D := by simpa only [D, hsize] using (hbound D).1
    have hNz : a * ρ / 2 ≤ N z := by
      have hh : N D ≤ N (D - z) + N z := by
        simpa only [sub_add_cancel] using map_add_le_add N (D - z) z
      have he := (hbound (D - z)).2
      linarith
    have hrad : t * N (P v) ≤ N z := by
      calc
        t * N (P v) ≤ t * b := mul_le_mul_of_nonneg_left (hPb v) ht.le
        _ = a * ρ / 2 := by dsimp [t]; field_simp
        _ ≤ N z := hNz
    have hgain := hg z hz hrad
    have htri : N (P v + z) ≤ N (P (child v n)) + b * ‖D - z‖ := by
      calc
        N (P v + z) = N (P (child v n) + (z - D)) := by congr 1; dsimp [D]; abel
        _ ≤ N (P (child v n)) + N (z - D) := map_add_le_add N _ _
        _ ≤ N (P (child v n)) + b * ‖D - z‖ := by
          simpa only [norm_sub_rev z D] using add_le_add (le_refl (N (P (child v n)))) (hbound (z - D)).2
    refine ⟨n, ?_⟩
    change (1 + δ / 2) * N (P v) ≤ N (P v + z) at hgain
    nlinarith
  have hq : 1 < 1 + δ / 4 := by linarith
  have hiter : ∀ k : ℕ, ∃ v, a * (1 + δ / 4) ^ k ≤ N (P v) := by
    intro k
    induction k with
    | zero => exact ⟨[], by simpa using hPa []⟩
    | succ k ih =>
      obtain ⟨v, hv⟩ := ih
      obtain ⟨n, hn⟩ := hstep v
      refine ⟨child v n, ?_⟩
      calc
        a * (1 + δ / 4) ^ (k + 1) = (1 + δ / 4) * (a * (1 + δ / 4) ^ k) := by
          rw [pow_succ]; ring
        _ ≤ (1 + δ / 4) * N (P v) := mul_le_mul_of_nonneg_left hv (by linarith)
        _ ≤ N (P (child v n)) := hn
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (b / a) hq
  obtain ⟨v, hv⟩ := hiter k
  have hk' : b < a * (1 + δ / 4) ^ k := by
    have := (div_lt_iff₀ ha).mp hk
    nlinarith
  linarith [hPb v]

end TreeObstruction
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uX
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem solution (P : Vertex → X) (hP : ∀ v, ‖P v‖ = 1)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hsize : ∀ v n, ‖P (child v n) - P v‖ = ρ)
    (hweak : ∀ v, WeaklyNull (fun n => P (child v n) - P v)) :
    ∀ N : Seminorm ℝ X, IsEquivalentNorm X N → ¬ IsAUC X N := by
  first
    | exact OAI.IndependentProducts.bounded_tree_no_equivalent_auc P hP hρ hsize hweak
    | exact OAI.IndependentProducts.bounded_tree_no_equivalent_auc
    | (apply OAI.IndependentProducts.bounded_tree_no_equivalent_auc <;> assumption)
    | (intros; apply OAI.IndependentProducts.bounded_tree_no_equivalent_auc <;> assumption)
