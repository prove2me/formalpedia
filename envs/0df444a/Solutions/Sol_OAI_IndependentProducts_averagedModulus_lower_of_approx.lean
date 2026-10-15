-- Prove2me | solution 1 for OAI.IndependentProducts.averagedModulus_lower_of_approx
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:19:36.146441+00:00
-- url     : https://prove2.me/submissions/56475a7b-79bd-40ab-b0e5-1d9dbdd501d9

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/MidpointModulus.lean:L77-L127
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.averagedModulus_lower_of_approx. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianExcess
import Definitions.Def_OAI_Analysis_ProductSpaces_RandomSigns
import Definitions.Def_OAI_Analysis_ProductSpaces_MidpointModulus

-- ---- from OAI.Analysis.ProductSpaces.MidpointModulus ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uX

namespace IndependentProducts
section MidpointGeometry
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma midpointGain_nonneg (t : ℝ) (x y : X) : 0 ≤ midpointGain t x y := by
  have h := norm_add_le (x + t • y) (x - t • y)
  have he : (x + t • y) + (x - t • y) = (2 : ℝ) • x := by module
  rw [he, norm_smul] at h
  norm_num at h
  unfold midpointGain
  linarith

lemma midpointGain_le (t : ℝ) (x y : X) : midpointGain t x y ≤ |t| * ‖y‖ := by
  have hp := norm_add_le x (t • y)
  have hm := norm_sub_le x (t • y)
  simp only [norm_smul, Real.norm_eq_abs] at hp hm
  unfold midpointGain
  linarith

lemma exists_unit_of_not_finiteDimensional (hdim : ¬ FiniteDimensional ℝ X) :
    ∃ x : X, ‖x‖ = 1 := by
  have : Nontrivial X := not_subsingleton_iff_nontrivial.mp (fun h => by
    let := h
    exact hdim inferInstance)
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  refine ⟨‖x‖⁻¹ • x, ?_⟩
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

lemma cofinite_exists_unit (hdim : ¬ FiniteDimensional ℝ X) (F : Submodule ℝ X)
    (hF : F ∈ CofiniteSubspaces X) : ∃ y : X, y ∈ F ∧ ‖y‖ = 1 := by
  have hne : F ≠ ⊥ := by
    intro hbot
    let : FiniteDimensional ℝ (X ⧸ F) := hF.2
    have hinj : Function.Injective F.mkQ := LinearMap.ker_eq_bot.mp (by simpa using hbot)
    exact hdim (FiniteDimensional.of_injective F.mkQ hinj)
  obtain ⟨y, hy, hny⟩ := F.ne_bot_iff.mp hne
  refine ⟨‖y‖⁻¹ • y, F.smul_mem _ hy, ?_⟩
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hny)]

lemma averagedModulus_lower_of_approx (hdim : ¬ FiniteDimensional ℝ X) (t L : ℝ)
    (h : ∀ x : X, ‖x‖ = 1 → ∀ ε : ℝ, 0 < ε →
      ∃ F ∈ CofiniteSubspaces X, ∀ y ∈ F, 1 ≤ ‖y‖ → L - ε ≤ midpointGain t x y) :
    L ≤ averagedMidpointModulus X (normSeminorm ℝ X) t := by
  let D : X → Submodule ℝ X → Set ℝ := fun x F =>
    {b | ∃ y : X, y ∈ F ∧ 1 ≤ ‖y‖ ∧ b = midpointGain t x y}
  let S : X → Set ℝ := fun x => {a | ∃ F ∈ CofiniteSubspaces X, a = sInf (D x F)}
  have hDne : ∀ x F, F ∈ CofiniteSubspaces X → (D x F).Nonempty := by
    intro x F hF
    obtain ⟨y, hy, hn⟩ := cofinite_exists_unit hdim F hF
    exact ⟨_, y, hy, hn.ge, rfl⟩
  have hDbdd : ∀ x F, BddBelow (D x F) := by
    intro x F
    refine ⟨0, ?_⟩
    rintro b ⟨y, hy, hn, rfl⟩
    exact midpointGain_nonneg t x y
  have hSbdd : ∀ x, BddAbove (S x) := by
    intro x
    refine ⟨|t|, ?_⟩
    rintro a ⟨F, hF, rfl⟩
    obtain ⟨y, hy, hn⟩ := cofinite_exists_unit hdim F hF
    have hm := csInf_le (hDbdd x F) (show midpointGain t x y ∈ D x F from ⟨y, hy, hn.ge, rfl⟩)
    have hg := midpointGain_le t x y
    rw [hn, mul_one] at hg
    exact hm.trans hg
  have hDform : ∀ x : X, ‖x‖ = 1 → ∀ F : Submodule ℝ X,
      {b | ∃ y : X, y ∈ F ∧ 1 ≤ (normSeminorm ℝ X) y ∧ b =
        ((normSeminorm ℝ X) (x + t • y) + (normSeminorm ℝ X) (x - t • y)) / 2 - 1} = D x F := by
    intro x hx F
    change {b | ∃ y : X, y ∈ F ∧ 1 ≤ ‖y‖ ∧ b = (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1} = _
    simp only [D, midpointGain, hx]
  unfold averagedMidpointModulus
  have hcne : {r | ∃ x : X, (normSeminorm ℝ X) x = 1 ∧ r = sSup {a | ∃ F ∈ CofiniteSubspaces X,
      a = sInf {b | ∃ y : X, y ∈ F ∧ 1 ≤ (normSeminorm ℝ X) y ∧ b =
        ((normSeminorm ℝ X) (x + t • y) + (normSeminorm ℝ X) (x - t • y)) / 2 - 1}}}.Nonempty := by
    obtain ⟨x, hx⟩ := exists_unit_of_not_finiteDimensional hdim
    exact ⟨_, x, hx, rfl⟩
  apply le_csInf hcne
  rintro r ⟨x, hx, rfl⟩
  change ‖x‖ = 1 at hx
  simp_rw [hDform x hx]
  change L ≤ sSup (S x)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨F, hF, hFy⟩ := h x hx ε hε
  have hlow : L - ε ≤ sInf (D x F) := by
    apply le_csInf (hDne x F hF)
    rintro b ⟨y, hy, hn, rfl⟩
    exact hFy y hy hn
  have hup : sInf (D x F) ≤ sSup (S x) := le_csSup (hSbdd x) ⟨F, hF, rfl⟩
  linarith

end MidpointGeometry
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uX
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem solution (hdim : ¬ FiniteDimensional ℝ X) (t L : ℝ)
    (h : ∀ x : X, ‖x‖ = 1 → ∀ ε : ℝ, 0 < ε →
      ∃ F ∈ CofiniteSubspaces X, ∀ y ∈ F, 1 ≤ ‖y‖ → L - ε ≤ midpointGain t x y) :
    L ≤ averagedMidpointModulus X (normSeminorm ℝ X) t := by
  first
    | exact OAI.IndependentProducts.averagedModulus_lower_of_approx hdim t L h
    | exact OAI.IndependentProducts.averagedModulus_lower_of_approx
    | (apply OAI.IndependentProducts.averagedModulus_lower_of_approx <;> assumption)
    | (intros; apply OAI.IndependentProducts.averagedModulus_lower_of_approx <;> assumption)
