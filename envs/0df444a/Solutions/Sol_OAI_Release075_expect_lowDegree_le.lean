-- Prove2me | solution 1 for OAI.Release075.expect_lowDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:16:57.449362+00:00
-- url     : https://prove2.me/submissions/cdb97c13-d202-48c3-a4a6-9e2a1224b787

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Incidence.lean:L334-L364
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.expect_lowDegree_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Theorems.Thm_OAI_Release075_expect_centered_sum_sq
import Theorems.Thm_OAI_Release075_puncturedIncidence_iff

-- ---- from OAI.GroupTheory.Hyperbolic.Incidence ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
namespace OAI

namespace Release075
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

theorem expect_low_indicator_le {Ω : Type*} [Fintype Ω]
    (X : Ω → ℝ) (μ t : ℝ) (ht : t < μ) :
    (𝔼 ω, if X ω < t then (1 : ℝ) else 0) ≤
      (𝔼 ω, (X ω - μ)^2) / (μ-t)^2 := by
  classical
  have hd : 0 < (μ-t)^2 := sq_pos_of_pos (sub_pos.mpr ht)
  rw [le_div_iff₀ hd, Finset.expect_mul]
  apply Finset.expect_le_expect
  intro ω _
  split_ifs with h
  · have hh : (μ-t)^2 ≤ (μ-X ω)^2 :=
      (sq_le_sq₀ (by linarith : 0 ≤ μ-t) (by linarith : 0 ≤ μ-X ω)).mpr (by linarith)
    nlinarith
  · simpa only [zero_mul] using sq_nonneg (X ω - μ)

theorem expect_bernoulli_sum_sq_le {I D : Type*} [Fintype I] [DecidableEq I]
    [Fintype D] [Nonempty D] (b : I → D → ℝ) (p : I → ℝ)
    (hb : ∀ i d, b i d = 0 ∨ b i d = 1)
    (hp : ∀ i, (𝔼 d, b i d) = p i) :
    (𝔼 ω : I → D, ((∑ i, b i (ω i)) - ∑ i, p i)^2) ≤ ∑ i, p i := by
  classical
  rw [expect_centered_sum_sq b p hp]
  apply Finset.sum_le_sum
  intro i _
  have heq : (𝔼 d, (b i d - p i)^2) = p i - (p i)^2 := by
    calc
      _ = 𝔼 d, (b i d - 2 * p i * b i d + (p i)^2) := by
        apply Finset.expect_congr rfl
        intro d _
        rcases hb i d with h | h <;> rw [h] <;> ring
      _ = _ := by
        rw [Finset.expect_add_distrib, Finset.expect_sub_distrib,
          ← Finset.mul_expect, hp]
        simp only [Fintype.expect_const]
        ring
  rw [heq]
  linarith [sq_nonneg (p i)]

section ProjectiveLines
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The exact Bernoulli parameter of a uniformly chosen direction. -/
theorem expect_puncturedIncidence [Fintype (Projectivization K V)]
    (a z : V) (hza : z ≠ a) :
    (𝔼 d : Projectivization K V, if PuncturedIncidence a z d then (1 : ℝ) else 0) =
      1 / Fintype.card (Projectivization K V) := by
  classical
  simp only [puncturedIncidence_iff a z hza, Fintype.expect_eq_sum_div_card,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end ProjectiveLines

section CycleCount
variable {A K V : Type*} [Field K] [AddCommGroup V] [Module K V]

namespace CycleCandidate
variable {S : Finset V} {σ : A → A}

end CycleCandidate

end CycleCount

section Degrees
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype (Projectivization K V)] [Nontrivial V]

theorem variance_pointDegree_le (S : Finset V) (z : V) :
    (𝔼 ω : S → Projectivization K V,
      ((pointDegree S ω z : ℝ) - pointMean (K := K) S z)^2) ≤ pointMean (K := K) S z := by
  let b : S → Projectivization K V → ℝ := fun a d =>
    if PuncturedIncidence a.val z d then 1 else 0
  let p : S → ℝ := fun a => if z ≠ a.val then
    1 / (Fintype.card (Projectivization K V) : ℝ) else 0
  have hp (a : S) : (𝔼 d, b a d) = p a := by
    by_cases ha : z = a.val
    · simp [b,p,ha,PuncturedIncidence]
    · simp only [p, ite_eq_left ha, b]; exact expect_puncturedIncidence a.val z ha
  have h := expect_bernoulli_sum_sq_le b p (by intro a d; simp only [b]; split_ifs <;> simp) hp
  simpa only [b,p,Finset.sum_boole,pointDegree,pointMean] using h

/-- Expected size of the exceptional low-degree set in a completely finite form. -/
theorem expect_lowDegree_le [Fintype V] (S : Finset V) (T : ℕ) (μ : ℝ)
    (hμ : 0 < μ) (hT : 2 * (T : ℝ) ≤ μ)
    (hlower : ∀ z : V, μ ≤ pointMean (K := K) S z) :
    (𝔼 ω : S → Projectivization K V,
      ((Finset.univ.filter (fun z : V => pointDegree S ω z < T)).card : ℝ)) ≤
        4 * (Fintype.card V : ℝ) / μ := by
  have hpoint (z : V) : (𝔼 ω : S → Projectivization K V,
      if pointDegree S ω z < T then (1 : ℝ) else 0) ≤ 4 / μ := by
    have hz := hlower z
    have hm : 0 < pointMean (K := K) S z := hμ.trans_le hz
    have ht : (T : ℝ) < pointMean (K := K) S z := by linarith
    have hcheb := expect_low_indicator_le (fun ω : S → Projectivization K V =>
      (pointDegree S ω z : ℝ)) (pointMean (K := K) S z) (T : ℝ) ht
    have hvar := variance_pointDegree_le (K := K) S z
    have hden : 0 < (pointMean (K := K) S z - (T : ℝ))^2 := sq_pos_of_pos (by linarith)
    have hrat : pointMean (K := K) S z / (pointMean (K := K) S z - (T : ℝ))^2 ≤ 4 / μ := by
      apply (div_le_div_iff₀ hden hμ).mpr
      have hbound : 2 * (T : ℝ) ≤ pointMean (K := K) S z := hT.trans hz
      have hnon : 0 ≤ pointMean (K := K) S z - 2 * (T : ℝ) := by linarith
      have hsq := sq_nonneg (pointMean (K := K) S z - 2 * (T : ℝ))
      have hprod := mul_nonneg hnon (show 0 ≤ (T : ℝ) by positivity)
      have hmμ := mul_le_mul_of_nonneg_left hz hm.le
      nlinarith
    have h := hcheb.trans ((div_le_div_of_nonneg_right hvar hden.le).trans hrat)
    simpa only [Nat.cast_lt] using h
  simp only [← Finset.sum_boole]
  rw [Finset.expect_sum_comm]
  calc
    _ ≤ ∑ z : V, (4 / μ : ℝ) := Finset.sum_le_sum (fun z _ => hpoint z)
    _ = _ := by simp; ring
end Degrees

section EncodingIncidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end EncodingIncidence

section Alteration
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable [Fintype K] [Fintype V]

end Alteration

section Exceptional
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Fintype K] [Fintype V]

end Exceptional

section AlterationMean
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Fintype V] [Nontrivial V] [Fintype (Projectivization K V)]

end AlterationMean

section DimensionTwenty
variable (q : ℕ) [Fact q.Prime]

variable [Fintype (Projectivization (ZMod q) (Fin 20 → ZMod q))]

end DimensionTwenty

attribute [instance] MarkedLineData.labelFintype

namespace MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)

end MarkedLineData

end
end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.Release075.expect_lowDegree_le := @_root_.OAI.Release075.expect_lowDegree_le
