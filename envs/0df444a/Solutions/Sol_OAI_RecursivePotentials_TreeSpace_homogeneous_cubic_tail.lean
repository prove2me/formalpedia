-- Prove2me | solution 1 for OAI.RecursivePotentials.TreeSpace.homogeneous_cubic_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:33:30.757352+00:00
-- url     : https://prove2.me/submissions/9d3dcb7b-50c3-4476-88ea-aa8ae50dd035

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/TreeGeometry.lean:L1022-L1041
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.TreeSpace.homogeneous_cubic_tail. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Theorems.Thm_OAI_RecursivePotentials_FiniteRootedTree_defect_nonneg
import Theorems.Thm_OAI_RecursivePotentials_FiniteRootedTree_fields_eq_off_head

-- ---- from OAI.Analysis.RecursivePotentials.TreeGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

lemma energy_nonneg {p q d : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hd : 0 ≤ d) :
    0 ≤ energy p q d := by
  unfold energy
  positivity

lemma energy_symm (p q d : ℝ) : energy p q d = energy q p d := by
  unfold energy
  congr 1
  ring

lemma energy_factor {p q d : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hd : 0 ≤ d) :
    energy p q d =
      (d * (2 * p + d)) ^ (2 / 3 : ℝ) * ((2 * q + d) ^ 2) ^ (1 / 3 : ℝ) := by
  have hq' : 0 ≤ 2 * q + d := by positivity
  rw [energy, Real.mul_rpow (by positivity) hq']
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq']
  norm_num

lemma holder_two_thirds {ι : Type uIndex} (s : Finset ι) (u v : ι → ℝ)
    (hu : ∀ i ∈ s, 0 ≤ u i) (hv : ∀ i ∈ s, 0 ≤ v i) :
    ∑ i ∈ s, (u i) ^ (2 / 3 : ℝ) * (v i) ^ (1 / 3 : ℝ) ≤
      (∑ i ∈ s, u i) ^ (2 / 3 : ℝ) * (∑ i ∈ s, v i) ^ (1 / 3 : ℝ) := by
  have hpq : Real.HolderConjugate (3 / 2 : ℝ) 3 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg s hpq
    (fun i hi => Real.rpow_nonneg (hu i hi) (2 / 3))
    (fun i hi => Real.rpow_nonneg (hv i hi) (1 / 3))
  have hleft : (∑ i ∈ s, (u i ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ)) = ∑ i ∈ s, u i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.rpow_mul (hu i hi)]
    norm_num
  have hright : (∑ i ∈ s, (v i ^ (1 / 3 : ℝ)) ^ (3 : ℝ)) = ∑ i ∈ s, v i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.rpow_mul (hv i hi)]
    norm_num
  rw [hleft, hright] at h
  norm_num at h ⊢
  exact h

lemma energy_step_first {ι : Type uIndex} (s : Finset ι) (p q d : ι → ℝ)
    {P Q D : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hD : 0 ≤ D)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 ≤ q i)
    (hd : ∀ i ∈ s, 0 ≤ d i)
    (hPtight : ∑ i ∈ s, p i ^ 2 = P ^ 2)
    (hQupper : ∑ i ∈ s, q i ^ 2 ≤ Q ^ 2)
    (hPupper' : ∑ i ∈ s, (p i + d i) ^ 2 ≤ (P + D) ^ 2)
    (hQupper' : ∑ i ∈ s, (q i + d i) ^ 2 ≤ (Q + D) ^ 2) :
    ∑ i ∈ s, energy (p i) (q i) (d i) ≤ energy P Q D := by
  have hu : ∀ i ∈ s, 0 ≤ d i * (2 * p i + d i) := by
    intro i hi
    exact mul_nonneg (hd i hi) (by linarith [hp i hi, hd i hi])
  have hU : ∑ i ∈ s, d i * (2 * p i + d i) ≤ D * (2 * P + D) := by
    have heq : ∑ i ∈ s, (p i + d i) ^ 2 =
        (∑ i ∈ s, p i ^ 2) + ∑ i ∈ s, d i * (2 * p i + d i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [heq, hPtight] at hPupper'
    nlinarith
  have hV : ∑ i ∈ s, (2 * q i + d i) ^ 2 ≤ (2 * Q + D) ^ 2 := by
    convert sum_add_sq_le s q (fun i => q i + d i) hQ (add_nonneg hQ hD)
      hQupper hQupper' using 1 <;> congr 1
    · ext i
      ring
    · ring
  calc
    ∑ i ∈ s, energy (p i) (q i) (d i) =
        ∑ i ∈ s, (d i * (2 * p i + d i)) ^ (2 / 3 : ℝ) *
          ((2 * q i + d i) ^ 2) ^ (1 / 3 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact energy_factor (hp i hi) (hq i hi) (hd i hi)
    _ ≤ (∑ i ∈ s, d i * (2 * p i + d i)) ^ (2 / 3 : ℝ) *
        (∑ i ∈ s, (2 * q i + d i) ^ 2) ^ (1 / 3 : ℝ) :=
      holder_two_thirds s _ _ hu (fun i _ => sq_nonneg _)
    _ ≤ (D * (2 * P + D)) ^ (2 / 3 : ℝ) *
        ((2 * Q + D) ^ 2) ^ (1 / 3 : ℝ) := by
      apply mul_le_mul
      · exact Real.rpow_le_rpow (Finset.sum_nonneg hu) hU (by norm_num)
      · exact Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => sq_nonneg _)) hV (by norm_num)
      · positivity
      · positivity
    _ = energy P Q D := (energy_factor hP hQ hD).symm

lemma energy_step {ι : Type uIndex} (s : Finset ι) (p q d : ι → ℝ)
    {P Q D : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hD : 0 ≤ D)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 ≤ q i)
    (hd : ∀ i ∈ s, 0 ≤ d i)
    (hPupper : ∑ i ∈ s, p i ^ 2 ≤ P ^ 2)
    (hQupper : ∑ i ∈ s, q i ^ 2 ≤ Q ^ 2)
    (hPupper' : ∑ i ∈ s, (p i + d i) ^ 2 ≤ (P + D) ^ 2)
    (hQupper' : ∑ i ∈ s, (q i + d i) ^ 2 ≤ (Q + D) ^ 2)
    (htight : (∑ i ∈ s, p i ^ 2 = P ^ 2) ∨ (∑ i ∈ s, q i ^ 2 = Q ^ 2)) :
    ∑ i ∈ s, energy (p i) (q i) (d i) ≤ energy P Q D := by
  rcases htight with h | h
  · exact energy_step_first s p q d hP hQ hD hp hq hd h hQupper hPupper' hQupper'
  · simpa only [energy_symm (p := P), energy_symm (p := p _)] using
      energy_step_first s q p d hQ hP hD hq hp hd h hPupper hQupper' hPupper'

lemma energy_zero_base {d : ℝ} (hd : 0 ≤ d) : energy 0 0 d = d ^ 2 := by
  unfold energy
  rw [show d * (2 * 0 + d) * (2 * 0 + d) = d ^ 3 by ring,
    ← Real.rpow_natCast d 3, ← Real.rpow_mul hd]
  norm_num

lemma sq_rpow_three_halves {a : ℝ} (ha : 0 ≤ a) :
    (a ^ 2) ^ (3 / 2 : ℝ) = a ^ 3 := by
  rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha]
  norm_num

lemma energy_rpow_three_halves {p q d : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hd : 0 ≤ d) :
    (energy p q d) ^ (3 / 2 : ℝ) = d * (2 * p + d) * (2 * q + d) := by
  unfold energy
  rw [← Real.rpow_mul (by positivity)]
  norm_num

lemma cube_le_of_sq_le_energy {r k p q d : ℝ} (hr : 0 ≤ r) (hk : 0 ≤ k)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hd : 0 ≤ d)
    (h : r ^ 2 ≤ k ^ 2 * energy p q d) :
    r ^ 3 ≤ k ^ 3 * (d * (2 * p + d) * (2 * q + d)) := by
  have hh := Real.rpow_le_rpow (sq_nonneg r) h (by norm_num : (0 : ℝ) ≤ 3 / 2)
  rwa [sq_rpow_three_halves hr,
    Real.mul_rpow (sq_nonneg k) (energy_nonneg hp hq hd),
    sq_rpow_three_halves hk, energy_rpow_three_halves hp hq hd] at hh

namespace FiniteRootedTree

section

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

lemma fields_tight (v : ι → ℝ) (s : ι) :
    (∑ c ∈ T.children s, (T.fields v c).1 ^ 2 = (T.fields v s).1 ^ 2) ∨
    (∑ c ∈ T.children s, (T.fields v c).2 ^ 2 = (T.fields v s).2 ^ 2) := by
  have h := leastPair_tight (v s)
    (Real.sqrt (∑ c ∈ T.children s, (T.fields v c).1 ^ 2))
    (Real.sqrt (∑ c ∈ T.children s, (T.fields v c).2 ^ 2))
  rw [← T.fields_eq] at h
  rcases h with h | h
  · left
    rw [h, Real.sq_sqrt (Finset.sum_nonneg fun c _ => sq_nonneg _)]
  · right
    rw [h, Real.sq_sqrt (Finset.sum_nonneg fun c _ => sq_nonneg _)]

lemma Upper.add {p q : ι → ℝ} (hpU : T.Upper p) (hqU : T.Upper q)
    (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s) : T.Upper (fun s => p s + q s) := by
  intro s
  exact sum_add_sq_le (T.children s) p q (hp s) (hq s) (hpU s) (hqU s)

lemma Upper.smul {p : ι → ℝ} (hpU : T.Upper p) (a : ℝ) :
    T.Upper (fun s => a * p s) := by
  intro s
  simp_rw [mul_pow, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hpU s) (sq_nonneg a)

lemma fields_head_zero {H : Finset ι} (hH : T.Initial H) (v : ι → ℝ)
    (hv : ∀ s ∉ H, v s = 0) (s : ι) (hs : s ∉ H) : T.fields v s = (0, 0) := by
  rw [T.fields_eq_off_head hH v (fun _ => 0) hv s hs, T.fields_zero]

lemma averaged_feasible (x z : ι → ℝ) :
    T.Upper (fun s => ((T.fields (x + z) s).1 + (T.fields (x - z) s).1) / 2) ∧
    T.Upper (fun s => ((T.fields (x + z) s).2 + (T.fields (x - z) s).2) / 2) := by
  constructor
  · convert ((T.fields_upper (x + z)).1.add T (T.fields_upper (x - z)).1
      (fun s => (T.fields_nonneg (x + z) s).1)
      (fun s => (T.fields_nonneg (x - z) s).1)).smul T (1 / 2) using 1 ;
      ext s ; ring
  · convert ((T.fields_upper (x + z)).2.add T (T.fields_upper (x - z)).2
      (fun s => (T.fields_nonneg (x + z) s).2)
      (fun s => (T.fields_nonneg (x - z) s).2)).smul T (1 / 2) using 1 ;
      ext s ; ring

lemma defect_representation (x z : ι → ℝ) (s : ι) :
    ((T.fields (x + z) s).1 + (T.fields (x - z) s).1) / 2 =
      (T.fields x s).1 + T.defect x z s ∧
    ((T.fields (x + z) s).2 + (T.fields (x - z) s).2) / 2 =
      (T.fields x s).2 + T.defect x z s := by
  have h₁ := T.fields_difference (x + z) s
  have h₂ := T.fields_difference (x - z) s
  have h₃ := T.fields_difference x s
  simp only [Pi.add_apply, Pi.sub_apply] at h₁ h₂
  unfold defect
  constructor <;> linarith

lemma defect_energy_step (x z : ι → ℝ) (s : ι) :
    ∑ c ∈ T.children s, energy (T.fields x c).1 (T.fields x c).2 (T.defect x z c) ≤
      energy (T.fields x s).1 (T.fields x s).2 (T.defect x z s) := by
  apply energy_step (T.children s)
    (fun c => (T.fields x c).1) (fun c => (T.fields x c).2) (T.defect x z)
    (T.fields_nonneg x s).1 (T.fields_nonneg x s).2 (T.defect_nonneg x z s)
    (fun c _ => (T.fields_nonneg x c).1) (fun c _ => (T.fields_nonneg x c).2)
    (fun c _ => T.defect_nonneg x z c) ((T.fields_upper x).1 s) ((T.fields_upper x).2 s)
  · simpa only [← (T.defect_representation x z _).1] using (T.averaged_feasible x z).1 s
  · simpa only [← (T.defect_representation x z _).2] using (T.averaged_feasible x z).2 s
  · exact T.fields_tight x s

lemma defect_off_head {H : Finset ι} (hH : T.Initial H) (x z : ι → ℝ)
    (hx : ∀ s ∉ H, x s = 0) (s : ι) (hs : s ∉ H) :
    T.defect x z s = ((T.fields z s).1 + (T.fields z s).2) / 2 := by
  have h₁ := T.fields_eq_off_head hH (x + z) z
    (fun s hs => by simp [hx s hs]) s hs
  have h₂ := T.fields_eq_off_head hH (x - z) (-z)
    (fun s hs => by simp [hx s hs]) s hs
  simp only [defect, h₁, h₂, T.fields_head_zero hH x hx s hs, T.fields_neg,
    sub_zero]

lemma max_fields_sq_le_children (v : ι → ℝ) (s : ι) (hv : v s = 0) :
    (max (T.fields v s).1 (T.fields v s).2) ^ 2 ≤
      ∑ c ∈ T.children s, (max (T.fields v c).1 (T.fields v c).2) ^ 2 := by
  let R := Real.sqrt (∑ c ∈ T.children s,
    (max (T.fields v c).1 (T.fields v c).2) ^ 2)
  have hp : Real.sqrt (∑ c ∈ T.children s, (T.fields v c).1 ^ 2) ≤ R := by
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro c hc
    exact pow_le_pow_left₀ (T.fields_nonneg v c).1 (le_max_left _ _) 2
  have hq : Real.sqrt (∑ c ∈ T.children s, (T.fields v c).2 ^ 2) ≤ R := by
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro c hc
    exact pow_le_pow_left₀ (T.fields_nonneg v c).2 (le_max_right _ _) 2
  have hr : max (T.fields v s).1 (T.fields v s).2 ≤ R := by
    rw [T.fields_eq]
    simp only [leastPair, hv, neg_zero, zero_add]
    exact max_le (max_le hp hq) (max_le hq hp)
  exact (Real.le_sqrt ((T.fields_nonneg v s).1.trans (le_max_left _ _))
    (Finset.sum_nonneg fun c _ => sq_nonneg _)).mp hr

theorem tail_energy {H : Finset ι} (hH : T.Initial H) (x z : ι → ℝ)
    (hx : ∀ s ∉ H, x s = 0) (hz : ∀ s ∈ H, z s = 0) (s : ι) :
    (max (T.fields z s).1 (T.fields z s).2) ^ 2 ≤
      4 * energy (T.fields x s).1 (T.fields x s).2 (T.defect x z s) := by
  by_cases hs : s ∈ H
  · calc
      (max (T.fields z s).1 (T.fields z s).2) ^ 2 ≤
          ∑ c ∈ T.children s, (max (T.fields z c).1 (T.fields z c).2) ^ 2 :=
        T.max_fields_sq_le_children z s (hz s hs)
      _ ≤ ∑ c ∈ T.children s,
          4 * energy (T.fields x c).1 (T.fields x c).2 (T.defect x z c) := by
        apply Finset.sum_le_sum
        intro c hc
        exact tail_energy hH x z hx hz c
      _ = 4 * ∑ c ∈ T.children s,
          energy (T.fields x c).1 (T.fields x c).2 (T.defect x z c) := by
        rw [Finset.mul_sum]
      _ ≤ 4 * energy (T.fields x s).1 (T.fields x s).2 (T.defect x z s) :=
        mul_le_mul_of_nonneg_left (T.defect_energy_step x z s) (by norm_num)
  · rw [T.fields_head_zero hH x hx s hs]

    rw [energy_zero_base (T.defect_nonneg x z s)]
    have hp := (T.fields_nonneg z s).1
    have hq := (T.fields_nonneg z s).2
    have hm : max (T.fields z s).1 (T.fields z s).2 ≤
        (T.fields z s).1 + (T.fields z s).2 := max_le (by linarith) (by linarith)
    have hsq := pow_le_pow_left₀ (hp.trans (le_max_left _ _)) hm 2
    rw [T.defect_off_head hH x z hx s hs]
    nlinarith
termination_by T.maxDepth - T.depth s
decreasing_by all_goals exact T.child_measure hc

lemma rootSum_defect (x z : ι → ℝ) :
    (T.rootSum (x + z) + T.rootSum (x - z)) / 2 =
      T.rootSum x + 2 * T.defect x z T.root := by
  have h := T.defect_representation x z T.root
  unfold rootSum
  linarith [h.1, h.2]

lemma rootSum_eq_twice_max_of_root_zero (v : ι → ℝ) (hv : v T.root = 0) :
    T.rootSum v = 2 * max (T.fields v T.root).1 (T.fields v T.root).2 := by
  have h := T.fields_difference v T.root
  rw [hv] at h
  have heq : (T.fields v T.root).1 = (T.fields v T.root).2 := by linarith
  simp [rootSum, heq, two_mul]

theorem rootSum_cubic {H : Finset ι} (hH : T.Initial H) (x z : ι → ℝ)
    (hx : ∀ s ∉ H, x s = 0) (hz : ∀ s ∈ H, z s = 0) :
    (T.rootSum z) ^ 3 ≤ 64 * T.defect x z T.root *
      (T.rootSum x + T.defect x z T.root) ^ 2 := by
  have he := T.tail_energy hH x z hx hz T.root
  have hr := (T.fields_nonneg z T.root).1.trans
    (le_max_left (T.fields z T.root).1 (T.fields z T.root).2)
  have hc := cube_le_of_sq_le_energy hr (by norm_num : (0 : ℝ) ≤ 2)
    (T.fields_nonneg x T.root).1 (T.fields_nonneg x T.root).2
    (T.defect_nonneg x z T.root) (by norm_num at he ⊢; exact he)
  have hd := T.defect_nonneg x z T.root
  have halg : (2 * (T.fields x T.root).1 + T.defect x z T.root) *
        (2 * (T.fields x T.root).2 + T.defect x z T.root) ≤
        (T.rootSum x + T.defect x z T.root) ^ 2 := by
    unfold rootSum
    nlinarith [sq_nonneg ((T.fields x T.root).1 - (T.fields x T.root).2)]
  have hm := mul_le_mul_of_nonneg_left halg hd
  rw [T.rootSum_eq_twice_max_of_root_zero z (hz T.root hH.1)]
  nlinarith

end

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma normSum_on_head (v : ι →₀ ℝ) (H : Finset ι) (hH : T.Initial H)
    (hv : v.support ⊆ H) : T.normSum v = (T.restrict H hH).rootSum (fun s => v s.1) := by
  have h := T.potentials_on_head v H hH hv ⟨T.root, hH.1⟩
  exact congrArg₂ (· + ·) h.1 h.2

end FiniteRootedTree

namespace TreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeVector

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeSpace

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma restrict_initial (K : Finset ι) (hK : T.Initial K) (H : Finset ι)
    (hH : T.Initial H) :
    (T.restrict K hK).Initial (Finset.univ.filter (fun s : K => s.1 ∈ H)) := by
  constructor
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hH.1
  · intro s hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hH.2 s.1 (Finset.mem_filter.mp hs).2⟩

theorem normSum_cubic (x z : ι →₀ ℝ) {H : Finset ι} (hH : T.Initial H)
    (hx : x.support ⊆ H) (hz : ∀ s ∈ H, z s = 0) :
    (T.normSum z) ^ 3 ≤ 8 * T.meanExcess x z *
      (2 * T.normSum x + T.meanExcess x z) ^ 2 := by
  let K := T.ancestorClosure (x.support ∪ z.support)
  have hK : T.Initial K := T.ancestorClosure_initial _
  have hxK : x.support ⊆ K := (Finset.subset_union_left).trans (T.subset_ancestorClosure _)
  have hzK : z.support ⊆ K := (Finset.subset_union_right).trans (T.subset_ancestorClosure _)
  have hpK : (x + z).support ⊆ K := Finsupp.support_add.trans (Finset.union_subset hxK hzK)
  have hmK : (x - z).support ⊆ K := Finsupp.support_sub.trans (Finset.union_subset hxK hzK)
  let U := T.restrict K hK
  let xf : K → ℝ := fun c => x c.1
  let zf : K → ℝ := fun c => z c.1
  have hxf : ∀ s ∉ Finset.univ.filter (fun s : K => s.1 ∈ H), xf s = 0 := by
    intro s hs
    have hsH : s.1 ∉ H := by simpa using hs
    exact Finsupp.notMem_support_iff.mp (fun h => hsH (hx h))
  have hzf : ∀ s ∈ Finset.univ.filter (fun s : K => s.1 ∈ H), zf s = 0 := by
    intro s hs
    exact hz s.1 (Finset.mem_filter.mp hs).2
  have he := U.rootSum_cubic (T.restrict_initial K hK H hH) xf zf hxf hzf
  have hd := U.rootSum_defect xf zf
  have hn₁ : T.normSum x = U.rootSum xf := T.normSum_on_head x K hK hxK
  have hn₂ : T.normSum z = U.rootSum zf := T.normSum_on_head z K hK hzK
  have hn₃ : T.normSum (x + z) = U.rootSum (xf + zf) := T.normSum_on_head (x + z) K hK hpK
  have hn₄ : T.normSum (x - z) = U.rootSum (xf - zf) := T.normSum_on_head (x - z) K hK hmK
  have hg : T.meanExcess x z = 2 * U.defect xf zf U.root := by
    unfold meanExcess
    rw [hn₁, hn₃, hn₄]
    linarith
  rw [hg, hn₁, hn₂]
  convert he using 1 ; ring

end FiniteRootedTree

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma meanExcess_nonneg (x z : TreeSpace T) : 0 ≤ meanExcess T x z := by
  have he : x + z + (x - z) = (2 : ℝ) • x := by module
  have ht := norm_add_le (x + z) (x - z)
  rw [he, norm_smul, Real.norm_eq_abs] at ht
  norm_num at ht
  unfold meanExcess
  linarith

lemma meanExcess_le (x z : TreeSpace T) : meanExcess T x z ≤ ‖z‖ := by
  have h₁ := norm_add_le x z
  have h₂ := norm_sub_le x z
  unfold meanExcess
  linarith

theorem cubic_projected_tail (x : TreeVector T) {H : Finset ι} (hH : T.Initial H)
    (hx : (show ι →₀ ℝ from x).support ⊆ H) (z : TreeSpace T) :
    ‖z - projection T H hH z‖ ^ 3 ≤
      8 * meanExcess T (x : TreeSpace T) (z - projection T H hH z) *
        (2 * ‖(x : TreeSpace T)‖ + meanExcess T (x : TreeSpace T)
          (z - projection T H hH z)) ^ 2 := by
  induction z using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by unfold meanExcess; fun_prop)
  | ih v =>
      rw [projection_coe, ← Completion.coe_sub, meanExcess_coe, Completion.norm_coe,
        Completion.norm_coe]
      change ι →₀ ℝ at v
      change T.normSum (v - T.projectHead H v) ^ 3 ≤ _
      apply T.normSum_cubic x _ hH hx
      intro s hs
      change v s - T.projectHead H v s = 0
      rw [T.projectHead_apply, ite_eq_left hs, sub_self]

theorem cubic_tail (x : TreeVector T) {H : Finset ι} (hH : T.Initial H)
    (hx : (show ι →₀ ℝ from x).support ⊆ H) (z : TreeSpace T)
    (hz : z ∈ tail T H hH) :
    ‖z‖ ^ 3 ≤ 8 * meanExcess T (x : TreeSpace T) z *
      (2 * ‖(x : TreeSpace T)‖ + meanExcess T (x : TreeSpace T) z) ^ 2 := by
  have he := cubic_projected_tail T x hH hx z
  have hz0 : projection T H hH z = 0 := hz
  simpa only [hz0, sub_zero] using he

theorem homogeneous_cubic_tail (x : TreeVector T) {H : Finset ι} (hH : T.Initial H)
    (hx : (show ι →₀ ℝ from x).support ⊆ H) (z : TreeSpace T)
    (hz : z ∈ tail T H hH) (hz0 : z ≠ 0) :
    (‖(x : TreeSpace T) + z‖ + ‖(x : TreeSpace T) - z‖) / 2 ≥
      ‖(x : TreeSpace T)‖ + ‖z‖ ^ 3 / (8 * (2 * ‖(x : TreeSpace T)‖ + ‖z‖) ^ 2) := by
  have he := cubic_tail T x hH hx z hz
  have hg := meanExcess_nonneg T (x : TreeSpace T) z
  have hg' := meanExcess_le T (x : TreeSpace T) z
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hmono : (2 * ‖(x : TreeSpace T)‖ + meanExcess T (x : TreeSpace T) z) ^ 2 ≤
      (2 * ‖(x : TreeSpace T)‖ + ‖z‖) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hden : 0 < 8 * (2 * ‖(x : TreeSpace T)‖ + ‖z‖) ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hmono (by positivity : 0 ≤ 8 * meanExcess T (x : TreeSpace T) z)
  have hdiv : ‖z‖ ^ 3 / (8 * (2 * ‖(x : TreeSpace T)‖ + ‖z‖) ^ 2) ≤
      meanExcess T (x : TreeSpace T) z := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  unfold meanExcess at hdiv
  linarith

end TreeSpace

namespace TreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeVector

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeSpace

namespace CofiniteSubspace

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]

end CofiniteSubspace

section Moduli

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Moduli

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeSpace

end RecursivePotentials

end

end OAI

-- ---- platform node ----
open OAI OAI.RecursivePotentials OAI.RecursivePotentials.TreeSpace
open scoped BigOperators
open UniformSpace


theorem solution.{uIndex} : type_of% @_root_.OAI.RecursivePotentials.TreeSpace.homogeneous_cubic_tail.{uIndex} := @_root_.OAI.RecursivePotentials.TreeSpace.homogeneous_cubic_tail.{uIndex}
