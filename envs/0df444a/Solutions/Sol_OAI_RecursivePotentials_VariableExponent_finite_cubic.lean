-- Prove2me | solution 1 for OAI.RecursivePotentials.VariableExponent.finite_cubic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:11:17.737384+00:00
-- url     : https://prove2.me/submissions/6bb50a00-c351-419c-be7b-41c154c38f98

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/VariableEstimates.lean:L973-L1017
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.VariableExponent.finite_cubic. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms
import Definitions.Def_OAI_Analysis_RecursivePotentials_JoinedGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableEstimates

-- ---- from OAI.Analysis.RecursivePotentials.TreeGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

namespace FiniteRootedTree

section

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

lemma Initial.child_not_mem {H : Finset ι} (hH : T.Initial H) {s c : ι}
    (hs : s ∉ H) (hc : c ∈ T.children s) : c ∉ H := by
  intro h
  have := hH.2 c h
  have hh := (Finset.mem_filter.mp hc).2.2
  exact hs (hh ▸ this)

end

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

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

end FiniteRootedTree

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

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

-- ---- from OAI.Analysis.RecursivePotentials.VariableEstimates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

open Filter Topology

open scoped ENNReal

open UniformSpace

open Filter

open scoped Topology

namespace FiniteRootedTree

end FiniteRootedTree

namespace ChildExponent

noncomputable section

variable (p : ChildExponent)

end

end ChildExponent

namespace FiniteRootedTree

noncomputable section

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι) (p : ChildExponent)

lemma PUpper.add {a b : ι → ℝ} (ha : T.PUpper p a) (hb : T.PUpper p b) :
    T.PUpper p (a+b) := fun s => (p.agg_add_le _ a b).trans (add_le_add (ha s) (hb s))

lemma PUpper.smul {a : ι → ℝ} (ha : T.PUpper p a) {k : ℝ} (hk : 0 ≤ k) :
    T.PUpper p (fun s => k * a s) := by
  intro s; rw [p.agg_smul, abs_of_nonneg hk]; exact mul_le_mul_of_nonneg_left (ha s) hk

lemma pfields_add_le (v w : ι → ℝ) (s : ι) :
    (T.pfields p (v+w) s).1 ≤ (T.pfields p v s).1 + (T.pfields p w s).1 ∧
    (T.pfields p (v+w) s).2 ≤ (T.pfields p v s).2 + (T.pfields p w s).2 := by
  exact T.pfields_minimal p (v+w)
    (fun s => (T.pfields p v s).1 + (T.pfields p w s).1)
    (fun s => (T.pfields p v s).2 + (T.pfields p w s).2)
    (fun s => add_nonneg (T.pfields_nonneg p v s).1 (T.pfields_nonneg p w s).1)
    (fun s => add_nonneg (T.pfields_nonneg p v s).2 (T.pfields_nonneg p w s).2)
    (fun s => by dsimp; linarith [T.pfields_difference p v s, T.pfields_difference p w s])
    ((T.pfields_upper p v).1.add T p (T.pfields_upper p w).1)
    ((T.pfields_upper p v).2.add T p (T.pfields_upper p w).2) s

lemma pfields_smul_le (v : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) (s : ι) :
    (T.pfields p (a • v) s).1 ≤ a * (T.pfields p v s).1 ∧
    (T.pfields p (a • v) s).2 ≤ a * (T.pfields p v s).2 := by
  exact T.pfields_minimal p (a • v)
    (fun s => a * (T.pfields p v s).1) (fun s => a * (T.pfields p v s).2)
    (fun s => mul_nonneg ha (T.pfields_nonneg p v s).1)
    (fun s => mul_nonneg ha (T.pfields_nonneg p v s).2)
    (fun s => by change a * _ - a * _ = a * v s; rw [← mul_sub, T.pfields_difference])
    ((T.pfields_upper p v).1.smul T p ha) ((T.pfields_upper p v).2.smul T p ha) s

lemma pfields_smul (v : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) (s : ι) :
    T.pfields p (a • v) s = (a * (T.pfields p v s).1, a * (T.pfields p v s).2) := by
  by_cases ha0 : a = 0
  · rw [ha0, zero_smul]; simpa only [zero_mul, Pi.zero_def] using T.pfields_zero p s
  · have h₁ := T.pfields_smul_le p v ha s
    have h₂ := T.pfields_smul_le p (a • v) (inv_nonneg.mpr ha) s
    rw [smul_smul, inv_mul_cancel₀ ha0, one_smul] at h₂
    have h₂a := mul_le_mul_of_nonneg_left h₂.1 ha
    have h₂b := mul_le_mul_of_nonneg_left h₂.2 ha
    rw [← mul_assoc, mul_inv_cancel₀ ha0, one_mul] at h₂a h₂b
    exact Prod.ext (le_antisymm h₁.1 h₂a) (le_antisymm h₁.2 h₂b)

lemma pRootSum_add_le (v w : ι → ℝ) : T.pRootSum p (v+w) ≤ T.pRootSum p v + T.pRootSum p w := by
  have h := T.pfields_add_le p v w T.root; unfold pRootSum; linarith [h.1, h.2]

lemma pRootSum_smul_nonneg (v : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    T.pRootSum p (a • v) = a * T.pRootSum p v := by
  simp [pRootSum, T.pfields_smul p v ha, mul_add]

lemma pfields_eq_off_head {H : Finset ι} (hH : T.Initial H) (v w : ι → ℝ)
    (hvw : ∀ s ∉ H, v s = w s) (s : ι) (hs : s ∉ H) : T.pfields p v s = T.pfields p w s := by
  rw [T.pfields_eq p v s, T.pfields_eq p w s, hvw s hs]
  apply congrArg₂ (leastPair (w s))
  · exact p.agg_congr _ _ _ (fun c hc => congrArg Prod.fst (pfields_eq_off_head hH v w hvw c (hH.child_not_mem T hs hc)))
  · exact p.agg_congr _ _ _ (fun c hc => congrArg Prod.snd (pfields_eq_off_head hH v w hvw c (hH.child_not_mem T hs hc)))
termination_by T.maxDepth - T.depth s
decreasing_by all_goals exact T.child_measure hc

lemma pfields_head_zero {H : Finset ι} (hH : T.Initial H) (v : ι → ℝ)
    (hv : ∀ s ∉ H, v s = 0) (s : ι) (hs : s ∉ H) : T.pfields p v s = (0,0) := by
  rw [T.pfields_eq_off_head p hH v (fun _ => 0) hv s hs, T.pfields_zero]

lemma pfields_head_le {H : Finset ι} (hH : T.Initial H) (v w : ι → ℝ)
    (hv : ∀ s ∉ H, v s = 0) (hvw : ∀ s ∈ H, v s = w s) (s : ι) :
    (T.pfields p v s).1 ≤ (T.pfields p w s).1 ∧ (T.pfields p v s).2 ≤ (T.pfields p w s).2 := by
  by_cases hs : s ∈ H
  · rw [T.pfields_eq p v s, T.pfields_eq p w s, hvw s hs]
    have h₁ : p.agg (T.children s) (fun c => (T.pfields p v c).1) ≤ p.agg (T.children s) (fun c => (T.pfields p w c).1) :=
      p.agg_mono_nonneg _ _ _ (fun c _ => (T.pfields_nonneg p v c).1)
        (fun c hc => (pfields_head_le hH v w hv hvw c).1)
    have h₂ : p.agg (T.children s) (fun c => (T.pfields p v c).2) ≤ p.agg (T.children s) (fun c => (T.pfields p w c).2) :=
      p.agg_mono_nonneg _ _ _ (fun c _ => (T.pfields_nonneg p v c).2)
        (fun c hc => (pfields_head_le hH v w hv hvw c).2)
    exact ⟨max_le_max h₁ (by linarith), max_le_max h₂ (by linarith)⟩
  · rw [T.pfields_head_zero p hH v hv s hs]
    exact T.pfields_nonneg p w s
termination_by T.maxDepth - T.depth s
decreasing_by all_goals exact T.child_measure hc

end

end FiniteRootedTree

namespace VariableExponent

noncomputable section

lemma heightExponent_pow_le_exp (h : ℕ+) : heightExponent h ^ h.val ≤ Real.exp 1 := by
  have hh : (0 : ℝ) < h.val := by exact_mod_cast h.pos
  have he : heightExponent h ≤ Real.exp (1 / (h.val : ℝ)) := by
    simpa [heightExponent, add_comm] using Real.add_one_le_exp (1 / (h.val : ℝ))
  calc
    heightExponent h ^ h.val ≤ Real.exp (1 / (h.val : ℝ)) ^ h.val :=
      pow_le_pow_left₀ (le_trans (by norm_num) (heightExponent_gt_one h).le) he _
    _ = Real.exp 1 := by rw [← Real.exp_nat_mul]; congr 1; field_simp

lemma recurrenceCeiling_one_le : 1 ≤ recurrenceCeiling := by
  dsimp [recurrenceCeiling]; linarith [Real.exp_one_gt_two]

lemma recurrenceCeiling_pos : 0 < recurrenceCeiling := lt_of_lt_of_le zero_lt_one recurrenceCeiling_one_le

lemma recurrence_coefficient_le {p : ℝ} (hp : 1 ≤ p) :
    p * (3 : ℝ) ^ ((p-1)/p) ≤ recurrenceCeiling ^ (p-1) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hpow : (3 : ℝ) ^ ((p-1)/p) ≤ (3 : ℝ) ^ (p-1) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply (div_le_iff₀ hp0).mpr
    nlinarith
  have hpexp : p ≤ Real.exp (p-1) := by simpa using Real.add_one_le_exp (p-1)
  calc
    p * (3 : ℝ) ^ ((p-1)/p) ≤ Real.exp (p-1) * (3 : ℝ) ^ (p-1) :=
      mul_le_mul hpexp hpow (by positivity) (by positivity)
    _ = recurrenceCeiling ^ (p-1) := by
      rw [recurrenceCeiling, Real.mul_rpow (by norm_num) (Real.exp_pos 1).le, Real.exp_one_rpow]
      ring

lemma accumulated_bound {p : ℝ} (hp : 1 ≤ p) (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    {h : ℕ} (hrec : ∀ j < h, K (j+1) ^ p ≤ p * (3 : ℝ) ^ ((p-1)/p) * K j) :
    ∀ j ≤ h, K j ≤ recurrenceCeiling * K 0 ^ ((1/p)^j) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hC := recurrenceCeiling_pos
  have hK0 := hK 0
  intro j hj
  induction j with
  | zero =>
      simp only [pow_zero, Real.rpow_one]
      exact le_mul_of_one_le_left (hK 0) recurrenceCeiling_one_le
  | succ j ih =>
      have hjh : j < h := by omega
      have hi := ih (by omega)
      apply (Real.rpow_le_rpow_iff (hK _) (by positivity) hp0).mp
      have hcoef := recurrence_coefficient_le hp
      have hprod : (recurrenceCeiling ^ (p-1)) * recurrenceCeiling = recurrenceCeiling ^ p := by
        calc
          _ = recurrenceCeiling ^ (p-1) * recurrenceCeiling ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = recurrenceCeiling ^ (p-1+1) := (Real.rpow_add recurrenceCeiling_pos _ _).symm
          _ = _ := by congr 1; ring
      calc
        K (j+1) ^ p ≤ p * (3 : ℝ) ^ ((p-1)/p) * K j := hrec j hjh
        _ ≤ recurrenceCeiling ^ (p-1) * (recurrenceCeiling * K 0 ^ ((1/p)^j)) :=
          mul_le_mul hcoef hi (hK j) (by positivity)
        _ = (recurrenceCeiling * K 0 ^ ((1/p)^(j+1))) ^ p := by
          rw [Real.mul_rpow recurrenceCeiling_pos.le (Real.rpow_nonneg (hK 0) _),
            ← Real.rpow_mul (hK 0), ← mul_assoc, hprod]
          congr 2
          rw [pow_succ]
          field_simp

lemma cubic_of_accumulated (h : ℕ+) (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    (hrec : ∀ j < h.val, K (j+1) ^ heightExponent h ≤
      heightExponent h * (3 : ℝ) ^ ((heightExponent h - 1) / heightExponent h) * K j)
    {Y : ℝ} (hY0 : 0 ≤ Y) (hY1 : Y ≤ 1) (hY : Y ≤ 2 * K h.val) :
    cubicConstant * Y ^ 3 ≤ K 0 := by
  have hC := recurrenceCeiling_pos
  let p := heightExponent h
  have hp : 1 < p := heightExponent_gt_one h
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpow : p ^ h.val ≤ 3 := (heightExponent_pow_le_exp h).trans Real.exp_one_lt_three.le
  have hb := accumulated_bound hp.le K hK hrec h.val le_rfl
  let a := Y / (2 * recurrenceCeiling)
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    apply (div_le_one (by positivity)).mpr
    linarith [recurrenceCeiling_one_le]
  have haK : a ≤ K 0 ^ ((1/p)^h.val) := by
    dsimp [a]
    apply (div_le_iff₀ (by positivity : 0 < 2 * recurrenceCeiling)).mpr
    dsimp [p] at *
    linarith
  have hraised := Real.rpow_le_rpow ha0 haK (pow_nonneg hp0.le h.val)
  have hexp : (1/p)^h.val * p^h.val = 1 := by rw [← mul_pow]; field_simp; simp
  rw [← Real.rpow_mul (hK 0), hexp, Real.rpow_one] at hraised
  have hcub : a ^ 3 ≤ a ^ (p ^ h.val) := by
    rw [← Real.rpow_natCast a 3]
    by_cases ha : a = 0
    · simp [ha, Real.zero_rpow (pow_pos hp0 h.val).ne']
    · exact Real.rpow_le_rpow_of_exponent_ge (lt_of_le_of_ne ha0 (Ne.symm ha)) ha1 hpow
  have heq : a ^ 3 = cubicConstant * Y ^ 3 := by
    dsimp [a, cubicConstant, recurrenceCeiling]
    ring
  rw [heq] at hcub
  exact hcub.trans hraised

end

end VariableExponent

namespace FiniteRootedTree

noncomputable section

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

lemma exitCut_zero {H : Finset ι} (hH : T.Initial H) : T.exitCut H 0 = {T.root} := by
  ext s
  simp only [exitCut, headLevel, stoppedExit, firstExit, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and, Nat.le_zero, Finset.mem_singleton]
  rw [T.depth_eq_zero_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
  · intro hs; subst s; exact Or.inl ⟨hH.1, rfl⟩

lemma exitCut_succ {H : Finset ι} (hH : T.Initial H)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1) (j : ℕ) :
    T.exitCut H (j+1) = T.childrenOf (T.headLevel H j) ∪ T.stoppedExit H j := by
  ext c
  simp only [exitCut, childrenOf, headLevel, stoppedExit, firstExit, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hcr : c = T.root
  · subst c
    simp [T.depth_root, hH.1]
  · have hd := hstep c hcr
    constructor
    · rintro (⟨hcH, hcd⟩ | ⟨⟨hcH, hcpH⟩, hcd⟩)
      · exact Or.inl ⟨hcr, hH.2 c hcH, by omega⟩
      · by_cases hlt : T.depth c ≤ j
        · exact Or.inr ⟨⟨hcH, hcpH⟩, hlt⟩
        · exact Or.inl ⟨hcr, hcpH, by omega⟩
    · rintro (⟨_, hcpH, hpd⟩ | ⟨⟨hcH, hcpH⟩, hcd⟩)
      · by_cases hcH : c ∈ H
        · exact Or.inl ⟨hcH, by omega⟩
        · exact Or.inr ⟨⟨hcH, hcpH⟩, by omega⟩
      · exact Or.inr ⟨⟨hcH, hcpH⟩, by omega⟩

lemma exitCut_succ_disjoint {H : Finset ι}
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1) (j : ℕ) :
    Disjoint (T.childrenOf (T.headLevel H j)) (T.stoppedExit H j) := by
  apply Finset.disjoint_left.mpr
  intro c hc hd
  simp only [childrenOf, headLevel, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  have hh := hstep c hc.1
  have hh' := (Finset.mem_filter.mp hd).2
  omega

lemma headLevel_stopped_disjoint (H : Finset ι) (j : ℕ) :
    Disjoint (T.headLevel H j) (T.stoppedExit H j) := by
  apply Finset.disjoint_left.mpr
  intro c hc hd
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).2.1 (Finset.mem_filter.mp hc).1

lemma sum_exitCut_succ {H : Finset ι} (hH : T.Initial H)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1) (j : ℕ) (f : ι → ℝ) :
    ∑ c ∈ T.exitCut H (j+1), f c =
      (∑ s ∈ T.headLevel H j, ∑ c ∈ T.children s, f c) + ∑ c ∈ T.stoppedExit H j, f c := by
  rw [T.exitCut_succ hH hstep j, Finset.sum_union (T.exitCut_succ_disjoint hstep j), T.sum_children_on]

end

end FiniteRootedTree

namespace VariableExponent

lemma rpow_increment_le {p a d : ℝ} (hp : 1 ≤ p) (ha : 0 ≤ a) (hd : 0 ≤ d) :
    (a+d)^p - a^p ≤ p * (a+d)^(p-1) * d := by
  by_cases hd0 : d = 0
  · simp [hd0]
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    have hlt : a < a+d := by linarith
    have hs := (convexOn_rpow hp).slope_le_of_hasDerivAt (x := a) (y := a+d) ha (add_nonneg ha hd) hlt
      (Real.hasDerivAt_rpow_const (Or.inr hp))
    rw [slope_def_field] at hs
    have hh : 0 < a+d-a := by linarith
    have ht := (div_le_iff₀ hh).mp hs
    nlinarith

lemma holder_powers {ι : Type uIndex} (s : Finset ι) {p : ℝ} (hp : 1 < p) (a d : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hd : ∀ i ∈ s, 0 ≤ d i) :
    ∑ i ∈ s, a i ^ (p-1) * d i ≤
      (∑ i ∈ s, a i ^ p) ^ ((p-1)/p) * (∑ i ∈ s, d i ^ p) ^ (1/p) := by
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg s
    (Real.HolderConjugate.conjExponent hp).symm
    (fun i hi => Real.rpow_nonneg (ha i hi) (p-1)) hd
  have hpp : p-1 ≠ 0 := by linarith
  have ht : ∀ i ∈ s, (a i ^ (p-1)) ^ Real.conjExponent p = a i ^ p := by
    intro i hi
    rw [← Real.rpow_mul (ha i hi)]
    congr 1
    dsimp [Real.conjExponent]
    field_simp
  simp_rw [Finset.sum_congr rfl ht] at hh
  convert hh using 2
  congr 1
  dsimp [Real.conjExponent]
  field_simp

end VariableExponent

namespace FiniteRootedTree

noncomputable section

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

lemma sum_exitCut_le_root {H : Finset ι} (hH : T.Initial H)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (f : ι → ℝ) (hf : ∀ s ∈ H, ∑ c ∈ T.children s, f c ≤ f s) (j : ℕ) :
    ∑ c ∈ T.exitCut H j, f c ≤ f T.root := by
  induction j with
  | zero => simp [T.exitCut_zero hH]
  | succ j ih =>
    rw [T.sum_exitCut_succ hH hstep]
    have hl : (∑ s ∈ T.headLevel H j, ∑ c ∈ T.children s, f c) ≤
        ∑ s ∈ T.headLevel H j, f s :=
      Finset.sum_le_sum fun s hs => hf s (Finset.mem_filter.mp hs).1
    calc
      _ ≤ (∑ s ∈ T.headLevel H j, f s) + ∑ c ∈ T.stoppedExit H j, f c := add_le_add hl le_rfl
      _ ≤ _ := by simpa only [exitCut, Finset.sum_union (T.headLevel_stopped_disjoint H j)] using ih

lemma root_le_sum_exitCut {H : Finset ι} (hH : T.Initial H)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (f : ι → ℝ) (hf : ∀ s ∈ H, f s ≤ ∑ c ∈ T.children s, f c) (j : ℕ) :
    f T.root ≤ ∑ c ∈ T.exitCut H j, f c := by
  have hh := T.sum_exitCut_le_root hH hstep (fun s => -f s) (fun s hs => by
    simpa only [Finset.sum_neg_distrib, neg_le_neg_iff] using hf s hs) j
  simpa only [Finset.sum_neg_distrib, neg_le_neg_iff] using hh

end

end FiniteRootedTree

namespace VariableExponent

noncomputable section

lemma holder_powers_two {ι : Type uIndex} (s : Finset ι) {p : ℝ} (hp : 1 < p)
    (a d : Bool → ι → ℝ) (ha : ∀ σ i, 0 ≤ a σ i) (hd : ∀ σ i, 0 ≤ d σ i) :
    ∑ σ, ∑ i ∈ s, a σ i ^ (p-1) * d σ i ≤
      (∑ σ, ∑ i ∈ s, a σ i ^ p) ^ ((p-1)/p) *
      (∑ σ, ∑ i ∈ s, d σ i ^ p) ^ (1/p) := by
  have hh := holder_powers (Finset.univ ×ˢ s) hp
    (fun q : Bool × ι => a q.1 q.2) (fun q : Bool × ι => d q.1 q.2)
    (fun q _ => ha q.1 q.2) (fun q _ => hd q.1 q.2)
  simpa only [Finset.sum_product] using hh

lemma rpow_sub_one_mul {p d : ℝ} (hp : 1 < p) (hd : 0 ≤ d) :
    d ^ (p-1) * d = d ^ p := by
  by_cases h : d = 0
  · simp [h, Real.zero_rpow (ne_of_gt (zero_lt_one.trans hp))]
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm h)
    calc
      _ = d ^ (p-1) * d ^ (1:ℝ) := by rw [Real.rpow_one]
      _ = d ^ (p-1+1) := (Real.rpow_add hdpos _ _).symm
      _ = _ := by congr 1; ring

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

lemma cutEnergy_nonneg (p : ℝ) (H : Finset ι) (d : Bool → ι → ℝ)
    (hd : ∀ σ s, 0 ≤ d σ s) (j : ℕ) : 0 ≤ cutEnergy T p H d j := by
  unfold cutEnergy
  exact Real.rpow_nonneg (Finset.sum_nonneg fun σ _ => Finset.sum_nonneg fun s _ =>
    Real.rpow_nonneg (hd σ s) _) _

lemma cutEnergy_pow {p : ℝ} (hp : 1 < p) (H : Finset ι) (d : Bool → ι → ℝ)
    (hd : ∀ σ s, 0 ≤ d σ s) (j : ℕ) :
    cutEnergy T p H d j ^ p = ∑ σ, ∑ s ∈ T.exitCut H j, d σ s ^ p := by
  rw [cutEnergy, ← Real.rpow_mul (Finset.sum_nonneg fun σ _ => Finset.sum_nonneg fun s _ =>
    Real.rpow_nonneg (hd σ s) _), one_div_mul_cancel (ne_of_gt (zero_lt_one.trans hp)), Real.rpow_one]

lemma accumulated_cut_recursion {p : ℝ} (hp : 1 < p) {H : Finset ι} (hH : T.Initial H)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (a d : Bool → ι → ℝ) (ha : ∀ σ s, 0 ≤ a σ s) (hd : ∀ σ s, 0 ≤ d σ s)
    (hloc : ∀ σ s, s ∈ H → ∑ c ∈ T.children s, d σ c ^ p ≤
      p * a σ s ^ (p-1) * d σ s)
    (hext : ∀ σ s, s ∉ H → a σ s = d σ s)
    (j : ℕ) (hA : ∑ σ, ∑ s ∈ T.exitCut H j, a σ s ^ p ≤ 3) :
    cutEnergy T p H d (j+1) ^ p ≤
      p * (3 : ℝ) ^ ((p-1)/p) * cutEnergy T p H d j := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hsum : (∑ σ, ∑ s ∈ T.exitCut H (j+1), d σ s ^ p) ≤
      p * (∑ σ, ∑ s ∈ T.exitCut H j, a σ s ^ (p-1) * d σ s) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro σ hσ
    rw [T.sum_exitCut_succ hH hstep, FiniteRootedTree.exitCut,
      Finset.sum_union (T.headLevel_stopped_disjoint H j), mul_add]
    apply add_le_add
    · rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun s hs => by
        simpa only [mul_assoc] using hloc σ s (Finset.mem_filter.mp hs).1
    · rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro s hs
      have hsH : s ∉ H := (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2.1
      rw [hext σ s hsH, rpow_sub_one_mul hp (hd σ s)]
      exact le_mul_of_one_le_left (Real.rpow_nonneg (hd σ s) _) hp.le
  rw [cutEnergy_pow T hp H d hd]
  apply hsum.trans
  have hh := holder_powers_two (T.exitCut H j) hp a d ha hd
  have hb : (∑ σ, ∑ s ∈ T.exitCut H j, a σ s ^ p) ^ ((p-1)/p) ≤
      (3 : ℝ) ^ ((p-1)/p) := Real.rpow_le_rpow (Finset.sum_nonneg fun σ _ =>
        Finset.sum_nonneg fun s _ => Real.rpow_nonneg (ha σ s) _) hA (by positivity)
  have hb' := mul_le_mul_of_nonneg_right hb (cutEnergy_nonneg T p H d hd j)
  have hh' := hh.trans hb'
  simpa only [mul_assoc, cutEnergy] using mul_le_mul_of_nonneg_left hh' hp0.le

end

end VariableExponent

namespace FiniteRootedTree

noncomputable section

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι) (p : ChildExponent)

lemma pField_nonneg (v : ι → ℝ) (b : Bool) (s : ι) : 0 ≤ T.pField p v b s := by
  cases b <;> simp only [pField, Bool.false_eq_true, ite_false, ite_true] <;>
    first | exact (T.pfields_nonneg p v s).1 | exact (T.pfields_nonneg p v s).2

lemma pField_power_upper (v : ι → ℝ) (b : Bool) (s : ι) :
    ∑ c ∈ T.children s, T.pField p v b c ^ p.val ≤ T.pField p v b s ^ p.val := by
  have hu : p.agg (T.children s) (T.pField p v b) ≤ T.pField p v b s := by
    cases b <;> first | exact (T.pfields_upper p v).1 s | exact (T.pfields_upper p v).2 s
  have hh := (p.agg_le_iff _ _ (T.pField_nonneg p v b s)).mp hu
  simpa only [abs_of_nonneg (T.pField_nonneg p v b _)] using hh

lemma tightLabel_spec (v : ι → ℝ) (s : ι) :
    T.pField p v (T.tightLabel p v s) s ^ p.val =
      ∑ c ∈ T.children s, T.pField p v (T.tightLabel p v s) c ^ p.val :=
  (T.exists_tight_label p v s).choose_spec

lemma pField_power_sum_le_norm (v : ι → ℝ) (s : ι) :
    T.pField p v true s ^ p.val + T.pField p v false s ^ p.val ≤
      ((T.pfields p v s).1 + (T.pfields p v s).2) ^ p.val := by
  exact Real.add_rpow_le_rpow_add (T.pfields_nonneg p v s).1 (T.pfields_nonneg p v s).2 p.one_le

end

end FiniteRootedTree

namespace VariableExponent

noncomputable section

variable {ι : Type uIndex}

variable [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (p : ChildExponent)

variable (H : Finset ι) (x y : ι → ℝ)

variable {H x y} (hH : T.Initial H) (hx : ∀ s ∉ H, x s = 0) (hy : ∀ s ∈ H, y s = 0)

omit hy in
lemma endpoint_on_head {ι : Type uIndex} [Fintype ι] [DecidableEq ι] {H : Finset ι} {x y : ι → ℝ}
    (hy : ∀ s ∈ H, y s = 0) (σ : Bool) (s : ι) (hs : s ∈ H) : (x + signed y σ) s = x s := by
  cases σ <;> simp [signed, hy s hs]

include hH hx hy in
lemma head_field_le (σ b : Bool) (s : ι) :
    T.pField p x b s ≤ T.pField p (x + signed y σ) b s := by
  have hh := T.pfields_head_le p hH x (x + signed y σ) hx
    (fun s hs => (endpoint_on_head hy σ s hs).symm) s
  cases b <;> first | exact hh.1 | exact hh.2

include hH hx hy in
lemma increment_nonneg (σ : Bool) (s : ι) : 0 ≤ increment T p H x y σ s := by
  unfold increment
  split_ifs with hs
  · exact sub_nonneg.mpr (head_field_le T p hH hx hy σ true s)
  · exact T.pField_nonneg p _ _ _

include hH hx hy in
lemma coefficient_nonneg (σ : Bool) (s : ι) : 0 ≤ coefficient T p H x y σ s := by
  unfold coefficient
  split_ifs
  · exact T.pField_nonneg p _ _ _
  · exact increment_nonneg T p hH hx hy σ s

include hy in
lemma common_increment (σ b : Bool) (s : ι) (hs : s ∈ H) :
    T.pField p (x + signed y σ) b s = T.pField p x b s + increment T p H x y σ s := by
  rw [increment, ite_eq_left hs]
  cases b
  · have hb := T.pfields_difference p x s
    have he := T.pfields_difference p (x + signed y σ) s
    rw [endpoint_on_head hy σ s hs] at he
    simp only [FiniteRootedTree.pField, Bool.false_eq_true, ite_false, ite_true]
    linarith
  · simp only [FiniteRootedTree.pField, ite_true]; ring

include hH hx hy in
lemma prefix_child_increment (σ : Bool) (s : ι) (_hs : s ∈ H) (c : ι) (hc : c ∈ T.children s) :
    T.pField p (x + signed y σ) (T.tightLabel p x s) c =
      T.pField p x (T.tightLabel p x s) c + increment T p H x y σ c := by
  by_cases hcH : c ∈ H
  · exact common_increment T p hy σ _ c hcH
  · have hb := T.pfields_head_zero p hH x hx c hcH
    have hp : T.parent c = s := (Finset.mem_filter.mp hc).2.2
    simp only [increment, ite_eq_right hcH, hp]
    have hb' : T.pField p x (T.tightLabel p x s) c = 0 := by
      simp [FiniteRootedTree.pField, hb]
    rw [hb', zero_add]

include hH hx hy in
lemma layer_increment (_hp : 1 < p.val) (σ : Bool) (s : ι) (hs : s ∈ H) :
    ∑ c ∈ T.children s, increment T p H x y σ c ^ p.val ≤
      p.val * coefficient T p H x y σ s ^ (p.val-1) * increment T p H x y σ s := by
  let b := T.tightLabel p x s
  let A := T.pField p x b s
  let d := increment T p H x y σ s
  have ha : 0 ≤ A := T.pField_nonneg p x b s
  have hd : 0 ≤ d := increment_nonneg T p hH hx hy σ s
  have hsum : (∑ c ∈ T.children s, T.pField p x b c ^ p.val) +
      (∑ c ∈ T.children s, increment T p H x y σ c ^ p.val) ≤
      ∑ c ∈ T.children s, T.pField p (x + signed y σ) b c ^ p.val := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro c hc
    rw [prefix_child_increment T p hH hx hy σ s hs c hc]
    exact Real.add_rpow_le_rpow_add (T.pField_nonneg p x b c)
      (increment_nonneg T p hH hx hy σ c) p.one_le
  have ht : A ^ p.val = ∑ c ∈ T.children s, T.pField p x b c ^ p.val := T.tightLabel_spec p x s
  have hu := T.pField_power_upper p (x + signed y σ) b s
  have he : T.pField p (x + signed y σ) b s = A+d := common_increment T p hy σ b s hs
  have hc : coefficient T p H x y σ s = A+d := by rw [coefficient, ite_eq_left hs]; exact he
  have hd' := rpow_increment_le p.one_le ha hd
  rw [← ht] at hsum
  rw [he] at hu
  rw [hc]
  exact le_trans (by linarith : (∑ c ∈ T.children s, increment T p H x y σ c ^ p.val) ≤ (A+d)^p.val-A^p.val) hd'

include hH hx in
lemma outside_field_eq (σ b : Bool) (s : ι) (hs : s ∉ H) :
    T.pField p (x + signed y σ) b s = T.pField p (signed y σ) b s := by
  have hh := T.pfields_eq_off_head p hH (x + signed y σ) (signed y σ)
    (fun c hc => by simp [hx c hc]) s hs
  cases b <;> simp only [FiniteRootedTree.pField, Bool.false_eq_true, ite_false, ite_true, hh]

include hH hx in
lemma exit_sign_mass (s : ι) (hs : s ∉ H) :
    (∑ σ, increment T p H x y σ s ^ p.val) =
      T.pField p y true s ^ p.val + T.pField p y false s ^ p.val := by
  simp only [increment, ite_eq_right hs, Fintype.sum_bool]
  rw [outside_field_eq T p hH hx true _ s hs, outside_field_eq T p hH hx false _ s hs]
  cases hb : T.tightLabel p x (T.parent s) <;>
    simp [signed, FiniteRootedTree.pField, T.pfields_neg, add_comm]

end

end VariableExponent

namespace FiniteRootedTree

noncomputable section

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι) (p : ChildExponent)

lemma fields_cut_mass {H : Finset ι} (hH : T.Initial H)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (v : ι → ℝ) (j : ℕ) :
    ∑ s ∈ T.exitCut H j, (T.pField p v true s ^ p.val + T.pField p v false s ^ p.val) ≤
      T.pRootSum p v ^ p.val := by
  rw [Finset.sum_add_distrib]
  have hp := T.sum_exitCut_le_root hH hstep (fun s => T.pField p v true s ^ p.val)
    (fun s _ => T.pField_power_upper p v true s) j
  have hq := T.sum_exitCut_le_root hH hstep (fun s => T.pField p v false s ^ p.val)
    (fun s _ => T.pField_power_upper p v false s) j
  exact (add_le_add hp hq).trans (T.pField_power_sum_le_norm p v T.root)

lemma fields_subcut_mass {H : Finset ι} (hH : T.Initial H)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (v : ι → ℝ) (j : ℕ) (S : Finset ι) (hS : S ⊆ T.exitCut H j) :
    ∑ s ∈ S, (T.pField p v true s ^ p.val + T.pField p v false s ^ p.val) ≤
      T.pRootSum p v ^ p.val := by
  apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hS (fun s _ _ =>
    add_nonneg (Real.rpow_nonneg (T.pField_nonneg p v true s) _)
      (Real.rpow_nonneg (T.pField_nonneg p v false s) _)))
  exact T.fields_cut_mass p hH hstep v j

lemma pRootSum_tail_midpoint (x y : ι → ℝ) :
    T.pRootSum p y ≤ (T.pRootSum p (x+y) + T.pRootSum p (x-y)) / 2 := by
  have he : y = (1/2:ℝ) • ((x+y) + -(x-y)) := by ext s; simp; ring
  calc
    T.pRootSum p y = T.pRootSum p ((1/2:ℝ) • ((x+y) + -(x-y))) := congrArg (T.pRootSum p) he
    _ = (1/2:ℝ) * T.pRootSum p ((x+y) + -(x-y)) := T.pRootSum_smul_nonneg p _ (by norm_num)
    _ ≤ (1/2:ℝ) * (T.pRootSum p (x+y) + T.pRootSum p (-(x-y))) :=
      mul_le_mul_of_nonneg_left (T.pRootSum_add_le p _ _) (by norm_num)
    _ = _ := by rw [T.pRootSum_neg]; ring

end

end FiniteRootedTree

namespace VariableExponent

noncomputable section

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι) (p : ChildExponent)

variable {H : Finset ι} {x y : ι → ℝ} (hH : T.Initial H)
    (hx : ∀ s ∉ H, x s = 0) (hy : ∀ s ∈ H, y s = 0)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)

omit hH hx hy hstep in
lemma total_coefficient_mass {ι : Type uIndex} [Fintype ι] [DecidableEq ι] (T : FiniteRootedTree ι)
    (p : ChildExponent) {H : Finset ι} {x y : ι → ℝ} (hH : T.Initial H) (hx : ∀ s ∉ H, x s = 0)
    (_hy : ∀ s ∈ H, y s = 0) (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (hM : ∀ σ, T.pRootSum p (x + signed y σ) ≤ 1) (j : ℕ) :
    ∑ σ, ∑ s ∈ T.exitCut H j, coefficient T p H x y σ s ^ p.val ≤ 3 := by
  have hY : T.pRootSum p y ≤ 1 := by
    have hh := T.pRootSum_tail_midpoint p x y
    have h₁ := hM true; have h₂ := hM false
    simp only [signed_true, signed_false, ← sub_eq_add_neg] at h₁ h₂
    linarith
  have hheads : ∀ σ, (∑ s ∈ T.headLevel H j, coefficient T p H x y σ s ^ p.val) ≤ 1 := by
    intro σ
    calc
      _ ≤ ∑ s ∈ T.headLevel H j, (T.pField p (x+signed y σ) true s ^ p.val +
          T.pField p (x+signed y σ) false s ^ p.val) := by
        apply Finset.sum_le_sum
        intro s hs
        rw [coefficient, ite_eq_left (Finset.mem_filter.mp hs).1]
        cases T.tightLabel p x s
        · exact le_add_of_nonneg_left (Real.rpow_nonneg (T.pField_nonneg p _ true s) _)
        · exact le_add_of_nonneg_right (Real.rpow_nonneg (T.pField_nonneg p _ false s) _)
      _ ≤ T.pRootSum p (x+signed y σ) ^ p.val := T.fields_subcut_mass p hH hstep _ j _
        (fun s hs => Finset.mem_union_left _ hs)
      _ ≤ 1 := by
        simpa only [Real.one_rpow] using Real.rpow_le_rpow (T.pRootSum_nonneg p _) (hM σ) p.pos.le
  have hstopped : (∑ σ, ∑ s ∈ T.stoppedExit H j, coefficient T p H x y σ s ^ p.val) ≤ 1 := by
    rw [Finset.sum_comm]
    have he : (∑ s ∈ T.stoppedExit H j, ∑ σ, coefficient T p H x y σ s ^ p.val) =
        ∑ s ∈ T.stoppedExit H j, (T.pField p y true s ^ p.val + T.pField p y false s ^ p.val) := by
      apply Finset.sum_congr rfl
      intro s hs
      have hsH := (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2.1
      simp only [coefficient, ite_eq_right hsH]
      exact exit_sign_mass T p hH hx s hsH
    rw [he]
    apply (T.fields_subcut_mass p hH hstep y j (T.stoppedExit H j)
      (fun s hs => Finset.mem_union_right _ hs)).trans
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (T.pRootSum_nonneg p y) hY p.pos.le
  simp only [FiniteRootedTree.exitCut, Finset.sum_union (T.headLevel_stopped_disjoint H j),
    Finset.sum_add_distrib]
  have hh : (∑ σ, ∑ s ∈ T.headLevel H j, coefficient T p H x y σ s ^ p.val) ≤ 2 := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun σ _ => hheads σ)
  linarith

include hy in
lemma tailFlux_dominates (b : Bool) (s : ι) : T.pField p y b s ^ p.val ≤ tailFlux T p H y s := by
  unfold tailFlux
  by_cases hs : s ∈ H
  · rw [ite_eq_left hs]
    cases b
    · have he := T.pfields_difference p y s
      rw [hy s hs] at he
      have hh : T.pField p y false s = T.pField p y true s := by
        simp only [FiniteRootedTree.pField, Bool.false_eq_true, ite_false, ite_true]; linarith
      rw [hh]
    · exact le_rfl
  · rw [ite_eq_right hs]
    cases b
    · exact le_add_of_nonneg_left (Real.rpow_nonneg (T.pField_nonneg p y true s) _)
    · exact le_add_of_nonneg_right (Real.rpow_nonneg (T.pField_nonneg p y false s) _)

include hy in
lemma tailFlux_local (s : ι) (hs : s ∈ H) :
    tailFlux T p H y s ≤ ∑ c ∈ T.children s, tailFlux T p H y c := by
  have he : T.pField p y true s = max (p.agg (T.children s) (T.pField p y true))
      (p.agg (T.children s) (T.pField p y false)) := by
    change (T.pfields p y s).1 = _
    rw [T.pfields_eq p y s]
    simp only [leastPair, hy s hs, zero_add]
    rfl
  rw [tailFlux, ite_eq_left hs, he, Real.rpow_max (p.agg_nonneg _ _) (p.agg_nonneg _ _) p.pos.le]
  apply max_le
  all_goals
    rw [p.agg_rpow]
    apply Finset.sum_le_sum
    intro c hc
    rw [abs_of_nonneg (T.pField_nonneg p y _ c)]
    exact tailFlux_dominates T p hy _ c

include hy in
lemma tailFlux_head_terminal {h : ℕ} (hheight : ∀ s, T.depth s ≤ h)
    (s : ι) (hs : s ∈ T.headLevel H h) : tailFlux T p H y s = 0 := by
  have hsH := (Finset.mem_filter.mp hs).1
  have hsh := (Finset.mem_filter.mp hs).2
  have hc : T.children s = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    have hlt := T.child_depth hc
    have hle := hheight c
    omega
  rw [tailFlux, ite_eq_left hsH]
  have hz : T.pField p y true s = 0 := by
    change (T.pfields p y s).1 = 0
    rw [T.pfields_eq p y s, hc]
    simp [leastPair, hy s hsH]
  rw [hz, Real.zero_rpow p.ne_zero]

include hH hx hy hstep in
lemma tail_le_cutEnergy (hp : 1 < p.val) {h : ℕ} (hheight : ∀ s, T.depth s ≤ h) :
    T.pRootSum p y ≤ 2 * cutEnergy T p.val H (increment T p H x y) h := by
  have hd := increment_nonneg T p hH hx hy
  have hmass := T.root_le_sum_exitCut hH hstep (tailFlux T p H y) (tailFlux_local T p hy) h
  rw [tailFlux, ite_eq_left hH.1] at hmass
  have hexit : (∑ s ∈ T.stoppedExit H h, tailFlux T p H y s) =
      ∑ σ, ∑ s ∈ T.stoppedExit H h, increment T p H x y σ s ^ p.val := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    have hsH := (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2.1
    rw [tailFlux, ite_eq_right hsH, exit_sign_mass T p hH hx s hsH]
  have hterminal : (∑ s ∈ T.headLevel H h, tailFlux T p H y s) = 0 :=
    Finset.sum_eq_zero fun s hs => tailFlux_head_terminal T p hy hheight s hs
  rw [FiniteRootedTree.exitCut, Finset.sum_union (T.headLevel_stopped_disjoint H h), hterminal,
    zero_add, hexit] at hmass
  have hmass' : T.pField p y true T.root ^ p.val ≤
      cutEnergy T p.val H (increment T p H x y) h ^ p.val := by
    rw [cutEnergy_pow T hp H _ hd]
    apply hmass.trans
    apply Finset.sum_le_sum
    intro σ hσ
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun s hs => Finset.mem_union_right _ hs)
      (fun s _ _ => Real.rpow_nonneg (hd σ s) _)
  have hroot := (Real.rpow_le_rpow_iff (T.pField_nonneg p y true T.root)
    (cutEnergy_nonneg T p.val H _ hd h) p.pos).mp hmass'
  have he := T.pfields_difference p y T.root
  rw [hy T.root hH.1] at he
  change (T.pfields p y T.root).1 + (T.pfields p y T.root).2 ≤ _
  change (T.pfields p y T.root).1 ≤ _ at hroot
  linarith

include hH hx hy in
lemma cutEnergy_zero_le_gap (hp : 1 < p.val) :
    cutEnergy T p.val H (increment T p H x y) 0 ≤
      (T.pRootSum p (x+y) + T.pRootSum p (x-y)) / 2 - T.pRootSum p x := by
  have hd := increment_nonneg T p hH hx hy
  have hroot : cutEnergy T p.val H (increment T p H x y) 0 ≤
      increment T p H x y true T.root + increment T p H x y false T.root := by
    apply (Real.rpow_le_rpow_iff (cutEnergy_nonneg T p.val H _ hd 0)
      (add_nonneg (hd true T.root) (hd false T.root)) p.pos).mp
    rw [cutEnergy_pow T hp H _ hd, T.exitCut_zero hH]
    simp only [Finset.sum_singleton, Fintype.sum_bool]
    exact Real.add_rpow_le_rpow_add (hd true T.root) (hd false T.root) p.one_le
  have ht := common_increment T p (x := x) hy true true T.root hH.1
  have ht' := common_increment T p (x := x) hy true false T.root hH.1
  have hf := common_increment T p (x := x) hy false true T.root hH.1
  have hf' := common_increment T p (x := x) hy false false T.root hH.1
  simp only [signed_true, signed_false, ← sub_eq_add_neg, FiniteRootedTree.pField,
    ite_true, Bool.false_eq_true, ite_false] at ht ht' hf hf'
  unfold FiniteRootedTree.pRootSum
  linarith

theorem finite_cubic_normalized (h : ℕ+) (hp : p.val = heightExponent h)
    (hH : T.Initial H) (hx : ∀ s ∉ H, x s = 0) (hy : ∀ s ∈ H, y s = 0)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (hheight : ∀ s, T.depth s ≤ h.val)
    (hM : ∀ σ, T.pRootSum p (x + signed y σ) ≤ 1) :
    cubicConstant * T.pRootSum p y ^ 3 ≤
      (T.pRootSum p (x+y) + T.pRootSum p (x-y)) / 2 - T.pRootSum p x := by
  have hp' : 1 < p.val := hp ▸ heightExponent_gt_one h
  let K := cutEnergy T p.val H (increment T p H x y)
  have hd := increment_nonneg T p hH hx hy
  have hK := cutEnergy_nonneg T p.val H _ hd
  have hrec : ∀ j < h.val, K (j+1) ^ heightExponent h ≤
      heightExponent h * (3:ℝ) ^ ((heightExponent h - 1) / heightExponent h) * K j := by
    intro j hj
    rw [← hp]
    exact accumulated_cut_recursion T hp' hH hstep _ _ (coefficient_nonneg T p hH hx hy) hd
      (fun σ s hs => layer_increment T p hH hx hy hp' σ s hs)
      (fun σ s hs => by rw [coefficient, ite_eq_right hs]) j
      (total_coefficient_mass T p hH hx hy hstep hM j)
  have hY : T.pRootSum p y ≤ 1 := by
    have hm := T.pRootSum_tail_midpoint p x y
    have h₁ := hM true; have h₂ := hM false
    simp only [signed_true, signed_false, ← sub_eq_add_neg] at h₁ h₂
    linarith
  have hb := cubic_of_accumulated h K hK hrec (T.pRootSum_nonneg p y) hY
    (tail_le_cutEnergy T p hH hx hy hstep hp' hheight)
  exact hb.trans (cutEnergy_zero_le_gap T p hH hx hy hp')

lemma signed_smul {ι : Type uIndex} [Fintype ι] [DecidableEq ι] (a : ℝ) (y : ι → ℝ) (σ : Bool) :
    signed (a • y) σ = a • signed y σ := by
  cases σ <;> simp [signed]

theorem finite_cubic (h : ℕ+) (hp : p.val = heightExponent h)
    (hH : T.Initial H) (hx : ∀ s ∉ H, x s = 0) (hy : ∀ s ∈ H, y s = 0)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (hheight : ∀ s, T.depth s ≤ h.val) :
    cubicConstant * T.pRootSum p y ^ 3 ≤
      ((T.pRootSum p (x+y) + T.pRootSum p (x-y)) / 2 - T.pRootSum p x) *
        max (T.pRootSum p (x+y)) (T.pRootSum p (x-y)) ^ 2 := by
  let M := max (T.pRootSum p (x+y)) (T.pRootSum p (x-y))
  have hM0 : 0 ≤ M := (T.pRootSum_nonneg p (x+y)).trans (le_max_left _ _)
  by_cases hm : M = 0
  · have hY := T.pRootSum_tail_midpoint p x y
    have h₁ : T.pRootSum p (x+y) ≤ 0 := (le_max_left _ _).trans_eq hm
    have h₂ : T.pRootSum p (x-y) ≤ 0 := (le_max_right _ _).trans_eq hm
    have hy0 : T.pRootSum p y = 0 := le_antisymm (by linarith) (T.pRootSum_nonneg p y)
    change _ ≤ _ * M ^ 2
    rw [hm, hy0]; norm_num
  · have hM : 0 < M := lt_of_le_of_ne hM0 (Ne.symm hm)
    have hi : 0 ≤ M⁻¹ := inv_nonneg.mpr hM0
    have hnorm : ∀ v, T.pRootSum p (M⁻¹ • v) = M⁻¹ * T.pRootSum p v :=
      fun v => T.pRootSum_smul_nonneg p v hi
    have hep : ∀ σ, (M⁻¹ • x) + signed (M⁻¹ • y) σ = M⁻¹ • (x + signed y σ) := by
      intro σ; rw [signed_smul, smul_add]
    have hends : ∀ σ, T.pRootSum p ((M⁻¹ • x) + signed (M⁻¹ • y) σ) ≤ 1 := by
      intro σ
      rw [hep, hnorm]
      have hle : T.pRootSum p (x+signed y σ) ≤ M := by
        cases σ
        · simpa only [signed_false, sub_eq_add_neg, M] using le_max_right (T.pRootSum p (x+y)) (T.pRootSum p (x-y))
        · exact le_max_left _ _
      calc
        _ ≤ M⁻¹ * M := mul_le_mul_of_nonneg_left hle hi
        _ = 1 := inv_mul_cancel₀ hm
    have hb := finite_cubic_normalized T p h hp hH
      (x := M⁻¹ • x) (y := M⁻¹ • y)
      (fun s hs => by simp [hx s hs]) (fun s hs => by simp [hy s hs]) hstep hheight hends
    have hplus : M⁻¹ • x + M⁻¹ • y = M⁻¹ • (x+y) := (smul_add _ _ _).symm
    have hminus : M⁻¹ • x - M⁻¹ • y = M⁻¹ • (x-y) := (smul_sub _ _ _).symm
    simp only [hplus, hminus, hnorm] at hb
    let D := (T.pRootSum p (x+y) + T.pRootSum p (x-y)) / 2 - T.pRootSum p x
    have hdiv : cubicConstant * T.pRootSum p y ^ 3 / M ^ 3 ≤ D / M := by
      convert hb using 1 <;> (try dsimp only [D]) <;> ring
    have hresult := (div_le_iff₀ (pow_pos hM 3)).mp hdiv
    have heq : D / M * M ^ 3 = D * M ^ 2 := by field_simp
    rw [heq] at hresult
    exact hresult

end

end VariableExponent

end RecursivePotentials

end OAI

-- ---- platform node ----
open OAI OAI.RecursivePotentials OAI.RecursivePotentials.VariableExponent
open scoped BigOperators
open Filter Topology
open Filter Topology
open scoped ENNReal
open UniformSpace
open Filter
open scoped Topology


theorem solution.{uIndex} : type_of% @_root_.OAI.RecursivePotentials.VariableExponent.finite_cubic.{uIndex} := @_root_.OAI.RecursivePotentials.VariableExponent.finite_cubic.{uIndex}
