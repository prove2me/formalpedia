-- Prove2me | solution 1 for OAI.TreeEdit.TorusTree.fixed_residue_failure
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:47:11.272882+00:00
-- url     : https://prove2.me/submissions/d29154ad-03e4-47fe-b8b1-af6119fc8336

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/CircleTree.lean:L329-L401
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.TorusTree.fixed_residue_failure. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Theorems.Thm_OAI_TreeEdit_FiniteProbability_hom_uniform
import Theorems.Thm_OAI_TreeEdit_FiniteProbability_independent_lower_tail_subset

-- ---- from OAI.Combinatorics.TreeEdit.FiniteProbability ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

namespace TreeEdit.FiniteProbability
open scoped BigOperators
open Classical

lemma mean_nonneg {A : Type*} [Fintype A] {f : A → ℝ} (hf : ∀ a, 0 ≤ f a) :
    0 ≤ mean f := mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg (fun a _ => hf a))

lemma mean_le {A : Type*} [Fintype A] {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    mean f ≤ mean g := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => h a)) (by positivity)

lemma mean_const {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) : mean (fun _ : A => c) = c := by
  simp only [mean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

lemma mean_add {A : Type*} [Fintype A] (f g : A → ℝ) :
    mean (fun a => f a + g a) = mean f + mean g := by simp [mean, Finset.sum_add_distrib, mul_add]

lemma mean_mul_const {A : Type*} [Fintype A] (f : A → ℝ) (c : ℝ) :
    mean (fun a => f a * c) = mean f * c := by simp [mean, Finset.sum_mul, mul_assoc]

lemma mean_sum {A I : Type*} [Fintype A] (s : Finset I) (f : I → A → ℝ) :
    mean (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, mean (f i) := by
  simp only [mean, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma probability_nonneg {A : Type*} [Fintype A] (E : A → Prop) : 0 ≤ probability E := by
  classical
  exact mean_nonneg (fun _ => by split_ifs <;> norm_num)

lemma probability_not {A : Type*} [Fintype A] [Nonempty A] (E : A → Prop) :
    probability (fun a => ¬ E a) = 1 - probability E := by
  classical
  have hh : probability E + probability (fun a => ¬ E a) = 1 := by
    rw [probability, probability, ← mean_add]
    calc
      _ = mean (fun _ : A => (1 : ℝ)) := by
        apply congrArg mean
        funext a
        by_cases h : E a <;> simp [h]
      _ = 1 := mean_const 1
  linarith

lemma probability_mono {A : Type*} [Fintype A] {E F : A → Prop} (h : ∀ a, E a → F a) :
    probability E ≤ probability F := by
  classical
  apply mean_le
  intro a
  by_cases he : E a <;> by_cases hf : F a <;> simp_all

lemma mean_pair {A B : Type*} [Fintype A] [Fintype B] (f : A × B → ℝ) :
    mean f = mean (fun a => mean (fun b => f (a, b))) := by
  simp only [mean, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma probability_eq {A : Type*} [Fintype A] (a : A) :
    probability (· = a) = (Fintype.card A : ℝ)⁻¹ := by
  simp [probability, mean]

lemma mean_fiberwise {A B : Type*} [Fintype A] [Fintype B] (f : A → B) (g : B → ℝ) :
    mean (fun a => g (f a)) = ∑ b : B, probability (fun a => f a = b) * g b := by
  have he (a : A) : g (f a) = ∑ b : B, (if f a = b then (1 : ℝ) else 0) * g b := by simp
  simp_rw [probability, ← mean_mul_const]
  rw [← mean_sum]
  apply congrArg mean
  funext a
  exact he a

lemma probability_comp_uniform {A B : Type*} [Fintype A] [Fintype B] (f : A → B)
    (hf : ∀ b, probability (fun a => f a = b) = (Fintype.card B : ℝ)⁻¹) (E : B → Prop) :
    probability (fun a => E (f a)) = probability E := by
  rw [probability, mean_fiberwise f (fun b => if E b then (1 : ℝ) else 0)]
  simp_rw [hf]
  simp only [probability, mean, Finset.mul_sum]

lemma probability_subsingleton {A : Type*} [Fintype A] (E : A → Prop)
    (hE : ∀ a b, E a → E b → a = b) : probability E ≤ (Fintype.card A : ℝ)⁻¹ := by
  by_cases h : ∃ a, E a
  · obtain ⟨a, ha⟩ := h
    exact (probability_mono (fun b hb => hE b a hb ha)).trans_eq (probability_eq a)
  · have hz : probability E = 0 := by simp [probability, mean, not_exists.mp h]
    rw [hz]
    positivity

lemma probability_pair {A B : Type*} [Fintype A] [Fintype B] (E : A × B → Prop) :
    probability E = mean (fun a => probability (fun b => E (a, b))) := mean_pair _

lemma pair_success_lower {A Z : Type*} [Fintype A] [Fintype Z]
    (E : Z → Prop) (F : Z → A → Prop) {p : ℝ}
    (h : ∀ z, E z → p ≤ probability (F z)) :
    p * probability E ≤ probability (fun a : Z × A => F a.1 a.2) := by
  rw [probability_pair, mul_comm p, probability, ← mean_mul_const]
  apply mean_le
  intro z
  by_cases hz : E z
  · simpa [hz] using h z hz
  · simpa [hz] using probability_nonneg (F z)

end TreeEdit.FiniteProbability

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.CircleTree ----
namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical

lemma point_mul {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (h : d ∣ n) :
    (n / d) • point n = point d := by
  simp only [point, ← AddCircle.coe_nsmul, nsmul_eq_mul]
  congr 1
  rw [Nat.cast_div h (by exact_mod_cast hd.ne')]
  field_simp

lemma nsmul_point_eq (n a : ℕ) : a • point n = ↑((a : ℝ) / n) := by
  simp only [point, ← AddCircle.coe_nsmul, nsmul_eq_mul, div_eq_mul_inv]

lemma point_toAddCircle {n : ℕ} [NeZero n] (a : ZMod n) :
    a.val • point n = ZMod.toAddCircle a := by
  rw [nsmul_point_eq, ZMod.toAddCircle_apply]

lemma circle_period_lower {x : UnitAddCircle} {d : ℕ} (hd : 0 < d)
    (hx : d • x = 0) (hx0 : x ≠ 0) : 1 ≤ (d : ℝ) * ‖x‖ := by
  let : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have hf : IsOfFinAddOrder x := isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨d, hd, hx⟩
  have hh := AddCircle.le_add_order_smul_norm_of_isOfFinAddOrder hf hx0
  simp only [nsmul_eq_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast addOrderOf_le_of_nsmul_eq_zero hd hx) (norm_nonneg _))

lemma grid_nearby_unique {r : ℕ} [NeZero r] {t : UnitAddCircle} {ε : ℝ}
    (hε : 2 * ε * (r : ℝ) < 1) {a b : ZMod r}
    (ha : ‖t + ZMod.toAddCircle a‖ < ε) (hb : ‖t + ZMod.toAddCircle b‖ < ε) : a = b := by
  apply ZMod.toAddCircle_injective r
  by_contra hn
  have hp : r • (ZMod.toAddCircle a - ZMod.toAddCircle b) = 0 := by
    rw [← map_sub, ← map_nsmul]
    simp [nsmul_eq_mul]
  have hh := circle_period_lower (NeZero.pos _) hp (sub_ne_zero.mpr hn)
  have hnorm : ‖ZMod.toAddCircle a - ZMod.toAddCircle b‖ < 2 * ε := by
    calc
      _ = ‖(t + ZMod.toAddCircle a) - (t + ZMod.toAddCircle b)‖ := by congr 1; abel
      _ ≤ ‖t + ZMod.toAddCircle a‖ + ‖t + ZMod.toAddCircle b‖ := norm_sub_le _ _
      _ < _ := by linarith
  have hr : (0 : ℝ) < r := by exact_mod_cast NeZero.pos r
  nlinarith

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

lemma dense_grid_bad {L r a : ℕ} [NeZero L] [NeZero r] (hr : Nat.Prime r) (hrL : r ∣ L)
    (ha : ¬ r ∣ a) {t : UnitAddCircle} {ε : ℝ} (hε : 2 * ε * r < 1) :
    probability (fun z : ZMod L =>
      ‖t + ZMod.toAddCircle ((a : ZMod r) * ZMod.castHom hrL (ZMod r) z)‖ < ε) ≤ (r : ℝ)⁻¹ := by
  let : Fact (Nat.Prime r) := ⟨hr⟩
  let f : ZMod L →+ ZMod r := (AddMonoidHom.mulLeft (a : ZMod r)).comp
    (ZMod.castHom hrL (ZMod r)).toAddMonoidHom
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨z, hz⟩ := ZMod.castHom_surjective hrL ((a : ZMod r)⁻¹ * b)
    refine ⟨z, ?_⟩
    change (a : ZMod r) * ZMod.castHom hrL (ZMod r) z = b
    rw [hz, ← mul_assoc, mul_inv_cancel₀ ((ZMod.natCast_eq_zero_iff a r).not.mpr ha), one_mul]
  calc
    _ = probability (fun b : ZMod r => ‖t + ZMod.toAddCircle b‖ < ε) :=
      probability_comp_uniform f (hom_uniform f hf) _
    _ ≤ (Fintype.card (ZMod r) : ℝ)⁻¹ := probability_subsingleton _ (fun _ _ => grid_nearby_unique hε)
    _ = _ := by rw [ZMod.card]

lemma dense_grid_eligible {L r a : ℕ} [NeZero L] [NeZero r] (hr : Nat.Prime r) (hrL : r ∣ L)
    (ha : ¬ r ∣ a) {t : UnitAddCircle} {ε : ℝ} (hε : 2 * ε * r < 1)
    (hr10 : 10 ≤ r) :
    9 / 10 ≤ probability (fun z : ZMod L =>
      ε ≤ ‖t + ZMod.toAddCircle ((a : ZMod r) * ZMod.castHom hrL (ZMod r) z)‖) := by
  have hh := dense_grid_bad (t := t) hr hrL ha hε
  have hn := probability_not (fun z : ZMod L =>
      ‖t + ZMod.toAddCircle ((a : ZMod r) * ZMod.castHom hrL (ZMod r) z)‖ < ε)
  simp only [not_lt] at hn
  rw [hn]
  have hi : (r : ℝ)⁻¹ ≤ (10 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by exact_mod_cast hr10)
  norm_num at hi
  linarith

lemma coefficient_circle {P r : ℕ} [NeZero r] (hP : 0 < P) (hr : 0 < r) (hd : r ∣ P)
    (a : ℕ) (z : ZMod r) :
    (a * (1 + z.val * (P / r))) • point P =
      a • point P + ZMod.toAddCircle ((a : ZMod r) * z) := by
  rw [Nat.mul_add, Nat.mul_one, add_smul]
  congr 1
  rw [mul_smul, mul_smul, point_mul hP hr hd, point_toAddCircle]
  rw [← map_nsmul]
  congr 1
  simp only [nsmul_eq_mul]

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

lemma group_card {g s : ℕ} (S : Finset (Fin g)) :
    (Finset.univ.filter (fun i : Fin (g * s) => group i ∈ S)).card = S.card * s := by
  rw [Finset.card_filter, ← (finProdFinEquiv (m := g) (n := s)).sum_comp]
  simp only [group, Equiv.symm_apply_apply, Fintype.sum_prod_type]
  calc
    _ = ∑ x : Fin g, s * (if x ∈ S then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ S <;> simp [hx]
    _ = s * S.card := by rw [← Finset.mul_sum, Finset.sum_boole]; simp
    _ = _ := Nat.mul_comm _ _

lemma period_pos {I : Type} {g : ℕ} {r : I → ℕ} (hr : ∀ i, 0 < r i)
    (j : Fin g → I) (σ : Equiv.Perm I) : 0 < period r j σ := product_positive _ (fun _ => hr _)

lemma group_prime_dvd {I : Type} {g : ℕ} (r : I → ℕ) (j : Fin g → I)
    (σ : Equiv.Perm I) (v : Fin g) : r (σ (j v)) ∣ period r j σ :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ v)

lemma cast_hom_val {L r : ℕ} [NeZero L] (hrL : r ∣ L) (z : ZMod L) :
    ZMod.castHom hrL (ZMod r) z = (z.val : ZMod r) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  simp only [map_natCast]

lemma coefficient_shift {I : Type} [Fintype I] {g s : ℕ} (r : I → ℕ)
    (hr : ∀ i, 0 < r i) (j : Fin g → I) (σ : Equiv.Perm I)
    {L : ℕ} [NeZero L] (hL : ∀ i, r i ∣ L) (i : Fin (g * s))
    [NeZero (r (σ (j (group i))))] (a : ℕ) (z : ZMod L) :
    (a * coefficient r j σ z i) • point (period r j σ) =
      a • point (period r j σ) +
        ZMod.toAddCircle ((a : ZMod (r (σ (j (group i))))) *
          ZMod.castHom (hL _) (ZMod (r (σ (j (group i))))) z) := by
  have hv : (ZMod.castHom (hL _) (ZMod (r (σ (j (group i))))) z).val =
      z.val % r (σ (j (group i))) := by rw [cast_hom_val, ZMod.val_natCast]
  change (a * (1 + _ * _)) • _ = _
  rw [← hv]
  exact coefficient_circle (period_pos hr j σ) (hr _) (group_prime_dvd r j σ _) a _

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

lemma fixed_residue_failure {I : Type} [Fintype I] {k s L h : ℕ} [NeZero L]
    (r : I → ℕ) (hr : ∀ i, Nat.Prime (r i)) (hr10 : ∀ i, 10 ≤ r i)
    (hL : ∀ i, r i ∣ L) (j : Fin (16 * k) ↪ I)
    {ε : ℝ} (hgrid : ∀ i, 2 * ε * r i < 1)
    (ih : ∀ t : UnitAddCircle, ε ≤ ‖t‖ → 9 / 10 ≤
      probability (fun C : Config I L (16 * k * s) h => Good ε r j h C t))
    (σ : Equiv.Perm I) (t : UnitAddCircle)
    (hlist : ∀ a : ℕ, (Finset.univ.filter (fun v : Fin (16 * k) => ¬ r (σ (j v)) ∣ a)).card ≤ k →
      ε ≤ ‖t + a • point (period r j σ)‖) (a : Fin (period r j σ)) :
    probability (fun C : Fin (16 * k * s) → ZMod L × Config I L (16 * k * s) h =>
      ¬ 16 * k * s ≤ 64 * (Finset.univ.filter (fun i =>
        Good ε r j h (C i).2 (t + (a.val * coefficient r j σ (C i).1 i) • point (period r j σ)))).card) ≤
      (4 / 5 : ℝ) ^ (k * s) := by
  let S := Finset.univ.filter (fun v : Fin (16 * k) => ¬ r (σ (j v)) ∣ a.val)
  let V := if S.card ≤ k then Sᶜ else S
  let J := Finset.univ.filter (fun i : Fin (16 * k * s) => group i ∈ V)
  let E (i : Fin (16 * k * s)) (C : ZMod L × Config I L (16 * k * s) h) : Prop :=
    Good ε r j h C.2 (t + (a.val * coefficient r j σ C.1 i) • point (period r j σ))
  have hn : k * s ≤ J.card := by
    have hv : k ≤ V.card := by
      dsimp [V]
      split_ifs with hs
      · rw [Finset.card_compl, Fintype.card_fin]
        omega
      · omega
    have hc := group_card (s := s) V
    exact (Nat.mul_le_mul_right s hv).trans_eq hc.symm
  have hE (i : Fin (16 * k * s)) (hi : i ∈ J) : 4 / 5 ≤ probability (E i) := by
    let p := r (σ (j (group i)))
    have hp : Nat.Prime p := hr _
    let : NeZero p := ⟨hp.ne_zero⟩
    have hg : group i ∈ V := (Finset.mem_filter.mp hi).2
    let sh (z : ZMod L) : UnitAddCircle := t + (a.val * coefficient r j σ z i) • point (period r j σ)
    have hsh (z : ZMod L) : sh z = t + a.val • point (period r j σ) +
        ZMod.toAddCircle ((a.val : ZMod p) * ZMod.castHom (hL _) (ZMod p) z) := by
      dsimp [sh]
      rw [coefficient_shift r (fun v => (hr v).pos) j σ hL i, ← add_assoc]
      simp only [ZMod.castHom_apply]
    have helig : 9 / 10 ≤ probability (fun z : ZMod L => ε ≤ ‖sh z‖) := by
      by_cases hs : S.card ≤ k
      · have hd : p ∣ a.val := by
          have hnot : group i ∉ S := Finset.mem_compl.mp (by simpa [V, hs] using hg)
          simpa [S, p] using hnot
        have he : ∀ z : ZMod L, ε ≤ ‖sh z‖ := by
          intro z
          rw [hsh, (ZMod.natCast_eq_zero_iff a.val p).mpr hd, zero_mul, map_zero, add_zero]
          exact hlist a.val hs
        have hh : probability (fun z : ZMod L => ε ≤ ‖sh z‖) = 1 := by simp [probability, he, mean_const]
        rw [hh]
        norm_num
      · have hd : ¬ p ∣ a.val := by
          have hin : group i ∈ S := by simpa [V, hs] using hg
          exact (Finset.mem_filter.mp hin).2
        have hh := dense_grid_eligible (t := t + a.val • point (period r j σ))
          hp (hL _) hd (hgrid _) (hr10 _)
        simpa only [hsh] using hh
    have hh := pair_success_lower (fun z : ZMod L => ε ≤ ‖sh z‖)
      (fun z (C : Config I L (16 * k * s) h) => Good ε r j h C (sh z))
      (p := (9 : ℝ) / 10) (fun z hz => ih (sh z) hz)
    change 9 / 10 * probability (fun z : ZMod L => ε ≤ ‖sh z‖) ≤ probability (E i) at hh
    nlinarith
  have hh := independent_lower_tail_subset E J hn hE
  calc
    _ ≤ probability (fun C : Fin (16 * k * s) → ZMod L × Config I L (16 * k * s) h =>
      4 * (Finset.univ.filter (fun i => E i (C i))).card < k * s) := probability_mono (by
        intro C hC
        change ¬ 16 * k * s ≤ 64 * (Finset.univ.filter (fun i => E i (C i))).card at hC
        have hh : 16 * k * s = 16 * (k * s) := by ring
        omega)
    _ ≤ _ := by
      convert hh using 1
      congr 1
      exact Subsingleton.elim _ _

end TreeEdit.TorusTree

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability


theorem solution : type_of% @_root_.OAI.TreeEdit.TorusTree.fixed_residue_failure := @_root_.OAI.TreeEdit.TorusTree.fixed_residue_failure
