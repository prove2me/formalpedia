-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Nibble.one_round
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:49:49.701706+00:00
-- url     : https://prove2.me/submissions/4403bf10-56d4-4611-a445-542f29bed270

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Nibble.lean:L540-L694
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Nibble.one_round. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Nibble_degree_loss_deleting
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Nibble_exists_controlled_outcome
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Nibble_expectation_noHit
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Nibble_noHit_sum_variance
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Nibble_residual_degree_variance
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Nibble_residual_mean_estimate

-- ---- from OAI.Analysis.Littlewood.ProductProbability ----
namespace OAI

universe uE uI

namespace AsymptoticallyMinimalLittlewood
namespace Nibble
open scoped BigOperators
open Finset

section ProductSpace
variable {E : Type uE} [Fintype E] [DecidableEq E]

lemma expectation_prod (p : ℝ) (g : E → Bool → ℝ) :
    expectation p (fun s ↦ ∏ e, g e (s e)) =
      ∏ e, (p * g e true + (1 - p) * g e false) := by
  dsimp [expectation, coinWeight]
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun e b ↦ (if b then p else 1 - p) * g e b)]
  simp

lemma coinWeight_sum (p : ℝ) : (∑ s : E → Bool, coinWeight p s) = 1 := by
  have h := expectation_prod (E := E) p (fun _ _ ↦ 1)
  simpa [expectation] using h

lemma expectation_const (p c : ℝ) : expectation (E := E) p (fun _ ↦ c) = c := by
  simp only [expectation, ← Finset.sum_mul, coinWeight_sum, one_mul]

lemma expectation_add (p : ℝ) (f g : (E → Bool) → ℝ) :
    expectation p (fun s ↦ f s + g s) = expectation p f + expectation p g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

lemma expectation_sub (p : ℝ) (f g : (E → Bool) → ℝ) :
    expectation p (fun s ↦ f s - g s) = expectation p f - expectation p g := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

lemma expectation_sum {I : Type uI} (p : ℝ) (S : Finset I) (f : I → (E → Bool) → ℝ) :
    expectation p (fun s ↦ ∑ i ∈ S, f i s) = ∑ i ∈ S, expectation p (f i) := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

lemma noHit_eq (A : Finset E) (s : E → Bool) :
    noHit A s = if ∀ e ∈ A, s e = false then 1 else 0 := by
  dsimp [noHit]
  split_ifs with h
  · apply Finset.prod_eq_one
    intro e he
    simp [h e he]
  · push Not at h
    obtain ⟨e, he, hs⟩ := h
    apply Finset.prod_eq_zero he
    cases hh : s e <;> simp_all

lemma noHit_union (A B : Finset E) (s : E → Bool) :
    noHit (A ∪ B) s = noHit A s * noHit B s := by
  simp only [noHit_eq, Finset.mem_union, or_imp, forall_and]
  split_ifs <;> simp_all

lemma one_sub_pow_le {p : ℝ} (_hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    1 - (1 - p) ^ n ≤ n * p := by
  have h := one_add_mul_le_pow (by linarith : -2 ≤ -p) n
  simp only [← sub_eq_add_neg] at h
  linarith

lemma pow_bonferroni {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (1 - p) ^ n - (1 - n * p) ≤ (n * p) ^ 2 / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hl := one_sub_pow_le hp hp1 n
    have hstep := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hp1)
    have he := mul_nonneg hp (sq_nonneg ((n : ℝ) * p))
    rw [pow_succ]
    push_cast
    nlinarith [sq_nonneg p]

omit [Fintype E] [DecidableEq E] in
lemma selectedIndicator_eq (e : E) (s : E → Bool) :
    selectedIndicator e s = 1 - noHit {e} s := by
  cases h : s e <;> simp [selectedIndicator, noHit, h]

omit [Fintype E] [DecidableEq E] in
lemma selectedIndicator_nonneg (e : E) (s : E → Bool) : 0 ≤ selectedIndicator e s := by
  dsimp [selectedIndicator]
  split_ifs <;> norm_num

lemma expectation_selected_mul (p : ℝ) (e f : E) (hef : e ≠ f) :
    expectation p (fun s ↦ selectedIndicator e s * selectedIndicator f s) = p^2 := by
  have heq (s : E → Bool) : selectedIndicator e s * selectedIndicator f s =
      1 - noHit {e} s - noHit {f} s + noHit ({e} ∪ {f}) s := by
    rw [noHit_union, selectedIndicator_eq, selectedIndicator_eq]
    ring
  simp_rw [heq]
  rw [expectation_add, expectation_sub, expectation_sub, expectation_const]
  simp only [expectation_noHit, Finset.card_singleton, pow_one]
  have hcard : ({e} ∪ {f} : Finset E).card = 2 := by simp [hef]
  rw [hcard]
  ring

end ProductSpace

end Nibble
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- from OAI.Analysis.Littlewood.Nibble ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

universe uI uE uV

namespace AsymptoticallyMinimalLittlewood
namespace Nibble
open scoped BigOperators
open Finset
section SetUnions
variable {I : Type uI} {E : Type uE} [DecidableEq I] [DecidableEq E]

omit [DecidableEq I] in
lemma card_biUnion_upper (S : Finset I) (A : I → Finset E) {D : ℝ}
    (hD : ∀ i ∈ S, ((A i).card : ℝ) ≤ D) :
    ((S.biUnion A).card : ℝ) ≤ S.card * D := by
  calc
    _ ≤ ∑ i ∈ S, ((A i).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ S, D := Finset.sum_le_sum hD
    _ = _ := by simp

end SetUnions

section Hypergraph
variable {V : Type uV} {E : Type uE} [DecidableEq V] [Fintype E] [DecidableEq E]

lemma untouched_card (U : Finset V) (S : Finset E) (A : E → Finset V) (s : E → Bool) :
    ((untouched U S A s).card : ℝ) = ∑ v ∈ U, noHit (incident S A v) s := by
  simp only [untouched, Finset.card_eq_sum_ones, Finset.sum_filter, noHit_eq,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

lemma untouched_variance (U : Finset V) (S : Finset E) (A : E → Finset V)
    {r : ℕ} {D p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : ∀ e ∈ S, (A e).card ≤ r)
    (hdeg : ∀ v ∈ U, ((incident S A v).card : ℝ) ≤ D) :
    let Y : (E → Bool) → ℝ := fun s ↦ ((untouched U S A s).card : ℝ)
    expectation p (fun s ↦ (Y s - expectation p Y)^2) ≤ p * U.card * D * r := by
  dsimp only
  simp_rw [untouched_card]
  apply noHit_sum_variance hp hp1 U (incident S A) (Nat.cast_nonneg r) hdeg
  intro e
  by_cases he : e ∈ S
  · have hsub : (U.filter fun v ↦ e ∈ incident S A v) ⊆ A e := by
      intro v hv
      exact (mem_incident S A v e |>.mp (Finset.mem_filter.mp hv).2).2
    exact_mod_cast (Finset.card_le_card hsub).trans (hr e he)
  · have hz : (U.filter fun v ↦ e ∈ incident S A v) = ∅ := by
      ext v
      simp [he]
    rw [hz]
    simp

lemma untouched_mean_upper (U : Finset V) (S : Finset E) (A : E → Finset V)
    {D Emax p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hE : 0 ≤ Emax)
    (hdeg : ∀ v ∈ U, D ≤ ((incident S A v).card : ℝ) ∧
      ((incident S A v).card : ℝ) ≤ Emax) :
    expectation p (fun s ↦ ((untouched U S A s).card : ℝ)) ≤
      U.card * (1 - p * D + (p * Emax)^2 / 2) := by
  simp_rw [untouched_card]
  rw [expectation_sum]
  calc
    _ ≤ ∑ _v ∈ U, (1 - p * D + (p * Emax)^2 / 2) := by
      apply Finset.sum_le_sum
      intro v hv
      rw [expectation_noHit]
      have hb := pow_bonferroni hp hp1 (incident S A v).card
      have hd := mul_le_mul_of_nonneg_left (hdeg v hv).1 hp
      have hu := mul_le_mul_of_nonneg_left (hdeg v hv).2 hp
      have hs : (p * ((incident S A v).card : ℝ))^2 ≤ (p*Emax)^2 :=
        (sq_le_sq₀ (by positivity) (mul_nonneg hp hE)).mpr hu
      nlinarith
    _ = _ := by simp; ring

omit [Fintype E] [DecidableEq E] in
lemma incident_restrict (S : Finset E) (A : E → Finset V) (W : Finset V) (v : V) :
    incident (restrictEdges S A W) A v = (incident S A v).filter fun e ↦ A e ⊆ W := by
  ext e
  simp [incident, restrictEdges, and_left_comm, and_comm]

lemma residual_degree_eq (U : Finset V) (S : Finset E) (A : E → Finset V)
    (hsub : ∀ e ∈ S, A e ⊆ U) (s : E → Bool) (v : V) (hv : v ∈ untouched U S A s) :
    ((incident (restrictEdges S A (untouched U S A s)) A v).card : ℝ) =
      ∑ e ∈ incident S A v, noHit (hits S A ((A e).erase v)) s := by
  have hvs : ∀ e ∈ incident S A v, s e = false := (Finset.mem_filter.mp hv).2
  rw [incident_restrict]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, noHit_eq]
  apply Finset.sum_congr rfl
  intro e he
  congr 1
  apply propext
  constructor
  · intro hW f hf
    obtain ⟨hfS, w, hw, hwe⟩ := mem_hits S A ((A e).erase v) f |>.mp hf
    exact (Finset.mem_filter.mp (hW (Finset.mem_of_mem_erase hw))).2 f
      (mem_incident S A w f |>.mpr ⟨hfS, hwe⟩)
  · intro hN w hw
    apply Finset.mem_filter.mpr
    refine ⟨hsub e (mem_incident S A v e |>.mp he).1 hw, ?_⟩
    intro f hf
    by_cases hwv : w = v
    · exact hvs f (hwv ▸ hf)
    · exact hN f (mem_hits S A ((A e).erase v) f |>.mpr
        ⟨(mem_incident S A w f |>.mp hf).1, w, Finset.mem_erase.mpr ⟨hwv, hw⟩,
          (mem_incident S A w f |>.mp hf).2⟩)

omit [Fintype E] in
lemma collisionCount_nonneg (U : Finset V) (S : Finset E) (A : E → Finset V) (s : E → Bool) :
    0 ≤ collisionCount U S A s := by
  apply Finset.sum_nonneg
  intro v hv
  apply Finset.sum_nonneg
  intro e he
  apply Finset.sum_nonneg
  intro f hf
  exact mul_nonneg (selectedIndicator_nonneg e s) (selectedIndicator_nonneg f s)

lemma collisionCount_mean (U : Finset V) (S : Finset E) (A : E → Finset V)
    {p D : ℝ} (hD : 0 ≤ D) (hdeg : ∀ v ∈ U, ((incident S A v).card : ℝ) ≤ D) :
    expectation p (collisionCount U S A) ≤ p^2 * U.card * D^2 := by
  change expectation p (fun s ↦ ∑ v ∈ U, ∑ e ∈ incident S A v,
    ∑ f ∈ (incident S A v).erase e, selectedIndicator e s * selectedIndicator f s) ≤ _
  simp_rw [expectation_sum]
  calc
    _ ≤ ∑ v ∈ U, (p^2 * D^2) := by
      apply Finset.sum_le_sum
      intro v hv
      calc
        _ = ∑ e ∈ incident S A v, ∑ f ∈ (incident S A v).erase e, p^2 := by
          apply Finset.sum_congr rfl
          intro e he
          apply Finset.sum_congr rfl
          intro f hf
          exact expectation_selected_mul p e f (Ne.symm (Finset.mem_erase.mp hf).1)
        _ ≤ ∑ e ∈ incident S A v, (incident S A v).card * p^2 := by
          apply Finset.sum_le_sum
          intro e he
          simp only [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr Finset.card_erase_le) (sq_nonneg p)
        _ = p^2 * ((incident S A v).card : ℝ)^2 := by simp; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ (Nat.cast_nonneg _) hD).mpr (hdeg v hv)) (sq_nonneg p)
    _ = _ := by simp; ring

omit [Fintype E] in
lemma colliding_card_le (U : Finset V) (S : Finset E) (A : E → Finset V)
    (hsub : ∀ e ∈ S, A e ⊆ U) (s : E → Bool) :
    ((colliding S A s).card : ℝ) ≤ collisionCount U S A s := by
  classical
  let T : E → V → ℝ := fun e v ↦ if v ∈ A e then
    ∑ f ∈ (incident S A v).erase e, selectedIndicator e s * selectedIndicator f s else 0
  have hT : ∀ e v, 0 ≤ T e v := by
    intro e v
    dsimp [T]
    split_ifs
    · exact Finset.sum_nonneg fun f _ ↦
        mul_nonneg (selectedIndicator_nonneg e s) (selectedIndicator_nonneg f s)
    · rfl
  have hid : collisionCount U S A s = ∑ e ∈ S, ∑ v ∈ U, T e v := by
    dsimp [collisionCount, T, incident]
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [hid]
  simp only [colliding, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_le_sum
  intro e he
  split_ifs with h
  · obtain ⟨hs, f, hf, hfe, hfs, hinter⟩ := h
    obtain ⟨v, hve, hvf⟩ := Finset.not_disjoint_iff.mp hinter
    have hvU := hsub e he hve
    have hfinc : f ∈ (incident S A v).erase e :=
      Finset.mem_erase.mpr ⟨hfe, mem_incident S A v f |>.mpr ⟨hf, hvf⟩⟩
    have hb : (1 : ℝ) ≤ T e v := by
      dsimp [T]
      rw [ite_eq_left hve]
      have hh := Finset.single_le_sum (fun g hg ↦
        mul_nonneg (selectedIndicator_nonneg e s) (selectedIndicator_nonneg g s)) hfinc
      simpa [selectedIndicator, hs, hfs] using hh
    exact hb.trans (Finset.single_le_sum (fun w _ ↦ hT e w) hvU)
  · exact Finset.sum_nonneg fun v hv ↦ hT e v

lemma isolated_pairwise (S : Finset E) (A : E → Finset V) (s : E → Bool) :
    (isolated S A s : Set E).Pairwise (fun e f ↦ Disjoint (A e) (A f)) := by
  intro e he f hf hef
  have hE := Finset.mem_filter.mp he
  have hF := Finset.mem_filter.mp hf
  exact hE.2.2 f hF.1 hef.symm hF.2.1

lemma isolated_untouched_disjoint (U : Finset V) (S : Finset E) (A : E → Finset V)
    (s : E → Bool) : Disjoint ((isolated S A s).biUnion A) (untouched U S A s) := by
  apply Finset.disjoint_left.mpr
  intro v hv hvW
  obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
  have heS := (Finset.mem_filter.mp he).1
  have hsel := (Finset.mem_filter.mp he).2.1
  have hno := (Finset.mem_filter.mp hvW).2 e (mem_incident S A v e |>.mpr ⟨heS, hve⟩)
  simp_all

lemma wasted_vertices_le (U : Finset V) (S : Finset E) (A : E → Finset V)
    {r : ℕ} (hsub : ∀ e ∈ S, A e ⊆ U) (hr : ∀ e ∈ S, (A e).card ≤ r)
    (s : E → Bool) :
    ((U \ (untouched U S A s ∪ (isolated S A s).biUnion A)).card : ℝ) ≤
      r * collisionCount U S A s := by
  classical
  have hsubset : U \ (untouched U S A s ∪ (isolated S A s).biUnion A) ⊆
      (colliding S A s).biUnion A := by
    intro v hv
    obtain ⟨hvU, hvnot⟩ := Finset.mem_sdiff.mp hv
    have hnot : ¬ ∀ e ∈ incident S A v, s e = false := by
      intro hh
      exact hvnot (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hvU, hh⟩))
    push Not at hnot
    obtain ⟨e, he, hse⟩ := hnot
    have hse' : s e = true := by cases hs : s e <;> simp_all
    have heS := (mem_incident S A v e |>.mp he).1
    have hve := (mem_incident S A v e |>.mp he).2
    have hnotiso : e ∉ isolated S A s := by
      intro hh
      exact hvnot (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, hh, hve⟩))
    have hcounter : ¬ ∀ f ∈ S, f ≠ e → s f = true → Disjoint (A e) (A f) := by
      intro hh
      exact hnotiso (Finset.mem_filter.mpr ⟨heS, hse', hh⟩)
    push Not at hcounter
    exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_filter.mpr ⟨heS, hse', hcounter⟩, hve⟩
  calc
    _ ≤ (((colliding S A s).biUnion A).card : ℝ) := by exact_mod_cast Finset.card_le_card hsubset
    _ ≤ (colliding S A s).card * (r : ℝ) := card_biUnion_upper _ _ fun e he ↦
      Nat.cast_le.mpr (hr e (Finset.mem_filter.mp he).1)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (colliding_card_le U S A hsub s) (Nat.cast_nonneg r)
      simpa only [mul_comm] using hh

lemma nibble_budget_inequalities {n r D C a K : ℝ}
    (hn : 0 < n) (_hr : 0 ≤ r) (hD : 0 < D) (_hC : 0 ≤ C)
    (ha : 0 < a) (hK : 0 ≤ K) (hcode : n*C ≤ K*D)
    (hsize : 512*r ≤ a*n) (hmany : 16*r^2*(K+1)^2 ≤ a^5*n) :
    4*n*(4*a*r^2*D*C) ≤ (a^2*D)^2 * (a^2*n/(K+1)) ∧
    4*(2*a*n*r) ≤ (a*n/8)^2 := by
  have hK1 : 0 < K+1 := by linarith
  have hh : 16*r^2*K*(K+1) ≤ a^5*n := by
    calc
      _ ≤ 16*r^2*(K+1)*(K+1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith : K ≤ K+1)
          (by positivity : 0 ≤ 16*r^2)) hK1.le
      _ = 16*r^2*(K+1)^2 := by ring
      _ ≤ _ := hmany
  have hdiv : 16*r^2*K ≤ a^5*n/(K+1) := (le_div_iff₀ hK1).mpr hh
  constructor
  · calc
      _ = (16*a*r^2*D)*(n*C) := by ring
      _ ≤ (16*a*r^2*D)*(K*D) := mul_le_mul_of_nonneg_left hcode (by positivity)
      _ = (a*D^2)*(16*r^2*K) := by ring
      _ ≤ (a*D^2)*(a^5*n/(K+1)) := mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = _ := by ring
  · have hh := mul_le_mul_of_nonneg_left hsize (show 0 ≤ a*n by positivity)
    nlinarith only [hh]

lemma nibble_bad_loss {n D C a K : ℝ} (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hcode : n*C ≤ K*D) :
    (a^2*n/(K+1))*C ≤ a^2*D := by
  have hK1 : 0 < K+1 := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hK1]
  have hh := mul_le_mul_of_nonneg_left hcode (sq_nonneg a)
  nlinarith only [hh, mul_nonneg (sq_nonneg a) hD]

omit [Fintype E] [DecidableEq E] in
lemma incident_restrict_subset (S : Finset E) (A : E → Finset V) (W : Finset V) (v : V) :
    incident (restrictEdges S A W) A v ⊆ incident S A v := by
  rw [incident_restrict]
  exact Finset.filter_subset _ _

lemma one_round (U : Finset V) (S : Finset E) (A : E → Finset V)
    {r : ℕ} (hr0 : 1 ≤ r) {D ε C a K : ℝ}
    (hD : 1 ≤ D) (he : 0 ≤ ε) (hequarter : ε ≤ D/4) (hC : 0 ≤ C)
    (ha : 0 < a) (ha16 : a ≤ 1/16) (hra : (r : ℝ)*a ≤ 1/4)
    (hK : 0 ≤ K) (hcode : U.card*C ≤ K*D) (hCa : C ≤ a*D)
    (hsize : 512*(r : ℝ) ≤ a*U.card)
    (hmany : 16*(r : ℝ)^2*(K+1)^2 ≤ a^5*U.card)
    (hsub : ∀ e ∈ S, A e ⊆ U) (hr : ∀ e ∈ S, (A e).card = r)
    (hdeg : ∀ v ∈ U, |((incident S A v).card : ℝ) - D| ≤ ε)
    (hcodeg : ∀ v ∈ U, ∀ w ∈ U, v ≠ w →
      ((incident S A v ∩ incident S A w).card : ℝ) ≤ C) :
    ∃ W : Finset V, ∃ T M : Finset E,
      W ⊆ U ∧ T ⊆ S ∧ (∀ e ∈ T, A e ⊆ W) ∧ M ⊆ S ∧
      (M : Set E).Pairwise (fun e f ↦ Disjoint (A e) (A f)) ∧
      Disjoint W (M.biUnion A) ∧
      ((W.card : ℝ) ≤ (1-a/2)*U.card) ∧
      (((U \ (W ∪ M.biUnion A)).card : ℝ) ≤ (16*(r : ℝ)+1)*a^2*U.card) ∧
      ∀ v ∈ W, |((incident T A v).card : ℝ) - (1-((r-1 : ℕ) : ℝ)*a)*D| ≤
        (1+2*(r : ℝ)*a)*ε + 8*(r : ℝ)^2*a^2*D := by
  classical
  let n : ℝ := U.card
  let p : ℝ := a/D
  let Y : V → (E → Bool) → ℝ := fun v s ↦
    ∑ e ∈ incident S A v, noHit (hits S A ((A e).erase v)) s
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr0
  have hD0 : 0 < D := by linarith
  have heD : ε ≤ D := by linarith
  have hn : 0 < n := by dsimp [n]; nlinarith only [hsize, hr1, ha]
  have hn0 : 0 ≤ n := hn.le
  have hp : 0 ≤ p := div_nonneg ha.le hD0.le
  have hp1 : p ≤ 1 := (div_le_one hD0).mpr (by linarith)
  have hpa : p*D = a := div_mul_cancel₀ a hD0.ne'
  have hK1 : 0 < K+1 := by linarith
  have hmax : ∀ v ∈ U, ((incident S A v).card : ℝ) ≤ D+ε := by
    intro v hv
    have := (abs_le.mp (hdeg v hv)).2
    linarith
  have hmult : p*(D+ε) ≤ 2*a := by
    have hh := mul_le_mul_of_nonneg_left heD hp
    nlinarith only [hh, hpa]
  have hmul0 : 0 ≤ p*(D+ε) := by positivity
  have hsq : (p*(D+ε))^2 ≤ 4*a^2 := by
    have hh := (sq_le_sq₀ hmul0 (by positivity : 0 ≤ 2*a)).mpr hmult
    nlinarith only [hh]
  have hY : ∀ v ∈ U, expectation p (fun s ↦ (Y v s - expectation p (Y v))^2) ≤
      4*a*(r : ℝ)^2*D*C := by
    intro v hv
    have hh := residual_degree_variance U S A (by linarith : 0 ≤ D+ε) hC hp hp1 hsub
      (fun e he ↦ (hr e he).le) hmax hcodeg v hv
    apply hh.trans
    have hsq' : (D+ε)^2 ≤ (2*D)^2 := (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
    calc
      _ = (p*(r : ℝ)^2*C)*(D+ε)^2 := by ring
      _ ≤ (p*(r : ℝ)^2*C)*(2*D)^2 := mul_le_mul_of_nonneg_left hsq' (by positivity)
      _ = _ := by linear_combination 4*(r : ℝ)^2*D*C*hpa
  have hZ : expectation p (fun s ↦ (((untouched U S A s).card : ℝ) -
      expectation p (fun s ↦ ((untouched U S A s).card : ℝ)))^2) ≤ 2*a*n*r := by
    apply (untouched_variance U S A hp hp1 (fun e he ↦ (hr e he).le) hmax).trans
    calc
      _ ≤ p*n*(2*D)*r := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith : D+ε ≤ 2*D)
          (by positivity : 0 ≤ p*n)) (Nat.cast_nonneg r)
      _ = _ := by linear_combination 2*n*(r : ℝ)*hpa
  have hCollision : expectation p (collisionCount U S A) ≤ 4*a^2*n := by
    apply (collisionCount_mean U S A (by linarith : 0 ≤ D+ε) hmax).trans
    have hh := mul_le_mul_of_nonneg_left hsq hn0
    nlinarith only [hh]
  have hbudgets := nibble_budget_inequalities hn (Nat.cast_nonneg r) hD0 hC ha hK hcode hsize hmany
  obtain ⟨s, hsB, hsZ, hsC⟩ := exists_controlled_outcome hp hp1 U Y
    (fun s ↦ ((untouched U S A s).card : ℝ)) (collisionCount U S A)
    (t := a^2*D) (b := a^2*n/(K+1)) (u := a*n/8) (c := 16*a^2*n)
    (by positivity) (by positivity) (by positivity) (by positivity)
    hY hZ (collisionCount_nonneg U S A) hCollision hbudgets.1 hbudgets.2 (by ring_nf; rfl)
  let B : Finset V := U.filter fun v ↦ a^2*D < |Y v s - expectation p (Y v)|
  let U₀ := untouched U S A s
  let W := U₀ \ B
  let S₀ := restrictEdges S A U₀
  let T := restrictEdges S₀ A W
  let M := isolated S A s
  have hU₀ : U₀ ⊆ U := Finset.filter_subset _ _
  have hW₀ : W ⊆ U₀ := Finset.sdiff_subset
  have hS₀ : S₀ ⊆ S := Finset.filter_subset _ _
  have hT₀ : T ⊆ S₀ := Finset.filter_subset _ _
  have hsub₀ : ∀ e ∈ S₀, A e ⊆ U₀ := fun e he ↦ (Finset.mem_filter.mp he).2
  have hTW : ∀ e ∈ T, A e ⊆ W := fun e he ↦ (Finset.mem_filter.mp he).2
  have hMS : M ⊆ S := Finset.filter_subset _ _
  have hBcard : (B.card : ℝ) ≤ a^2*n/(K+1) := hsB
  have hbmax : a^2*n/(K+1) ≤ a^2*n := by
    rw [div_le_iff₀ hK1]
    nlinarith only [mul_nonneg (show 0 ≤ a^2*n by positivity) hK]
  have hmeanZ : expectation p (fun s ↦ ((untouched U S A s).card : ℝ)) ≤ n*(1-5*a/8) := by
    apply (untouched_mean_upper U S A hp hp1 (by linarith : 0 ≤ D+ε) (D := D-ε) ?_).trans
    · apply mul_le_mul_of_nonneg_left _ hn0
      have hpe : p*ε ≤ a/4 := by
        have hh := mul_le_mul_of_nonneg_left hequarter hp
        nlinarith only [hh, hpa]
      have haa := mul_nonneg ha.le (sub_nonneg.mpr ha16)
      nlinarith only [hpe, hpa, hsq, haa]
    · intro v hv
      have hb := abs_le.mp (hdeg v hv)
      constructor <;> linarith
  have hUcard : (U₀.card : ℝ) ≤ (1-a/2)*n := by
    have hh := (abs_le.mp hsZ).2
    dsimp [U₀]
    linarith
  have hwaste0 : ((U \ (U₀ ∪ M.biUnion A)).card : ℝ) ≤ r*collisionCount U S A s :=
    wasted_vertices_le U S A hsub (fun e he ↦ (hr e he).le) s
  have hwaste : ((U \ (W ∪ M.biUnion A)).card : ℝ) ≤ (16*(r : ℝ)+1)*a^2*n := by
    have hset : U \ (W ∪ M.biUnion A) ⊆ (U \ (U₀ ∪ M.biUnion A)) ∪ B := by
      intro v hv
      simp only [W, Finset.mem_sdiff, Finset.mem_union] at *
      tauto
    have hcard : ((U \ (W ∪ M.biUnion A)).card : ℝ) ≤
        (U \ (U₀ ∪ M.biUnion A)).card + B.card := by
      exact_mod_cast (Finset.card_le_card hset).trans (Finset.card_union_le _ _)
    have hc := mul_le_mul_of_nonneg_left hsC (Nat.cast_nonneg r)
    nlinarith only [hcard, hwaste0, hBcard, hbmax, hc]
  refine ⟨W, T, M, hW₀.trans hU₀, hT₀.trans hS₀, hTW, hMS,
    isolated_pairwise S A s,
    (isolated_untouched_disjoint U S A s).symm.mono_left hW₀,
    (Nat.cast_le.mpr (Finset.card_le_card hW₀)).trans hUcard, hwaste, ?_⟩
  intro v hv
  obtain ⟨hv₀, hvB⟩ := Finset.mem_sdiff.mp hv
  have hvU := hU₀ hv₀
  have htest : |Y v s - expectation p (Y v)| ≤ a^2*D := by
    apply le_of_not_gt
    intro hh
    exact hvB (Finset.mem_filter.mpr ⟨hvU, hh⟩)
  have hmeanY := residual_mean_estimate U S A hr0 hD0 he heD hC hCa hp hp1 ha.le hpa
    (by linarith : (r : ℝ)*a ≤ 1) hsub hr hdeg hcodeg v hvU
  have hdegeq : ((incident S₀ A v).card : ℝ) = Y v s :=
    residual_degree_eq U S A hsub s v hv₀
  have hdegree0 : |((incident S₀ A v).card : ℝ) - (1-((r-1 : ℕ) : ℝ)*a)*D| ≤
      (1+2*(r : ℝ)*a)*ε + 6*(r : ℝ)^2*a^2*D + a^2*D := by
    rw [hdegeq]
    exact (abs_sub_le (Y v s) (expectation p (Y v)) _).trans (by linarith)
  have hc₀ : ∀ w ∈ B, v ≠ w → ((incident S₀ A v ∩ incident S₀ A w).card : ℝ) ≤ C := by
    intro w hw hvw
    apply (Nat.cast_le.mpr (Finset.card_le_card (Finset.inter_subset_inter
      (incident_restrict_subset S A U₀ v) (incident_restrict_subset S A U₀ w)))).trans
    exact hcodeg v hvU w (Finset.mem_filter.mp hw).1 hvw
  have hloss := degree_loss_deleting U₀ B S₀ A hC hsub₀ v hc₀ hvB
  change ((incident S₀ A v).card : ℝ) - B.card*C ≤ ((incident T A v).card : ℝ) at hloss
  have hBCloss : B.card*C ≤ a^2*D :=
    (mul_le_mul_of_nonneg_right hBcard hC).trans (nibble_bad_loss hD0.le hK hcode)
  have hupper : ((incident T A v).card : ℝ) ≤ (incident S₀ A v).card :=
    Nat.cast_le.mpr (Finset.card_le_card (incident_restrict_subset S₀ A W v))
  have hrerr : 2*a^2*D ≤ 2*(r : ℝ)^2*a^2*D := by
    have hh : (2 : ℝ) ≤ 2*(r : ℝ)^2 := by nlinarith only [hr1]
    have hh' := mul_le_mul_of_nonneg_right hh (show 0 ≤ a^2*D by positivity)
    nlinarith only [hh']
  apply abs_le.mpr
  have hlow0 := (abs_le.mp hdegree0).1
  have hupp0 := (abs_le.mp hdegree0).2
  constructor <;> nlinarith only [hloss, hBCloss, hupper, hrerr, hlow0, hupp0]

namespace PackingState

end PackingState

open Filter Topology

end Hypergraph

end Nibble
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Nibble
open scoped BigOperators
open Finset


theorem solution.{uE,uV} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Nibble.one_round.{uE,uV} := @_root_.OAI.AsymptoticallyMinimalLittlewood.Nibble.one_round.{uE,uV}
