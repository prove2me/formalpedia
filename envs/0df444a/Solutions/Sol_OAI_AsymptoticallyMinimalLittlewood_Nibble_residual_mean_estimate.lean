-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Nibble.residual_mean_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:48:10.290726+00:00
-- url     : https://prove2.me/submissions/4f090dac-90ad-4a98-9040-c6f165886321

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Nibble.lean:L475-L532
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Nibble.residual_mean_estimate. The node keeps its source
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
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Nibble_noHit_mean_error

-- ---- from OAI.Analysis.Littlewood.Nibble ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

lemma card_biUnion_lower (S : Finset I) (A : I → Finset E) {C : ℝ} (hC : 0 ≤ C)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ((A i ∩ A j).card : ℝ) ≤ C) :
    (∑ i ∈ S, ((A i).card : ℝ)) ≤ ((S.biUnion A).card : ℝ) + (S.card : ℝ) ^ 2 * C := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hiS : ∀ j ∈ S, ((A i ∩ A j).card : ℝ) ≤ C := fun j hj ↦
      hpair i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (by intro h; subst j; contradiction)
    have hh := card_biUnion_upper S (fun j ↦ A i ∩ A j) hiS
    rw [← Finset.inter_biUnion] at hh
    have hcard := Finset.card_union_add_card_inter (A i) (S.biUnion A)
    have hcard' : ((A i ∪ S.biUnion A).card : ℝ) + (A i ∩ S.biUnion A).card =
        (A i).card + (S.biUnion A).card := by exact_mod_cast hcard
    have hind := ih (fun j hj k hk hjk ↦
      hpair j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk)
    rw [Finset.sum_insert hi, Finset.biUnion_insert, Finset.card_insert_of_notMem hi]
    push_cast
    nlinarith [show (0 : ℝ) ≤ S.card from Nat.cast_nonneg _]

end SetUnions

section Hypergraph
variable {V : Type uV} {E : Type uE} [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype E] in
lemma hits_card_upper (S : Finset E) (A : E → Finset V) (W : Finset V) {D : ℝ}
    (hD : ∀ v ∈ W, ((incident S A v).card : ℝ) ≤ D) :
    ((hits S A W).card : ℝ) ≤ W.card * D := card_biUnion_upper W _ hD

omit [Fintype E] in
lemma hits_card_deviation (S : Finset E) (A : E → Finset V) (W : Finset V)
    {D e C : ℝ} (hC : 0 ≤ C)
    (hD : ∀ v ∈ W, |((incident S A v).card : ℝ) - D| ≤ e)
    (hpair : ∀ v ∈ W, ∀ w ∈ W, v ≠ w →
      ((incident S A v ∩ incident S A w).card : ℝ) ≤ C) :
    |((hits S A W).card : ℝ) - W.card * D| ≤ W.card * e + (W.card : ℝ) ^ 2 * C := by
  have hupper := hits_card_upper S A W (D := D + e) (fun v hv ↦ by
    have := (abs_le.mp (hD v hv)).2
    linarith)
  have hlower := card_biUnion_lower W (incident S A) hC hpair
  have hsum : W.card * (D - e) ≤ ∑ v ∈ W, ((incident S A v).card : ℝ) := by
    calc
      _ = ∑ _v ∈ W, (D - e) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun v hv ↦ by have := (abs_le.mp (hD v hv)).1; linarith
  change (∑ v ∈ W, ((incident S A v).card : ℝ)) ≤
    ((hits S A W).card : ℝ) + (W.card : ℝ)^2 * C at hlower
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg (sq_nonneg (W.card : ℝ)) hC]

lemma residual_degree_mean (U : Finset V) (S : Finset E) (A : E → Finset V)
    {r : ℕ} (hr0 : 1 ≤ r) {D ε C p : ℝ} (hD : 0 ≤ D) (he : 0 ≤ ε) (hC : 0 ≤ C)
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hsub : ∀ e ∈ S, A e ⊆ U) (hr : ∀ e ∈ S, (A e).card = r)
    (hdeg : ∀ v ∈ U, |((incident S A v).card : ℝ) - D| ≤ ε)
    (hcodeg : ∀ v ∈ U, ∀ w ∈ U, v ≠ w →
      ((incident S A v ∩ incident S A w).card : ℝ) ≤ C)
    (v : V) (_hv : v ∈ U) :
    |expectation p (fun s ↦ ∑ e ∈ incident S A v, noHit (hits S A ((A e).erase v)) s) -
      (incident S A v).card * (1 - p * ((r-1 : ℕ) : ℝ) * D)| ≤
      (incident S A v).card * (p * ((r : ℝ)*ε + (r : ℝ)^2*C) +
        (p * ((r : ℝ)*(D+ε)))^2/2) := by
  have htcard (e : E) (heS : e ∈ incident S A v) : ((A e).erase v).card = r-1 := by
    rw [Finset.card_erase_of_mem (mem_incident S A v e |>.mp heS).2, hr e
      (mem_incident S A v e |>.mp heS).1]
  have hrle : ((r-1 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.sub_le r 1
  have hcard : ∀ e ∈ incident S A v,
      |((hits S A ((A e).erase v)).card : ℝ) - ((r-1 : ℕ) : ℝ)*D| ≤
        (r : ℝ)*ε + (r : ℝ)^2*C := by
    intro e heS
    have hsube : ∀ w ∈ (A e).erase v, w ∈ U := fun w hw ↦
      hsub e (mem_incident S A v e |>.mp heS).1 (Finset.mem_of_mem_erase hw)
    have hb := hits_card_deviation S A ((A e).erase v) hC
      (fun w hw ↦ hdeg w (hsube w hw))
      (fun w hw z hz hwz ↦ hcodeg w (hsube w hw) z (hsube z hz) hwz)
    rw [htcard e heS] at hb
    apply hb.trans
    exact add_le_add (mul_le_mul_of_nonneg_right hrle he)
      (mul_le_mul_of_nonneg_right ((sq_le_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr hrle) hC)
  have hupper : ∀ e ∈ incident S A v,
      ((hits S A ((A e).erase v)).card : ℝ) ≤ (r : ℝ)*(D+ε) := by
    intro e heS
    apply (hits_card_upper S A ((A e).erase v) (D := D+ε) ?_).trans
    · rw [htcard e heS]
      exact mul_le_mul_of_nonneg_right hrle (add_nonneg hD he)
    · intro w hw
      have hh := (abs_le.mp (hdeg w (hsub e (mem_incident S A v e |>.mp heS).1
        (Finset.mem_of_mem_erase hw)))).2
      linarith
  simpa only [mul_assoc] using noHit_mean_error hp hp1
    (by positivity : 0 ≤ (r : ℝ)*(D+ε)) (incident S A v)
    (fun e ↦ hits S A ((A e).erase v)) hcard hupper

lemma residual_mean_estimate (U : Finset V) (S : Finset E) (A : E → Finset V)
    {r : ℕ} (hr0 : 1 ≤ r) {D ε C p a : ℝ}
    (hD : 0 < D) (he : 0 ≤ ε) (heD : ε ≤ D) (hC : 0 ≤ C) (hCa : C ≤ a*D)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (ha : 0 ≤ a) (hpa : p*D = a)
    (hra : (r : ℝ)*a ≤ 1)
    (hsub : ∀ e ∈ S, A e ⊆ U) (hr : ∀ e ∈ S, (A e).card = r)
    (hdeg : ∀ v ∈ U, |((incident S A v).card : ℝ) - D| ≤ ε)
    (hcodeg : ∀ v ∈ U, ∀ w ∈ U, v ≠ w →
      ((incident S A v ∩ incident S A w).card : ℝ) ≤ C)
    (v : V) (hv : v ∈ U) :
    |expectation p (fun s ↦ ∑ e ∈ incident S A v, noHit (hits S A ((A e).erase v)) s) -
      (1 - ((r-1 : ℕ) : ℝ)*a)*D| ≤ (1+2*(r : ℝ)*a)*ε + 6*(r : ℝ)^2*a^2*D := by
  let d : ℝ := (incident S A v).card
  let q : ℝ := 1 - ((r-1 : ℕ) : ℝ)*a
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hd : d ≤ 2*D := by have := (abs_le.mp (hdeg v hv)).2; dsimp [d]; linarith
  have hq1 : q ≤ 1 := by
    dsimp [q]
    linarith [mul_nonneg (Nat.cast_nonneg (r-1)) ha]
  have hq0 : 0 ≤ q := by
    have hrl : ((r-1 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.sub_le r 1
    have hh := mul_le_mul_of_nonneg_right hrl ha
    dsimp [q]
    linarith
  have hmean := residual_degree_mean U S A hr0 hD.le he hC hp hp1 hsub hr hdeg hcodeg v hv
  have hqeq : 1 - p*((r-1 : ℕ) : ℝ)*D = q := by dsimp [q]; nlinarith only [hpa]
  rw [hqeq] at hmean
  have hglobal : p * ((r : ℝ)*(D+ε)) ≤ 2*a*r := by
    calc
      _ ≤ p*((r : ℝ)*(2*D)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (by linarith : D+ε ≤ 2*D) (Nat.cast_nonneg _)) hp
      _ = _ := by nlinarith only [hpa]
  have hsq : (p*((r : ℝ)*(D+ε)))^2/2 ≤ 2*a^2*(r : ℝ)^2 := by
    have hh := (sq_le_sq₀ (show 0 ≤ p*((r : ℝ)*(D+ε)) by positivity)
      (show 0 ≤ 2*a*r by positivity)).mpr hglobal
    nlinarith only [hh]
  have hC' : p*(r : ℝ)^2*C ≤ a^2*(r : ℝ)^2 := by
    calc
      _ ≤ p*(r : ℝ)^2*(a*D) := mul_le_mul_of_nonneg_left hCa (by positivity)
      _ = _ := by linear_combination a * (r : ℝ)^2 * hpa
  have hinner : p*((r : ℝ)*ε+(r : ℝ)^2*C)+(p*((r : ℝ)*(D+ε)))^2/2 ≤
      p*(r : ℝ)*ε+3*a^2*(r : ℝ)^2 := by nlinarith only [hC', hsq]
  have hbound : d * (p*((r : ℝ)*ε+(r : ℝ)^2*C)+(p*((r : ℝ)*(D+ε)))^2/2) ≤
      2*(r : ℝ)*a*ε+6*(r : ℝ)^2*a^2*D := by
    calc
      _ ≤ d*(p*(r : ℝ)*ε+3*a^2*(r : ℝ)^2) := mul_le_mul_of_nonneg_left hinner hd0
      _ ≤ (2*D)*(p*(r : ℝ)*ε+3*a^2*(r : ℝ)^2) := mul_le_mul_of_nonneg_right hd (by positivity)
      _ = _ := by linear_combination 2 * (r : ℝ) * ε * hpa
  have hcenter : |d*q-q*D| ≤ ε := by
    have hh : |d*q-q*D| = |d-D| * q := by
      rw [show d*q-q*D = (d-D)*q by ring, abs_mul, abs_of_nonneg hq0]
    rw [hh]
    exact (mul_le_mul_of_nonneg_left hq1 (abs_nonneg _)).trans (by simpa [d] using hdeg v hv)
  calc
    _ ≤ |expectation p (fun s ↦ ∑ e ∈ incident S A v, noHit (hits S A ((A e).erase v)) s) - d*q| +
        |d*q-q*D| := abs_sub_le _ _ _
    _ ≤ (2*(r : ℝ)*a*ε+6*(r : ℝ)^2*a^2*D)+ε := add_le_add (hmean.trans hbound) hcenter
    _ = _ := by ring

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


theorem solution.{uE,uV} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Nibble.residual_mean_estimate.{uE,uV} := @_root_.OAI.AsymptoticallyMinimalLittlewood.Nibble.residual_mean_estimate.{uE,uV}
