-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Nibble.residual_degree_variance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:44:31.959425+00:00
-- url     : https://prove2.me/submissions/9eb5b3df-ed32-423c-be84-b679bd86aae9

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Nibble.lean:L101-L138
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Nibble.residual_degree_variance. The node keeps its source
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
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Nibble_noHit_sum_variance

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

end SetUnions

section Hypergraph
variable {V : Type uV} {E : Type uE} [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype E] in
lemma hits_card_upper (S : Finset E) (A : E → Finset V) (W : Finset V) {D : ℝ}
    (hD : ∀ v ∈ W, ((incident S A v).card : ℝ) ≤ D) :
    ((hits S A W).card : ℝ) ≤ W.card * D := card_biUnion_upper W _ hD

omit [Fintype E] in
lemma residual_test_frequency (S : Finset E) (A : E → Finset V) (v : V) (f : E) :
    ((incident S A v).filter fun e ↦ f ∈ hits S A ((A e).erase v)) =
      if f ∈ S then ((A f).erase v).biUnion (fun w ↦ incident S A v ∩ incident S A w) else ∅ := by
  ext e
  simp only [Finset.mem_filter, mem_incident, mem_hits, Finset.mem_erase,
    ]
  split_ifs <;> simp_all ; aesop

/-- Codegrees control the influence of each edge-bit on a residual degree. -/
lemma residual_degree_variance (U : Finset V) (S : Finset E) (A : E → Finset V)
    {r : ℕ} {D C p : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hsub : ∀ e ∈ S, A e ⊆ U) (hr : ∀ e ∈ S, (A e).card ≤ r)
    (hdeg : ∀ v ∈ U, ((incident S A v).card : ℝ) ≤ D)
    (hcodeg : ∀ v ∈ U, ∀ w ∈ U, v ≠ w →
      ((incident S A v ∩ incident S A w).card : ℝ) ≤ C)
    (v : V) (hv : v ∈ U) :
    let Y : (E → Bool) → ℝ := fun s ↦
      ∑ e ∈ incident S A v, noHit (hits S A ((A e).erase v)) s
    expectation p (fun s ↦ (Y s - expectation p Y)^2) ≤ p * (r : ℝ)^2 * D^2 * C := by
  classical
  let T := fun e ↦ hits S A ((A e).erase v)
  have hL : ∀ e ∈ incident S A v, ((T e).card : ℝ) ≤ r * D := by
    intro e he
    obtain ⟨heS, hve⟩ := mem_incident S A v e |>.mp he
    apply (hits_card_upper S A ((A e).erase v) (fun w hw ↦
      hdeg w (hsub e heS (Finset.mem_of_mem_erase hw)))).trans
    apply mul_le_mul_of_nonneg_right _ hD
    exact_mod_cast (Finset.card_erase_le.trans (hr e heS))
  have hK : ∀ f, (((incident S A v).filter fun e ↦ f ∈ T e).card : ℝ) ≤ r * C := by
    intro f
    dsimp [T]
    rw [residual_test_frequency]
    split_ifs with hf
    · apply (card_biUnion_upper ((A f).erase v) (fun w ↦ incident S A v ∩ incident S A w)
        (fun w hw ↦ hcodeg v hv w (hsub f hf (Finset.mem_of_mem_erase hw))
          (Ne.symm (Finset.mem_erase.mp hw).1))).trans
      apply mul_le_mul_of_nonneg_right _ hC
      exact_mod_cast (Finset.card_erase_le.trans (hr f hf))
    · simp only [Finset.card_empty, Nat.cast_zero]
      positivity
  have hb := noHit_sum_variance hp hp1 (incident S A v) T (by positivity : 0 ≤ (r : ℝ)*C) hL hK
  apply hb.trans
  have hd := hdeg v hv
  have hm := mul_le_mul_of_nonneg_right hd (show 0 ≤ p * (r : ℝ)^2 * D * C by positivity)
  nlinarith

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


theorem solution.{uE,uV} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Nibble.residual_degree_variance.{uE,uV} := @_root_.OAI.AsymptoticallyMinimalLittlewood.Nibble.residual_degree_variance.{uE,uV}
