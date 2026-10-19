-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Nibble.nibble_parameters
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:53:31.240189+00:00
-- url     : https://prove2.me/submissions/bd94fdd1-ba61-4c64-b924-86754597fd27

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Nibble.lean:L923-L992
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Nibble.nibble_parameters. The node keeps its source
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

end SetUnions

section Hypergraph
variable {V : Type uV} {E : Type uE} [DecidableEq V] [Fintype E] [DecidableEq E]

namespace PackingState

end PackingState

open Filter Topology

/-- Fixed nibble parameters, chosen in the order required by packing:
first the tolerated residual, then finitely many rounds, then regularity. -/
lemma nibble_parameters (r : ℕ) {d : ℝ} (hd : 0 < d) :
    ∃ (a : ℝ) (k : ℕ) (e : ℝ), 0 < a ∧ a ≤ 1/16 ∧
      (r : ℝ)*a ≤ 1/4 ∧ 0 < e ∧
      0 < (1-((r-1 : ℕ) : ℝ)*a)^k ∧
      (1+2*(r : ℝ)*a)^k*(e+8*(r : ℝ)^2*a^2*k) ≤
        (1-((r-1 : ℕ) : ℝ)*a)^k/4 ∧
      (1-a/2)^k ≤ d ∧ k*(16*(r : ℝ)+1)*a^2 ≤ d := by
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hd
    (Real.exp_lt_one_iff.mpr (show (-1/2 : ℝ) < 0 by norm_num))
  let Q : ℝ := Real.exp (-((r-1 : ℕ) : ℝ))^M
  let G : ℝ := Real.exp (2*(r : ℝ))^M
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  let e : ℝ := Q/(16*G)
  have he : 0 < e := by dsimp [e]; positivity
  have ha0 : Tendsto (fun n : ℕ ↦ (1 : ℝ)/n) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop |>.congr (by simp)
  have ha2k : Tendsto (fun n : ℕ ↦ ((1 : ℝ)/n)^2*(n*M : ℕ)) atTop (𝓝 0) := by
    apply (show Tendsto (fun n : ℕ ↦ (1 : ℝ)/n * M) atTop (𝓝 0) by
      simpa using ha0.mul_const (M : ℝ)).congr' _
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    push_cast
    field_simp
  have hq : Tendsto (fun n : ℕ ↦ (1-((r-1 : ℕ) : ℝ)*(1/n))^(n*M))
      atTop (𝓝 Q) := by
    simpa only [pow_mul, div_eq_mul_inv, one_mul, sub_eq_add_neg, neg_mul]
      using (Real.tendsto_one_add_div_pow_exp (-((r-1 : ℕ) : ℝ))).pow M
  have hg : Tendsto (fun n : ℕ ↦ (1+2*(r : ℝ)*(1/n))^(n*M))
      atTop (𝓝 G) := by
    simpa only [pow_mul, div_eq_mul_inv, one_mul]
      using (Real.tendsto_one_add_div_pow_exp (2*(r : ℝ))).pow M
  have hb : Tendsto (fun n : ℕ ↦ (1-(1/(n : ℝ))/2)^(n*M))
      atTop (𝓝 (Real.exp (-1/2)^M)) := by
    convert (Real.tendsto_one_add_div_pow_exp (-1/2)).pow M using 1
    ext n
    rw [pow_mul]
    congr 2
    ring
  have herr : Tendsto (fun n : ℕ ↦
      (1+2*(r : ℝ)*(1/n))^(n*M)*(e+8*(r : ℝ)^2*(1/n)^2*(n*M : ℕ)))
      atTop (𝓝 (G*e)) := by
    have ht : Tendsto (fun n : ℕ ↦ e+8*(r : ℝ)^2*((1/(n : ℝ))^2*(n*M : ℕ)))
        atTop (𝓝 e) := by
      simpa using tendsto_const_nhds.add (ha2k.const_mul (8*(r : ℝ)^2))
    simpa only [mul_assoc] using hg.mul ht
  have hw : Tendsto (fun n : ℕ ↦ (n*M : ℕ)*(16*(r : ℝ)+1)*(1/(n : ℝ))^2)
      atTop (𝓝 0) := by
    convert ha2k.const_mul (16*(r : ℝ)+1) using 1 <;> (try {ext n; ring_nf})
  have hgap : G*e < Q/4 := by dsimp [e]; field_simp; nlinarith
  have hparams : ∀ᶠ n : ℕ in atTop,
      0 < (1 : ℝ)/n ∧ (1 : ℝ)/n ≤ 1/16 ∧
      (r : ℝ)*(1/n) ≤ 1/4 ∧
      0 < (1-((r-1 : ℕ) : ℝ)*(1/n))^(n*M) ∧
      (1+2*(r : ℝ)*(1/n))^(n*M)*(e+8*(r : ℝ)^2*(1/n)^2*(n*M : ℕ)) ≤
        (1-((r-1 : ℕ) : ℝ)*(1/n))^(n*M)/4 ∧
      (1-(1/(n : ℝ))/2)^(n*M) ≤ d ∧
      (n*M : ℕ)*(16*(r : ℝ)+1)*(1/(n : ℝ))^2 ≤ d := by
    filter_upwards [eventually_ge_atTop 1, ha0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/16)),
      (ha0.const_mul (r : ℝ)).eventually (gt_mem_nhds (by norm_num : (r : ℝ)*0 < 1/4)),
      hq.eventually (lt_mem_nhds hQ),
      herr.eventually_lt (hq.div_const 4) hgap,
      hb.eventually (gt_mem_nhds hM), hw.eventually (gt_mem_nhds hd)] with n hn ha hr hq' he1 hb' hw'
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    refine ⟨by positivity, ha.le, hr.le, hq', ?_, hb'.le, hw'.le⟩
    exact he1.le
  obtain ⟨n, hn⟩ := hparams.exists
  exact ⟨1/(n : ℝ), n*M, e, hn.1, hn.2.1, hn.2.2.1, he, hn.2.2.2⟩

end Hypergraph

end Nibble
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Nibble
open scoped BigOperators
open Finset
open Filter Topology


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Nibble.nibble_parameters := @_root_.OAI.AsymptoticallyMinimalLittlewood.Nibble.nibble_parameters
