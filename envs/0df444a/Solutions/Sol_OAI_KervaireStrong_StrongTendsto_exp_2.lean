-- Prove2me | solution 2 for OAI.KervaireStrong.StrongTendsto.exp
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:32:35.083087+00:00
-- url     : https://prove2.me/submissions/77ca7cc6-89dc-407f-b85c-aab90850da29

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/StrongLimits.lean:L47-L75
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireStrong.StrongTendsto.exp. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits

-- ---- from OAI.GroupTheory.Kervaire.StrongLimits ----
namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace KervaireStrong
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {ι : Type*} {l : Filter ι}
/-- Joint continuity of evaluation for strong convergence on an operator-norm
bounded family. -/
theorem StrongTendsto.apply_variable {T : ι → Operator H} {S : Operator H}
    (h : StrongTendsto T l S) {C : ℝ} (_hC : 0 ≤ C) (hb : ∀ i, ‖T i‖ ≤ C)
    {x : ι → H} {ξ : H} (hx : Tendsto x l (𝓝 ξ)) :
    Tendsto (fun i => T i (x i)) l (𝓝 (S ξ)) := by
  have hzero : Tendsto (fun i => T i (x i - ξ)) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun i => (T i).le_of_opNorm_le (hb i) _)
    have hx' : Tendsto (fun i => ‖x i - ξ‖) l (𝓝 0) := by
      simpa using (hx.sub (tendsto_const_nhds (x := ξ))).norm
    simpa using hx'.const_mul C
  have hs := hzero.add (h ξ)
  simpa only [map_sub, sub_add_cancel, zero_add] using hs

theorem StrongTendsto.mul {T T' : ι → Operator H} {S S' : Operator H}
    (h : StrongTendsto T l S) (h' : StrongTendsto T' l S')
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ i, ‖T i‖ ≤ C) :
    StrongTendsto (fun i => T i * T' i) l (S * S') := by
  intro ξ
  exact h.apply_variable hC hb (h' ξ)

theorem StrongTendsto.pow {T : ι → Operator H} {S : Operator H}
    (h : StrongTendsto T l S) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ i, ‖T i‖ ≤ C)
    (n : ℕ) : StrongTendsto (fun i => T i ^ n) l (S ^ n) := by
  induction n with
  | zero => intro ξ; simp only [pow_zero]; exact tendsto_const_nhds
  | succ n ih => simpa only [pow_succ'] using h.mul ih hC hb

/-- Exponentiation is strongly continuous on uniformly bounded families. -/
theorem StrongTendsto.exp [CompleteSpace H] {T : ι → Operator H} {S : Operator H}
    (h : StrongTendsto T l S) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ i, ‖T i‖ ≤ C) :
    StrongTendsto (fun i => NormedSpace.exp (T i)) l (NormedSpace.exp S) := by
  intro ξ
  let a : ℕ → ℝ := fun n => (n.factorial : ℝ)⁻¹
  have hs (R : Operator H) : HasSum (fun n => a n • ((R ^ n) ξ))
      (NormedSpace.exp R ξ) := by
    simpa [a] using
      ((ContinuousLinearMap.apply ℂ H ξ).restrictScalars ℝ).hasSum
        (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) R)
  have ht := tendsto_tsum_of_dominated_convergence
    ((NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) C).mul_right ‖ξ‖)
    (fun n => (h.pow hC hb n ξ).const_smul (a n)) ?_
  · simpa only [(hs _).tsum_eq] using ht
  · filter_upwards [] with i n
    calc
      ‖a n • ((T i ^ n) ξ)‖ = ‖a n‖ * ‖(T i ^ n) ξ‖ := norm_smul _ _
      _ ≤ ‖a n‖ * (C ^ n * ‖ξ‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ', mul_apply_eq_comp]
          exact ((T i).le_of_opNorm_le (hb i) _).trans
            ((mul_le_mul_of_nonneg_left ih hC).trans_eq (by rw [pow_succ']; ring))
      _ = ‖(n.factorial : ℝ)⁻¹ • C ^ n‖ * ‖ξ‖ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hC n)]
        exact (mul_assoc _ _ _).symm

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
open scoped ComplexOrder

end KervaireStrong

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireStrong
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.KervaireStrong.StrongTendsto.exp := @_root_.OAI.KervaireStrong.StrongTendsto.exp
