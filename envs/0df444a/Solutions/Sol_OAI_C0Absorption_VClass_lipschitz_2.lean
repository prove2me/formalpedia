-- Prove2me | solution 2 for OAI.C0Absorption.VClass_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:06:06.153999+00:00
-- url     : https://prove2.me/submissions/fb778715-64d5-400e-a363-f04c406ea2a7

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Tests.lean:L242-L255
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.VClass_lipschitz. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Theorems.Thm_OAI_C0Absorption_bounded_product_lipschitz
import Theorems.Thm_OAI_C0Absorption_localG_sup
import Theorems.Thm_OAI_C0Absorption_tailFactor_lipschitz

-- ---- from OAI.Analysis.C0Absorption.Localization ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

open Set Filter Topology

noncomputable section

theorem localR_sup {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ)
    (u : X → ℝ) (A : ℝ) (hu : ∀ x, |u x| ≤ A) (x : X) :
    |localR q ε u x| ≤ 2*A := by
  calc
    |localR q ε u x| = |localG q ε u x-u x| := rfl
    _ ≤ |localG q ε u x|+|u x| := abs_sub _ _
    _ ≤ A+A := add_le_add (localG_sup q ε u A hu x) (hu x)
    _ = 2*A := by ring

end

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Coordinates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace C0Absorption
noncomputable section

theorem tailFactor_nonneg (c : ℝ) (N : ℕ) (s : C0) : 0 ≤ tailFactor c N s := by
  exact le_min zero_le_one (le_max_right _ _)

theorem tailFactor_le_one (c : ℝ) (N : ℕ) (s : C0) : tailFactor c N s ≤ 1 := min_le_left _ _

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Tests ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace CylinderOperation
variable {I : Finset ℕ}
theorem act_sup (r : CylinderOperation I) {A : ℝ} (hA : 0 ≤ A)
    {u : Cube I → ℝ} (hu : ∀ x, |u x| ≤ A) : ∀ x, |r.act u x| ≤ 2*A := by
  intro x
  cases hr : r.isG <;> simp only [act, localOp, hr, Bool.false_eq_true, ↓reduceIte]
  · exact localR_sup r.point r.scale u A hu x
  · exact (localG_sup r.point r.scale u A hu x).trans (by linarith)

end CylinderOperation

theorem applyOperations_sup {I : Finset ℕ} (ops : List (CylinderOperation I))
    {A : ℝ} (hA : 0 ≤ A) {u : Cube I → ℝ} (hu : ∀ x, |u x| ≤ A) :
    ∀ x, |applyOperations ops u x| ≤ 2^ops.length*A := by
  induction ops generalizing A u with
  | nil => simpa using hu
  | cons r rs ih =>
    have hh := ih (by positivity : 0 ≤ 2*A) (r.act_sup hA hu)
    simpa only [applyOperations_cons, List.length_cons, pow_succ, mul_assoc] using hh

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

theorem cubeValue_sup (r : GeneratedRepresentation B γ) :
    ∀ x, |r.cubeValue x| ≤ (2 : ℝ)^r.operations.length*B.A :=
  applyOperations_sup _ B.A.coe_nonneg (B.base_sup γ)

theorem value_sup (r : GeneratedRepresentation B γ) :
    ∀ x, |r.value x| ≤ (2 : ℝ)^r.operations.length*B.A :=
  fun point => r.cubeValue_sup (cubeRestrict (B.coordinates γ) point)

end GeneratedRepresentation

namespace TailOperation

theorem factor_abs_le (t : TailOperation) (s : C0Ball) : |t.factor s| ≤ 1 := by
  have hl := tailFactor_nonneg (dyadic t.scaleIndex) (t.tailIndex+1) s.val
  have hu := tailFactor_le_one (dyadic t.scaleIndex) (t.tailIndex+1) s.val
  rw [abs_le]
  unfold factor
  split <;> constructor <;> linarith

theorem factor_lipschitz (t : TailOperation) : LipschitzWith (2^t.scaleIndex) t.factor := by
  apply LipschitzWith.of_dist_le_mul
  intro s u
  have hh := (tailFactor_lipschitz (dyadic_pos t.scaleIndex) (t.tailIndex+1)).dist_le_mul s.val u.val
  change dist (tailFactor (dyadic t.scaleIndex) (t.tailIndex+1) s.val)
      (tailFactor (dyadic t.scaleIndex) (t.tailIndex+1) u.val) ≤
      (dyadic t.scaleIndex)⁻¹ * dist s u at hh
  simp only [dyadic, inv_inv] at hh
  simp only [NNReal.coe_pow, NNReal.coe_ofNat]
  cases ht : t.isBasic
  · simpa only [factor, dyadic, ht, Bool.false_eq_true, ↓reduceIte, dist_sub_right] using hh
  · simpa only [factor, dyadic, ht, ↓reduceIte] using hh

end TailOperation

theorem tailProduct_abs_le (ts : List TailOperation) (s : C0Ball) : |tailProduct ts s| ≤ 1 := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [tailProduct_cons, abs_mul]
    exact (mul_le_mul (t.factor_abs_le s) ih (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem tailProduct_lipschitz (ts : List TailOperation) :
    LipschitzWith ((ts.map (fun t => (2 : ℝ≥0)^t.scaleIndex)).sum) (tailProduct ts) := by
  induction ts with
  | nil =>
    change LipschitzWith 0 (fun _ : C0Ball => (1 : ℝ))
    exact LipschitzWith.const 1
  | cons t ts ih =>
    have hh := bounded_product_lipschitz (A := 1) (B := 1) t.factor_lipschitz ih t.factor_abs_le (tailProduct_abs_le ts)
    convert hh using 1 <;> first | rfl | simp only [List.map_cons, List.sum_cons, one_mul, add_comm]

theorem tailProduct_lipschitz_bound (ts : List TailOperation) (h : ℕ)
    (hlen : ts.length ≤ h) (hscale : ∀ t ∈ ts, t.scaleIndex ≤ h) :
    LipschitzWith ((h : ℝ≥0)*2^h) (tailProduct ts) := by
  apply (tailProduct_lipschitz ts).weaken
  calc
    (ts.map (fun t => (2 : ℝ≥0)^t.scaleIndex)).sum ≤
        (ts.map (fun _ => (2 : ℝ≥0)^h)).sum := List.sum_le_sum
          (fun t ht => pow_le_pow_right₀ (by norm_num) (hscale t ht))
    _ = (ts.length : ℝ≥0)*2^h := by simp
    _ ≤ (h : ℝ≥0)*2^h := mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) (by positivity)

theorem TClass_sup {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) {f : C0Ball → ℝ}
    (hf : f ∈ TClass B h) : ∀ s, |f s| ≤ (2 : ℝ)^h*B.A := by
  obtain ⟨γ,r,hlen,rfl⟩ := hf
  intro s
  exact (r.value_sup s).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num) hlen) B.A.coe_nonneg)

theorem VClass_lipschitz {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) {f : C0Ball → ℝ}
    (hf : f ∈ VClass B h) : LipschitzWith (4^h*B.L0+h*4^h*B.A) f := by
  obtain ⟨γ,r,ts,hren,hband,hlen,hscale,rfl⟩ := hf
  have hu : LipschitzWith (4^h*B.L0) r.value := TClass_lipschitz B h ⟨γ,r,hren,rfl⟩
  have hb := tailProduct_lipschitz_bound ts h hlen hscale
  have hsup : ∀ s, |r.value s| ≤ ((2 : ℝ≥0)^h*B.A : ℝ≥0) := by
    intro s
    simpa only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat] using TClass_sup B h ⟨γ,r,hren,rfl⟩ s
  have hh := bounded_product_lipschitz (B := 1) hu hb hsup (tailProduct_abs_le ts)
  convert hh using 1 ; try rfl
  rw [one_mul]
  have hp : (4 : ℝ≥0)^h = 2^h*2^h := by rw [← mul_pow]; norm_num
  rw [hp]
  ring

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

end GeneratedRepresentation

end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty


theorem solution : type_of% @_root_.OAI.C0Absorption.VClass_lipschitz := @_root_.OAI.C0Absorption.VClass_lipschitz
