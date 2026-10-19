-- Prove2me | solution 1 for OAI.C0Absorption.VClass_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:28:12.809904+00:00
-- url     : https://prove2.me/submissions/2b3f5940-4dd3-477d-a34f-11f23df9ba0f

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

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
theorem h41_prod_lip {X : Type*} [PseudoMetricSpace X]
    {f g : X → ℝ} {K L A B : ℝ≥0} (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hfB : ∀ x, |f x| ≤ A) (hgB : ∀ x, |g x| ≤ B) :
    LipschitzWith (A*L+B*K) (fun x => f x*g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h1 := hf.dist_le_mul x y
  have h2 := hg.dist_le_mul x y
  rw [Real.dist_eq] at h1 h2 ⊢
  have e : f x * g x - f y * g y = f x * (g x - g y) + g y * (f x - f y) := by ring
  rw [e]
  have hA := hfB x
  have hB := hgB y
  have hd : 0 ≤ dist x y := dist_nonneg
  calc |f x * (g x - g y) + g y * (f x - f y)|
      ≤ |f x * (g x - g y)| + |g y * (f x - f y)| := abs_add_le _ _
    _ = |f x| * |g x - g y| + |g y| * |f x - f y| := by rw [abs_mul, abs_mul]
    _ ≤ (A:ℝ) * ((L:ℝ) * dist x y) + (B:ℝ) * ((K:ℝ) * dist x y) := by
        gcongr
    _ = ((A*L+B*K : ℝ≥0) : ℝ) * dist x y := by push_cast; ring

theorem h41_localOp_sup {X : Type*} [PseudoMetricSpace X] (isG : Bool) (q : X) (ε : ℝ)
    (u : X → ℝ) (M : ℝ) (hu : ∀ x, |u x| ≤ M) (x : X) : |localOp isG q ε u x| ≤ 2 * M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hu x)
  have hc0 : 0 ≤ chi (dist x q / ε) := le_min zero_le_one (le_max_left _ _)
  have hc1 : chi (dist x q / ε) ≤ 1 := min_le_left _ _
  have hG : |localG q ε u x| ≤ M := by
    unfold localG
    set c := chi (dist x q / ε)
    have e : u q + c * (u x - u q) = (1 - c) * u q + c * u x := by ring
    rw [e]
    have h1 := hu q
    have h2 := hu x
    calc |(1 - c) * u q + c * u x| ≤ |(1 - c) * u q| + |c * u x| := abs_add_le _ _
      _ = (1 - c) * |u q| + c * |u x| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - c), abs_of_nonneg hc0]
      _ ≤ (1 - c) * M + c * M := by gcongr
      _ = M := by ring
  cases isG
  · simp only [localOp, Bool.false_eq_true, ↓reduceIte, localRLinear_apply]
    unfold localR
    have h2 := hu x
    calc |localG q ε u x - u x| ≤ |localG q ε u x| + |u x| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  · simp only [localOp, ↓reduceIte]
    show |localG q ε u x| ≤ 2 * M
    linarith

theorem h41_applyOps_sup {I : Finset ℕ} (ops : List (CylinderOperation I)) (u : Cube I → ℝ) (M : ℝ)
    (hu : ∀ x, |u x| ≤ M) : ∀ x, |applyOperations ops u x| ≤ 2^ops.length * M := by
  induction ops generalizing u M with
  | nil => simpa using hu
  | cons r rs ih =>
    intro x
    rw [applyOperations_cons]
    have := ih (r.act u) (2*M) (fun y => h41_localOp_sup r.isG r.point r.scale u M hu y) x
    calc _ ≤ 2^rs.length*(2*M) := this
      _ = 2^(r::rs).length*M := by rw [List.length_cons, pow_succ]; ring

theorem h41_tailFactor_dist {c : ℝ} (hc : 0 < c) (N : ℕ) (s s' : C0) :
    |tailFactor c N s - tailFactor c N s'| ≤ dist s s' / c := by
  unfold tailFactor
  have h1 := abs_min_sub_min_le_max (1:ℝ) (max (2 - tau N s / c) 0) 1 (max (2 - tau N s' / c) 0)
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg (max (2 - tau N s / c) 0 - max (2 - tau N s' / c) 0))] at h1
  have h2 := abs_max_sub_max_le_abs (2 - tau N s / c) (2 - tau N s' / c) 0
  have h3 : |(2 - tau N s / c) - (2 - tau N s' / c)| = |tau N s - tau N s'| / c := by
    rw [show (2 - tau N s / c) - (2 - tau N s' / c) = (tau N s' - tau N s) / c by ring,
      abs_div, abs_of_pos hc, abs_sub_comm]
  have h4 := (tau_lipschitz N).dist_le_mul s s'
  rw [Real.dist_eq, NNReal.coe_one, one_mul] at h4
  have h5 : |tau N s - tau N s'| / c ≤ dist s s' / c := div_le_div_of_nonneg_right h4 hc.le
  linarith

theorem h41_factor_abs (t : TailOperation) (s : C0Ball) : |t.factor s| ≤ 1 := by
  unfold TailOperation.factor
  have a0 : ∀ c N (s : C0), 0 ≤ tailFactor c N s := fun c N s => le_min zero_le_one (le_max_right _ _)
  have a1 : ∀ c N (s : C0), tailFactor c N s ≤ 1 := fun c N s => min_le_left _ _
  split_ifs
  · have := a0 (dyadic t.scaleIndex) (t.tailIndex+1) s.val
    have := a1 (dyadic t.scaleIndex) (t.tailIndex+1) s.val
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have := a0 (dyadic t.scaleIndex) (t.tailIndex+1) s.val
    have := a1 (dyadic t.scaleIndex) (t.tailIndex+1) s.val
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem h41_factor_lip (t : TailOperation) : LipschitzWith ((2:ℝ≥0)^t.scaleIndex) t.factor := by
  apply LipschitzWith.of_dist_le_mul
  intro s s'
  have := h41_tailFactor_dist (dyadic_pos t.scaleIndex) (t.tailIndex+1) s.val s'.val
  have e : dist s.val s'.val / dyadic t.scaleIndex = ((2:ℝ≥0)^t.scaleIndex : ℝ≥0) * dist s s' := by
    rw [Subtype.dist_eq, dyadic, div_inv_eq_mul]; push_cast; ring
  rw [e] at this
  rw [Real.dist_eq]
  unfold TailOperation.factor
  split_ifs
  · exact this
  · rw [show tailFactor (dyadic t.scaleIndex) (t.tailIndex + 1) s.val - 1 -
        (tailFactor (dyadic t.scaleIndex) (t.tailIndex + 1) s'.val - 1) =
        tailFactor (dyadic t.scaleIndex) (t.tailIndex + 1) s.val -
        tailFactor (dyadic t.scaleIndex) (t.tailIndex + 1) s'.val by ring]
    exact this

theorem h41_tailProduct_abs (ts : List TailOperation) (s : C0Ball) : |tailProduct ts s| ≤ 1 := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [tailProduct_cons, abs_mul]
    exact mul_le_one₀ (h41_factor_abs t s) (abs_nonneg _) ih

theorem h41_tailProduct_lip (h : ℕ) (ts : List TailOperation) (hs : ∀ t ∈ ts, t.scaleIndex ≤ h) :
    LipschitzWith ((ts.length : ℝ≥0) * 2^h) (tailProduct ts) := by
  induction ts with
  | nil =>
    have e : tailProduct [] = fun _ => (1:ℝ) := funext tailProduct_nil
    rw [e]
    exact (LipschitzWith.const (1:ℝ)).weaken (by simp)
  | cons t ts ih =>
    have ht := (h41_factor_lip t).weaken (pow_le_pow_right₀ (by norm_num) (hs t List.mem_cons_self))
    have ih' := ih (fun t' ht' => hs t' (List.mem_cons_of_mem _ ht'))
    have hp := h41_prod_lip (A := 1) (B := 1) ht ih' (fun x => by simpa using h41_factor_abs t x)
      (fun x => by simpa using h41_tailProduct_abs ts x)
    have hf : tailProduct (t::ts) = fun x => t.factor x * tailProduct ts x :=
      funext (fun x => tailProduct_cons t ts x)
    rw [hf]
    refine hp.weaken (le_of_eq ?_)
    rw [List.length_cons]; push_cast; ring

theorem solution {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) {f : C0Ball → ℝ}
    (hf : f ∈ VClass B h) : LipschitzWith (4^h*B.L0+h*4^h*B.A) f := by
  obtain ⟨γ, r, ts, hl, hb, hts, hsc, rfl⟩ := hf
  have hv := r.value_lipschitz.weaken
    (show 4^r.operations.length*B.L0 ≤ 4^h*B.L0 from
      mul_le_mul_left (pow_le_pow_right₀ (by norm_num) hl) _)
  have hvb : ∀ s, |r.value s| ≤ (((2:ℝ≥0)^h*B.A : ℝ≥0) : ℝ) := by
    intro s
    have h1 := h41_applyOps_sup r.operations (B.base γ) B.A (B.base_sup γ)
      (cubeRestrict (B.coordinates γ) s)
    have h2 : (2:ℝ)^r.operations.length ≤ 2^h := pow_le_pow_right₀ (by norm_num) hl
    have h3 : (2:ℝ)^r.operations.length * B.A ≤ 2^h * B.A :=
      mul_le_mul_of_nonneg_right h2 B.A.coe_nonneg
    push_cast
    exact h1.trans h3
  have hT := h41_tailProduct_lip h ts hsc
  have hp := h41_prod_lip (B := 1) hv hT hvb (fun x => by simpa using h41_tailProduct_abs ts x)
  refine hp.weaken ?_
  have hlen : (ts.length : ℝ≥0) ≤ h := by exact_mod_cast hts
  have e4 : (4:ℝ≥0)^h = 2^h*2^h := by rw [← mul_pow]; norm_num
  calc (2:ℝ≥0)^h*B.A*((ts.length : ℝ≥0)*2^h) + 1*(4^h*B.L0)
      = 4^h*B.L0 + (ts.length : ℝ≥0)*4^h*B.A := by rw [e4]; ring
    _ ≤ 4^h*B.L0 + h*4^h*B.A := by gcongr

