-- Prove2me | solution 1 for OAI.C0Absorption.GeneratedRepresentation.exists_flatten
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:34:22.960825+00:00
-- url     : https://prove2.me/submissions/a9f669fb-275b-4ed4-9b0b-92eb13f2e97e

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
import Definitions.Def_OAI_Analysis_C0Absorption_Duality

open OAI OAI.C0Absorption OAI.C0Absorption.GeneratedRepresentation
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}
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


theorem h41_VClass_lip {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) {f : C0Ball → ℝ}
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

theorem h41_cp_lip {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S) (g : S → ℝ) (A : ℝ≥0)
    (hg : ∀ m : PreSpace L o, |pairing S g m| ≤ A * ‖m‖) (w w' : TestSpace L o) :
    |completedPairing L o g w - completedPairing L o g w'| ≤ A * ‖w - w'‖ := by
  refine UniformSpace.Completion.induction_on₂ (p := fun w w' : UniformSpace.Completion (PreSpace L o) =>
    |completedPairing L o g w - completedPairing L o g w'| ≤ A * ‖w - w'‖) w w' ?_ ?_
  · apply isClosed_le
    · exact ((UniformSpace.Completion.continuous_extension.comp continuous_fst).sub
        (UniformSpace.Completion.continuous_extension.comp continuous_snd)).abs
    · exact continuous_const.mul (continuous_fst.sub continuous_snd).norm
  · intro a b
    have h1 := completedPairing_coe L o g A hg a
    have h2 := completedPairing_coe L o g A hg b
    change |completedPairing L o g (toTestSpace L o a) - completedPairing L o g (toTestSpace L o b)| ≤
      A * ‖(a : UniformSpace.Completion (PreSpace L o)) - (b : UniformSpace.Completion (PreSpace L o))‖
    rw [h1, h2, ← UniformSpace.Completion.coe_sub, UniformSpace.Completion.norm_coe]
    have := (initialPairing_lipschitz L o g A hg).dist_le_mul a b
    rwa [Real.dist_eq, dist_eq_norm] at this

theorem h41_pairing_sub_le {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)
    (f g : S → ℝ) (m : PreSpace L o) (ε : ℝ) (hε : 0 ≤ ε) (hfg : ∀ s, |g s - f s| ≤ ε) :
    |pairing S g m - pairing S f m| ≤ ε * ∑ s ∈ (show Molecule S from m).val.support,
      |(show Molecule S from m).val s| := by
  show |Finsupp.linearCombination ℝ g (show Molecule S from m).val -
      Finsupp.linearCombination ℝ f (show Molecule S from m).val| ≤ _
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul, ← Finset.sum_sub_distrib,
    ← mul_sub, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun s _ => ?_))
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hfg s) (abs_nonneg _)

theorem h41_cp_approx {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S) (A : ℝ≥0)
    (f : S → ℝ) (hf : ∀ m : PreSpace L o, |pairing S f m| ≤ A * ‖m‖) (z : TestSpace L o)
    {δ : ℝ} (hδ : 0 < δ) : ∃ ε > 0, ∀ g : S → ℝ, (∀ m : PreSpace L o, |pairing S g m| ≤ A * ‖m‖) →
      (∀ s, |g s - f s| ≤ ε) → |completedPairing L o g z - completedPairing L o f z| < δ := by
  have hA : (0:ℝ) < A + 1 := by positivity
  set η := δ / (4 * (A + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨m, hm⟩ := (UniformSpace.Completion.denseRange_coe (α := PreSpace L o)).exists_dist_lt z hη0
  set Sm := ∑ s ∈ (show Molecule S from m).val.support, |(show Molecule S from m).val s| with hS
  have hS0 : 0 ≤ Sm := Finset.sum_nonneg (fun s _ => abs_nonneg _)
  refine ⟨δ / (4 * (Sm + 1)), by positivity, fun g hg hgf => ?_⟩
  have hzm : ‖z - (toTestSpace L o m)‖ < η := by
    rw [← dist_eq_norm]; exact hm
  have e1 := h41_cp_lip L o g A hg z (toTestSpace L o m)
  have e2 := h41_cp_lip L o f A hf z (toTestSpace L o m)
  have c1 := completedPairing_coe L o g A hg m
  have c2 := completedPairing_coe L o f A hf m
  rw [c1] at e1
  rw [c2] at e2
  have e3 : |pairing S g m - pairing S f m| ≤ δ / (4 * (Sm + 1)) * Sm := h41_pairing_sub_le L o f g m (δ / (4 * (Sm + 1))) (by positivity) hgf
  have hAη : (A:ℝ) * ‖z - (toTestSpace L o m)‖ ≤ (A + 1) * η :=
    mul_le_mul (by linarith) hzm.le (norm_nonneg _) hA.le
  have hAη' : (A + 1) * η = δ / 4 := by rw [hη]; field_simp
  have hS' : δ / (4 * (Sm + 1)) * Sm ≤ δ / 4 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have := abs_sub_le (completedPairing L o g z) (pairing S g m) (completedPairing L o f z)
  have := abs_sub_le (pairing S g m) (pairing S f m) (completedPairing L o f z)
  rw [abs_sub_comm (pairing S f m)] at this
  linarith

theorem h41_localG_sub {X : Type*} [PseudoMetricSpace X] (q : X) {ε : ℝ} (hε : 0 < ε)
    (u : X → ℝ) (K : ℝ≥0) (hu : LipschitzWith K u) (x : X) :
    |localG q ε u x - u x| ≤ K * ε := by
  unfold localG
  have e : u q + chi (dist x q / ε) * (u x - u q) - u x = (1 - chi (dist x q / ε)) * (u q - u x) := by ring
  rw [e]
  have hc0 : 0 ≤ chi (dist x q / ε) := le_min zero_le_one (le_max_left _ _)
  have hc1 : chi (dist x q / ε) ≤ 1 := min_le_left _ _
  have hK : (0:ℝ) ≤ K := K.coe_nonneg
  rcases lt_or_ge (dist x q) ε with hd | hd
  · have h1 := hu.dist_le_mul q x
    rw [Real.dist_eq, dist_comm] at h1
    rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - chi (dist x q / ε))]
    calc (1 - chi (dist x q / ε)) * |u q - u x| ≤ 1 * (K * ε) := by
          apply mul_le_mul (by linarith) (h1.trans (mul_le_mul_of_nonneg_left hd.le hK)) (abs_nonneg _)
            zero_le_one
      _ = K * ε := one_mul _
  · have ht : 1 ≤ dist x q / ε := by rw [le_div_iff₀ hε]; linarith
    have hc : chi (dist x q / ε) = 1 := by
      unfold chi
      rw [max_eq_right (by linarith), min_eq_left (by linarith)]
    rw [hc, sub_self, zero_mul, abs_zero]
    positivity

theorem h41_localG_flat {X : Type*} [PseudoMetricSpace X] (q : X) {ε : ℝ} (hε : 0 < ε)
    (u : X → ℝ) (x : X) (hd : dist x q < ε / 2) : localG q ε u x = u q := by
  unfold localG
  have ht : dist x q / ε < 1 / 2 := by rw [div_lt_iff₀ hε]; linarith
  have hc : chi (dist x q / ε) = 0 := by
    unfold chi
    rw [max_eq_left (by linarith), min_eq_right zero_le_one]
  rw [hc, zero_mul, add_zero]

theorem h41_localG_sup {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ)
    (u : X → ℝ) (M : ℝ) (hu : ∀ x, |u x| ≤ M) (x : X) : |localG q ε u x| ≤ M := by
  have hc0 : 0 ≤ chi (dist x q / ε) := le_min zero_le_one (le_max_left _ _)
  have hc1 : chi (dist x q / ε) ≤ 1 := min_le_left _ _
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

theorem h41_dyadic_anti {a b : ℕ} (hab : a ≤ b) : dyadic b ≤ dyadic a := by
  unfold dyadic
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hab)

theorem h41_dyadic_small {x : ℝ} (hx : 0 < x) : ∃ a, dyadic a < x := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hx (by norm_num : (1/2 : ℝ) < 1)
  exact ⟨n, by unfold dyadic; rw [← inv_pow, ← one_div]; exact hn⟩

theorem h41_grid_dist (I : Finset ℕ) (a : ℕ) (v : Cube I) :
    dist v (operationGridPoint I a (nearestOperationGrid I a v)) ≤ dyadic a / 16 := by
  have hd : 0 ≤ dyadic a / 16 := by have := dyadic_pos a; positivity
  rw [dist_pi_le_iff hd]
  intro i
  have := nearestGrid_dist (2^(a+3)) (by positivity) (v i)
  have e : 1 / (2 * ((2^(a+3) : ℕ) : ℝ)) = dyadic a / 16 := by
    unfold dyadic; push_cast; rw [pow_add]; field_simp; norm_num
  rw [e] at this
  exact this

theorem solution (r : GeneratedRepresentation B γ) (ts : List TailOperation)
    (h : ℕ) (hr : r.operations.length ≤ h) (hj : B.band γ ≤ h)
    (ht : ts.length ≤ h) (hs : ∀ t ∈ ts, t.scaleIndex ≤ h)
    (v : Cube (B.coordinates γ)) (z : SourceSpace B) {δ cap : ℝ}
    (hδ : 0 < δ) (hcap : 0 < cap) :
    ∃ (a : ℕ) (r' : GeneratedRepresentation B γ),
      dyadic a < cap ∧ r'.operations = r.operations++[flattenOperation (B.coordinates γ) a v] ∧
      |completedPairing (sourceClasses B) c0Origin (fun s => r'.value s*tailProduct ts s) z-
        completedPairing (sourceClasses B) c0Origin (fun s => r.value s*tailProduct ts s) z| < δ ∧
      (∀ s, dist (cubeRestrict (B.coordinates γ) s) v < 3*dyadic a/8 →
        r'.value s = r.cubeValue (flattenOperation (B.coordinates γ) a v).point) ∧
      (∀ s, |r'.value s| ≤ (2 : ℝ)^r.operations.length*B.A) := by
  obtain ⟨A0, hA0⟩ := class_pairing_bound (sourceClasses B) c0Origin (2*h+1)
    (4^(h+1)*B.L0+((h+1:ℕ):ℝ≥0)*4^(h+1)*B.A) (by
      rw [sourceClasses_odd]; exact fun f hf => h41_VClass_lip B (h+1) hf)
  have hfT : (fun s => r.value s*tailProduct ts s) ∈ sourceClasses B (2*h+1) := by
    rw [sourceClasses_odd]
    exact ⟨γ, r, ts, by omega, by omega, by omega, fun t ht => (hs t ht).trans (Nat.le_succ h), rfl⟩
  obtain ⟨ε, hε, hεP⟩ := h41_cp_approx (sourceClasses B) c0Origin A0 _ (hA0 _ hfT) z hδ
  have hLu := r.cubeValue_lipschitz
  have hgap : 0 < B.ell (B.band γ)/2 - (r.operations.map CylinderOperation.scale).sum := by
    linarith [r.budget]
  have hL1 : (0:ℝ) < ((4^r.operations.length*B.L0 : ℝ≥0) : ℝ) + 1 := by positivity
  have hpos : 0 < min (min (B.ell (B.band γ)/2 - (r.operations.map CylinderOperation.scale).sum) cap)
      (ε / (((4^r.operations.length*B.L0 : ℝ≥0) : ℝ) + 1)) := by
    apply lt_min (lt_min hgap hcap); positivity
  obtain ⟨a0, ha0⟩ := h41_dyadic_small hpos
  have hm1 := min_le_left (min (B.ell (B.band γ)/2 - (r.operations.map CylinderOperation.scale).sum) cap)
      (ε / (((4^r.operations.length*B.L0 : ℝ≥0) : ℝ) + 1))
  have hm2 := min_le_right (min (B.ell (B.band γ)/2 - (r.operations.map CylinderOperation.scale).sum) cap)
      (ε / (((4^r.operations.length*B.L0 : ℝ≥0) : ℝ) + 1))
  have hm3 := min_le_left (B.ell (B.band γ)/2 - (r.operations.map CylinderOperation.scale).sum) cap
  have hm4 := min_le_right (B.ell (B.band γ)/2 - (r.operations.map CylinderOperation.scale).sum) cap
  have hda : dyadic (a0 + (r.operations.map CylinderOperation.scaleIndex).sum) ≤ dyadic a0 :=
    h41_dyadic_anti (by omega)
  have hord : ∀ p ∈ r.operations, (flattenOperation (B.coordinates γ)
      (a0 + (r.operations.map CylinderOperation.scaleIndex).sum) v).scale ≤ p.scale := by
    intro p hp
    rw [flattenOperation_scale]
    apply h41_dyadic_anti
    have : p.scaleIndex ≤ (r.operations.map CylinderOperation.scaleIndex).sum :=
      List.le_sum_of_mem (List.mem_map_of_mem hp)
    omega
  have hbud : (r.operations.map CylinderOperation.scale).sum + (flattenOperation (B.coordinates γ)
      (a0 + (r.operations.map CylinderOperation.scaleIndex).sum) v).scale < B.ell (B.band γ)/2 := by
    rw [flattenOperation_scale]; linarith
  have hdpos := dyadic_pos (a0 + (r.operations.map CylinderOperation.scaleIndex).sum)
  refine ⟨a0 + (r.operations.map CylinderOperation.scaleIndex).sum, r.append _ hord hbud, ?_, rfl, ?_, ?_, ?_⟩
  · linarith
  · apply hεP
    · apply hA0
      rw [sourceClasses_odd]
      refine ⟨γ, r.append _ hord hbud, ts, ?_, by omega, by omega,
        fun t ht => (hs t ht).trans (Nat.le_succ h), rfl⟩
      simp only [GeneratedRepresentation.append, List.length_append, List.length_singleton]
      omega
    · intro s
      show |(r.append _ hord hbud).cubeValue (cubeRestrict _ s) * tailProduct ts s -
        r.cubeValue (cubeRestrict _ s) * tailProduct ts s| ≤ ε
      rw [GeneratedRepresentation.append_cubeValue, flattenOperation_act, ← sub_mul, abs_mul]
      refine (mul_le_of_le_one_right (abs_nonneg _) (h41_tailProduct_abs ts s)).trans ?_
      refine (h41_localG_sub _ hdpos _ _ hLu _).trans ?_
      have h1 : dyadic (a0 + (r.operations.map CylinderOperation.scaleIndex).sum) <
          ε / (((4^r.operations.length*B.L0 : ℝ≥0) : ℝ) + 1) := by linarith
      rw [lt_div_iff₀ hL1] at h1
      have : (0:ℝ) ≤ ((4^r.operations.length*B.L0 : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
      nlinarith
  · intro s hs
    show (r.append _ hord hbud).cubeValue (cubeRestrict _ s) = r.cubeValue _
    rw [GeneratedRepresentation.append_cubeValue, flattenOperation_act]
    apply h41_localG_flat _ hdpos
    have hg := h41_grid_dist (B.coordinates γ) (a0 + (r.operations.map CylinderOperation.scaleIndex).sum) v
    have ht := dist_triangle (cubeRestrict (B.coordinates γ) s) v
      (flattenOperation (B.coordinates γ) (a0 + (r.operations.map CylinderOperation.scaleIndex).sum) v).point
    have hp : (flattenOperation (B.coordinates γ) (a0 + (r.operations.map CylinderOperation.scaleIndex).sum) v).point
        = operationGridPoint (B.coordinates γ) (a0 + (r.operations.map CylinderOperation.scaleIndex).sum)
          (nearestOperationGrid (B.coordinates γ) (a0 + (r.operations.map CylinderOperation.scaleIndex).sum) v) := rfl
    rw [hp] at ht ⊢
    linarith
  · intro s
    show |(r.append _ hord hbud).cubeValue (cubeRestrict _ s)| ≤ _
    rw [GeneratedRepresentation.append_cubeValue, flattenOperation_act]
    exact h41_localG_sup _ _ _ _ (h41_applyOps_sup r.operations (B.base γ) B.A (B.base_sup γ)) _

