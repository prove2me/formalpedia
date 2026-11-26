-- Prove2me | solution 1 for Kyprianou.Ch04.jointCutoffProbabilityFromSquareCauchyV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:07:38.210437+00:00
-- url     : https://prove2.me/submissions/8f18e906-aeaa-4ac1-ae2f-a206e7d42d47

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_compactSquareSupProbabilityV1
import Theorems.Thm_Kyprianou_Ch04_compactPairSquareProbabilityV1
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Joint compact probability Cauchy estimate from the two maximal square estimates. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (U V : ℝ → NNReal → Ω → ℝ)
    (hC : ∀ W ∈ ({U,V} : Set (ℝ → NNReal → Ω → ℝ)), ∀ T : NNReal, 0 < T →
      ∀ δ : ℝ, 0 < δ → ∃ e0 : ℝ, 0 < e0 ∧ e0 < 1 ∧
        ∀ a b : ℝ, 0 < a → a < e0 → 0 < b → b < e0 →
          (∀ᵐ w ∂P, BddAbove ((fun t : NNReal => |W a t w - W b t w|^2) '' Iic T)) ∧
          Integrable (fun w => sSup ((fun t : NNReal => |W a t w - W b t w|^2) '' Iic T)) P ∧
          (∫ w, sSup ((fun t : NNReal => |W a t w - W b t w|^2) '' Iic T) ∂P) < δ) :
    ∀ i : ℕ, ∃ J : ℕ, ∀ m n, J ≤ m → J ≤ n →
      P {w | ∃ t ≤ (i : NNReal), (2⁻¹ : ℝ)^i <
        dist (U (1 / ((m : ℝ)+2)) t w,V (1 / ((m : ℝ)+2)) t w)
          (U (1 / ((n : ℝ)+2)) t w,V (1 / ((n : ℝ)+2)) t w)} ≤ (2⁻¹ : ENNReal)^i := by
  intro i
  let T : NNReal := (i : NNReal) + 1
  let d : ℝ := (2⁻¹ : ℝ)^i
  let δ := d^2*d/2
  have hd : 0 < d := by dsimp [d]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨a0,ha0,ha1,hA⟩ := hC U (by simp) T (by dsimp [T]; positivity) δ hδ
  obtain ⟨b0,hb0,hb1,hB⟩ := hC V (by simp) T (by dsimp [T]; positivity) δ hδ
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ)+2)
  have he0 : Tendsto e atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => (n : ℝ)+2) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa [e,one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp h
  have hp (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  obtain ⟨J,hJ⟩ := eventually_atTop.mp ((tendsto_order.mp he0).2 (min a0 b0)
    (lt_min ha0 hb0))
  refine ⟨J,fun m n hm hn => ?_⟩
  have ha := hA (e m) (e n) (hp m) ((hJ m hm).trans_le (min_le_left _ _))
    (hp n) ((hJ n hn).trans_le (min_le_left _ _))
  have hb := hB (e m) (e n) (hp m) ((hJ m hm).trans_le (min_le_right _ _))
    (hp n) ((hJ n hn).trans_le (min_le_right _ _))
  have hcalc (x : ℝ) (hx : x ≤ δ) :
      ENNReal.ofReal x / ENNReal.ofReal (d^2) ≤ ENNReal.ofReal (d/2) := by
    rw [← ENNReal.ofReal_div_of_pos (sq_pos_of_pos hd)]
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ (sq_pos_of_pos hd)).2
    calc
      x ≤ δ := hx
      _ = d/2*d^2 := by dsimp [δ]; ring
  have hu := (Kyprianou.Ch04.compactSquareSupProbabilityV1 P
    (U (e m) - U (e n)) T d hd ha.1 ha.2.1).trans (hcalc _ ha.2.2.le)
  have hv := (Kyprianou.Ch04.compactSquareSupProbabilityV1 P
    (V (e m) - V (e n)) T d hd hb.1 hb.2.1).trans (hcalc _ hb.2.2.le)
  have h := Kyprianou.Ch04.compactPairSquareProbabilityV1 P
    (U (e m)) (U (e n)) (V (e m)) (V (e n)) T d d hd.le hu hv
  have hle : (i : NNReal) ≤ T := by dsimp [T]; simp
  have hsub : {w | ∃ t ≤ (i : NNReal), d <
      dist (U (e m) t w,V (e m) t w) (U (e n) t w,V (e n) t w)} ⊆
      {w | ∃ t ≤ T, d < dist (U (e m) t w,V (e m) t w) (U (e n) t w,V (e n) t w)} :=
    fun _ ⟨t,ht,h⟩ => ⟨t,ht.trans hle,h⟩
  have hh := (measure_mono hsub).trans h
  have heq : ENNReal.ofReal d = (2⁻¹ : ENNReal)^i := by
    dsimp [d]
    rw [ENNReal.ofReal_pow (by positivity),ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<2)]
    norm_num
  exact hh.trans_eq heq
