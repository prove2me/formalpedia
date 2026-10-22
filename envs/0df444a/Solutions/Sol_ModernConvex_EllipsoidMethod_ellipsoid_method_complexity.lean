-- Prove2me | solution 1 for ModernConvex.EllipsoidMethod.ellipsoid_method_complexity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:40:44.85156+00:00
-- url     : https://prove2.me/submissions/f6021c72-9947-4be9-9359-bd14f9c4020b

import Mathlib
import Definitions.Def_ModernConvex_EllipsoidMethod_EllipsoidMethod

open Matrix MeasureTheory ModernConvex.EllipsoidMethod
lemma g69el_det_aux {n : ℕ} (hn : 1 ≤ n) (κ μ : ℝ) (hκ : κ ≠ 0) (p : Fin n → ℝ) (hp : p ⬝ᵥ p = 1) :
    det (κ • (1 : Matrix (Fin n) (Fin n) ℝ) + μ • vecMulVec p p) = κ ^ (n - 1) * (κ + μ) := by
  have e : κ • (1 : Matrix (Fin n) (Fin n) ℝ) + μ • vecMulVec p p =
      κ • (1 + vecMulVec ((μ / κ) • p) p) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, vecMulVec_apply, Pi.smul_apply,
      smul_eq_mul]
    field_simp
  rw [e, det_smul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, Fintype.card_fin,
    dotProduct_smul, hp, smul_eq_mul]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  field_simp
  ring

lemma g69el_det_next {n : ℕ} (hn : 2 ≤ n) (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    (nextMatrix B a).det = B.det * (((n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1)) ^ (n - 1) * ((n:ℝ) / ((n:ℝ) + 1))) := by
  have hN : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hw : 0 < (n:ℝ) ^ 2 - 1 := by nlinarith
  have hs : 0 < Real.sqrt ((n:ℝ) ^ 2 - 1) := Real.sqrt_pos.2 hw
  have hκ : 0 < (n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1) := div_pos (by linarith) hs
  set w := Bᵀ *ᵥ a with hwdef
  have hBt : IsUnit Bᵀ.det := by rw [det_transpose]; exact isUnit_iff_ne_zero.mpr hB
  have hw0 : w ≠ 0 := by
    intro h
    apply ha
    have : (Bᵀ)⁻¹ *ᵥ w = a := by rw [hwdef, mulVec_mulVec, nonsing_inv_mul _ hBt, one_mulVec]
    rw [← this, h, mulVec_zero]
  have hq : a ⬝ᵥ ((B * Bᵀ) *ᵥ a) = w ⬝ᵥ w := by
    rw [← mulVec_mulVec, dotProduct_mulVec, hwdef, ← mulVec_transpose]
  have hqpos : 0 < w ⬝ᵥ w := by
    have h0 : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg fun i _ => mul_self_nonneg (w i)
    exact lt_of_le_of_ne h0 (Ne.symm (fun h => hw0 (dotProduct_self_eq_zero.mp h)))
  have hp : cutDirection B a ⬝ᵥ cutDirection B a = 1 := by
    unfold cutDirection
    rw [hq, ← hwdef, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc]
    rw [one_div_mul_one_div, Real.mul_self_sqrt hqpos.le]
    field_simp
  have e : nextMatrix B a = B * (((n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1)) • (1 : Matrix (Fin n) (Fin n) ℝ) +
      ((n:ℝ) / ((n:ℝ) + 1) - (n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1)) •
        vecMulVec (cutDirection B a) (cutDirection B a)) := by
    unfold nextMatrix
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, mul_vecMulVec]
  rw [e, det_mul, g69el_det_aux (by omega) _ _ hκ.ne' _ hp]
  ring

lemma g69el_vol {n : ℕ} (c : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ) :
    MeasureTheory.volume (ellipsoid c B) =
      ENNReal.ofReal |B.det| * MeasureTheory.volume {u : Fin n → ℝ | u ⬝ᵥ u ≤ 1} := by
  have : ellipsoid c B = (fun x => c + x) '' (Matrix.toLin' B '' {u | u ⬝ᵥ u ≤ 1}) := by
    ext x
    simp only [ellipsoid, Set.mem_setOf_eq, Set.mem_image, Matrix.toLin'_apply]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨B *ᵥ u, ⟨u, hu, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩; exact ⟨u, hu, rfl⟩
  rw [this, Set.image_add_left, MeasureTheory.measure_preimage_add,
    MeasureTheory.Measure.addHaar_image_linearMap, LinearMap.det_toLin']

lemma g69el_unit {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) (a : Fin n → ℝ) (ha : a ≠ 0) :
    cutDirection B a ⬝ᵥ cutDirection B a = 1 ∧
      Bᵀ *ᵥ a = Real.sqrt (a ⬝ᵥ ((B * Bᵀ) *ᵥ a)) • cutDirection B a ∧
      0 < Real.sqrt (a ⬝ᵥ ((B * Bᵀ) *ᵥ a)) := by
  set w := Bᵀ *ᵥ a with hwdef
  have hBt : IsUnit Bᵀ.det := by rw [det_transpose]; exact isUnit_iff_ne_zero.mpr hB
  have hw0 : w ≠ 0 := by
    intro h
    apply ha
    have : (Bᵀ)⁻¹ *ᵥ w = a := by rw [hwdef, mulVec_mulVec, nonsing_inv_mul _ hBt, one_mulVec]
    rw [← this, h, mulVec_zero]
  have hq : a ⬝ᵥ ((B * Bᵀ) *ᵥ a) = w ⬝ᵥ w := by
    rw [← mulVec_mulVec, dotProduct_mulVec, hwdef, ← mulVec_transpose]
  have hqpos : 0 < w ⬝ᵥ w := by
    have h0 : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg fun i _ => mul_self_nonneg (w i)
    exact lt_of_le_of_ne h0 (Ne.symm (fun h => hw0 (dotProduct_self_eq_zero.mp h)))
  have hsq : 0 < Real.sqrt (w ⬝ᵥ w) := Real.sqrt_pos.2 hqpos
  refine ⟨?_, ?_, by rw [hq]; exact hsq⟩
  · unfold cutDirection
    rw [hq, ← hwdef, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc]
    rw [one_div_mul_one_div, Real.mul_self_sqrt hqpos.le]
    field_simp
  · unfold cutDirection
    rw [hq, ← hwdef, smul_smul, mul_one_div_cancel hsq.ne', one_smul]

lemma g69el_half {n : ℕ} (hn : 1 < n) (c : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    halfEllipsoid c B a ⊆ ellipsoid (nextCenter c B a) (nextMatrix B a) := by
  obtain ⟨hp, hBa, hsq⟩ := g69el_unit B hB a ha
  set p := cutDirection B a with hpdef
  set q := Real.sqrt (a ⬝ᵥ ((B * Bᵀ) *ᵥ a))
  have hN : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hw : 0 < (n:ℝ) ^ 2 - 1 := by nlinarith
  have hs : 0 < Real.sqrt ((n:ℝ) ^ 2 - 1) := Real.sqrt_pos.2 hw
  set κ := (n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1) with hκdef
  set l := (n:ℝ) / ((n:ℝ) + 1) with hldef
  have hκ : 0 < κ := div_pos (by linarith) hs
  have hl : 0 < l := div_pos (by linarith) (by linarith)
  rintro x ⟨⟨u, hu, rfl⟩, hcut⟩
  set s := p ⬝ᵥ u with hsdef
  set δ := 1 / ((n:ℝ) + 1) with hδdef
  -- s ≤ 0
  have hs0 : s ≤ 0 := by
    have h1 : a ⬝ᵥ (B *ᵥ u) ≤ 0 := by
      rw [dotProduct_add] at hcut; linarith
    have h2 : a ⬝ᵥ (B *ᵥ u) = q * s := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hBa, smul_dotProduct, smul_eq_mul]
    rw [h2] at h1
    by_contra hc; push Not at hc
    have := mul_pos hsq hc; linarith
  -- |u - s p|² = u⬝u - s²
  have hperp : (u - s • p) ⬝ᵥ (u - s • p) = u ⬝ᵥ u - s ^ 2 := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul, hp]
    rw [dotProduct_comm u p]; ring
  have hp_perp : p ⬝ᵥ (u - s • p) = 0 := by
    rw [dotProduct_sub, dotProduct_smul, hp, smul_eq_mul]; ring
  have hnn : 0 ≤ (u - s • p) ⬝ᵥ (u - s • p) := by
    unfold dotProduct; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hsge : -1 ≤ s := by nlinarith
  refine ⟨κ⁻¹ • (u - s • p) + l⁻¹ • ((s + δ) • p), ?_, ?_⟩
  · -- norm bound
    have e : (κ⁻¹ • (u - s • p) + l⁻¹ • ((s + δ) • p)) ⬝ᵥ (κ⁻¹ • (u - s • p) + l⁻¹ • ((s + δ) • p))
        = κ⁻¹ ^ 2 * (u ⬝ᵥ u - s ^ 2) + l⁻¹ ^ 2 * (s + δ) ^ 2 := by
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul, hperp, hp]
      rw [dotProduct_comm (u - s • p) p, hp_perp]; ring
    rw [e]
    have hκ2 : κ⁻¹ ^ 2 = ((n:ℝ) ^ 2 - 1) / (n:ℝ) ^ 2 := by
      rw [hκdef, inv_div, div_pow, Real.sq_sqrt hw.le]
    have hl2 : l⁻¹ ^ 2 = ((n:ℝ) + 1) ^ 2 / (n:ℝ) ^ 2 := by rw [hldef, inv_div, div_pow]
    rw [hκ2, hl2, hδdef]
    have hn0 : (0:ℝ) < (n:ℝ) ^ 2 := by positivity
    have hn1 : (0:ℝ) < (n:ℝ) + 1 := by linarith
    have key : ((n:ℝ) ^ 2 - 1) / (n:ℝ) ^ 2 * (u ⬝ᵥ u - s ^ 2) +
        ((n:ℝ) + 1) ^ 2 / (n:ℝ) ^ 2 * (s + 1 / ((n:ℝ) + 1)) ^ 2 =
        (((n:ℝ) ^ 2 - 1) * (u ⬝ᵥ u - s ^ 2) + (((n:ℝ) + 1) * s + 1) ^ 2) / (n:ℝ) ^ 2 := by
      field_simp
    rw [key, div_le_one hn0]
    have h1 := mul_le_mul_of_nonneg_left hu hw.le
    have h2 := mul_nonneg hn1.le (mul_nonneg (neg_nonneg.mpr hs0) (show 0 ≤ s + 1 by linarith))
    nlinarith
  · -- the point
    have hvm : ∀ v w z : Fin n → ℝ, vecMulVec (B *ᵥ v) w *ᵥ z = (w ⬝ᵥ z) • (B *ᵥ v) := by
      intro v w z; ext i; simp [vecMulVec, mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
    unfold nextCenter nextMatrix
    rw [← hpdef, add_mulVec, smul_mulVec, smul_mulVec, hvm]
    have hdot : p ⬝ᵥ (κ⁻¹ • (u - s • p) + l⁻¹ • ((s + δ) • p)) = l⁻¹ * (s + δ) := by
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, hp_perp, dotProduct_smul, hp]; simp
    rw [hdot]
    simp only [mulVec_add, mulVec_smul, mulVec_sub]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    simp only [hκdef, hldef, hδdef]
    have hn0 : (n:ℝ) ≠ 0 := by positivity
    have hn1 : (n:ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

lemma g70mc1_cs {n : ℕ} (a z : Fin n → ℝ) : a ⬝ᵥ z ≤ eucNorm a * eucNorm z := by
  unfold eucNorm dotProduct
  have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a z
  simpa [sq] using this

lemma g70mc1_unitball_pos (n : ℕ) :
    0 < volume {u : Fin n → ℝ | u ⬝ᵥ u ≤ 1} := by
  have ho : IsOpen {u : Fin n → ℝ | u ⬝ᵥ u < 1} := by
    apply isOpen_lt _ continuous_const
    unfold dotProduct; fun_prop
  have hne : ({u : Fin n → ℝ | u ⬝ᵥ u < 1}).Nonempty := ⟨0, by simp⟩
  exact lt_of_lt_of_le (ho.measure_pos volume hne) (measure_mono fun u (hu : u ⬝ᵥ u < 1) => (le_of_lt hu : u ⬝ᵥ u ≤ 1))

lemma g70mc1_unitball_fin (n : ℕ) :
    volume {u : Fin n → ℝ | u ⬝ᵥ u ≤ 1} < ⊤ := by
  apply Bornology.IsBounded.measure_lt_top
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨1, fun u hu => ?_⟩
  simp only [Set.mem_setOf_eq] at hu
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs, abs_le_one_iff_mul_self_le_one]
  have : u i * u i ≤ u ⬝ᵥ u := by
    unfold dotProduct
    exact Finset.single_le_sum (f := fun j => u j * u j) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  linarith

/-- a ball of radius ρ > radius B cannot be inside the ellipsoid -/
lemma g70mc1_not_sub {n : ℕ} (hn : 1 ≤ n) (c z : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (ρ : ℝ) (hρ : radius B < ρ) :
    ∃ x ∈ ellipsoid z (ρ • (1 : Matrix (Fin n) (Fin n) ℝ)), x ∉ ellipsoid c B := by
  by_contra hcon
  push Not at hcon
  have hsub : ellipsoid z (ρ • (1 : Matrix (Fin n) (Fin n) ℝ)) ⊆ ellipsoid c B := hcon
  have hm := measure_mono (μ := volume) hsub
  rw [g69el_vol, g69el_vol] at hm
  have hpos := g70mc1_unitball_pos n
  have hfin := g70mc1_unitball_fin n
  have hm2 := (ENNReal.mul_le_mul_iff_left hpos.ne' hfin.ne).1 hm
  have hrad0 : 0 ≤ radius B := by unfold radius; positivity
  have hρ0 : 0 < ρ := lt_of_le_of_lt hrad0 hρ
  rw [det_smul, det_one, mul_one, Fintype.card_fin, abs_of_pos (pow_pos hρ0 n)] at hm2
  rw [ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)] at hm2
  have hn0 : n ≠ 0 := by omega
  have e : (radius B) ^ n = |B.det| := by
    unfold radius; rw [one_div]; exact Real.rpow_inv_natCast_pow (abs_nonneg _) hn0
  have := pow_lt_pow_left₀ hρ hrad0 hn0
  linarith

def g70mc1_Inv {n : ℕ} (f : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ))
    (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (R : ℝ) (s : State n) : Prop :=
  s.B.det ≠ 0 ∧ 0 ≤ s.L ∧ (∀ b, s.best = some b → b ∈ X) ∧
  ∀ x ∈ X, x ∈ ellipsoid s.c s.B ∨ ∃ c ∈ X, ∃ b, s.best = some b ∧ f b ≤ f c ∧
     0 < (O c).2 ⬝ᵥ (x - c) ∧ R * eucNorm (O c).2 - (O c).2 ⬝ᵥ c ≤ s.L

lemma g70mc1_ub {n : ℕ} (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (best : Option (Fin n → ℝ))
    (x : Fin n → ℝ) : ∃ b', updateBest O best x = some b' ∧ (O b').1 ≤ (O x).1 ∧
      (∀ b, best = some b → (O b').1 ≤ (O b).1) ∧ (b' = x ∨ best = some b') := by
  cases best with
  | none => exact ⟨x, rfl, le_rfl, by simp, Or.inl rfl⟩
  | some y =>
    by_cases h : (O x).1 < (O y).1
    · refine ⟨x, by simp [updateBest, h], le_rfl, ?_, Or.inl rfl⟩
      intro b hb; cases hb; exact h.le
    · refine ⟨y, by simp [updateBest, h], not_lt.1 h, ?_, Or.inr rfl⟩
      intro b hb; cases hb; exact le_rfl

lemma g70mc1_detc {n : ℕ} (hn : 2 ≤ n) :
    ((n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1)) ^ (n - 1) * ((n:ℝ) / ((n:ℝ) + 1)) ≠ 0 := by
  have hN : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hw : 0 < (n:ℝ) ^ 2 - 1 := by nlinarith
  have hs : 0 < Real.sqrt ((n:ℝ) ^ 2 - 1) := Real.sqrt_pos.2 hw
  exact (mul_pos (pow_pos (div_pos (by linarith) hs) _) (div_pos (by linarith) (by linarith))).ne'

lemma g70mc1_step_inv {n : ℕ} (hn : 2 ≤ n) {f : (Fin n → ℝ) → ℝ} {X : Set (Fin n → ℝ)}
    {sep : (Fin n → ℝ) → Option (Fin n → ℝ)} (hsep : IsSeparationOracle X sep)
    {O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)} (hO : IsFirstOrderOracle f O) (R : ℝ)
    (s s' : State n) (hI : g70mc1_Inv f X O R s) (h : step sep O R s = StepResult.next s') :
    g70mc1_Inv f X O R s' := by
  obtain ⟨hdet, hL, hbX, hcov⟩ := hI
  unfold step at h
  rcases hs : sep s.c with _ | a
  · rw [hs] at h
    simp only at h
    split_ifs at h with h0
    cases h
    have hcX : s.c ∈ X := ((hsep s.c).1).1 hs
    obtain ⟨b', hub, hb'x, hb'b, hb'or⟩ := g70mc1_ub O s.best s.c
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only
      rw [g69el_det_next hn _ hdet _ h0]
      exact mul_ne_zero hdet (g70mc1_detc hn)
    · exact le_max_of_le_left hL
    · intro b hb
      simp only at hb
      rw [hub] at hb
      cases hb
      rcases hb'or with rfl | h
      · exact hcX
      · exact hbX _ h
    · intro x hx
      simp only
      rcases hcov x hx with hE | ⟨c, hc, b, hb, hfb, hpos, hl⟩
      · by_cases hcut : (O s.c).2 ⬝ᵥ x ≤ (O s.c).2 ⬝ᵥ s.c
        · left; exact g69el_half (by omega) _ _ hdet _ h0 ⟨hE, hcut⟩
        · right
          refine ⟨s.c, hcX, b', hub, ?_, ?_, le_max_right _ _⟩
          · rw [← (hO b').1, ← (hO s.c).1]; exact hb'x
          · rw [dotProduct_sub]; linarith
      · right
        refine ⟨c, hc, b', hub, ?_, hpos, le_max_of_le_left hl⟩
        have := hb'b b hb
        rw [(hO b').1, (hO b).1] at this
        linarith
  · rw [hs] at h
    simp only at h
    cases h
    obtain ⟨ha0, hsepa⟩ := (hsep s.c).2 a hs
    refine ⟨?_, hL, hbX, ?_⟩
    · simp only
      rw [g69el_det_next hn _ hdet _ ha0]
      exact mul_ne_zero hdet (g70mc1_detc hn)
    · intro x hx
      simp only
      rcases hcov x hx with hE | hw
      · left; exact g69el_half (by omega) _ _ hdet _ ha0 ⟨hE, hsepa x hx⟩
      · right; exact hw

lemma g70mc1_run_inv {n : ℕ} (hn : 2 ≤ n) {f : (Fin n → ℝ) → ℝ} {X : Set (Fin n → ℝ)}
    {sep : (Fin n → ℝ) → Option (Fin n → ℝ)} (hsep : IsSeparationOracle X sep)
    {O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)} (hO : IsFirstOrderOracle f O) (R r ε : ℝ) (hR : 0 < R)
    (hXR : X ⊆ {x | eucNorm x ≤ R}) :
    ∀ (t : ℕ) (s : State n), run sep O R r ε t = Outcome.running s → g70mc1_Inv f X O R s := by
  intro t
  induction t with
  | zero =>
    intro s h
    simp only [run] at h
    cases h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [initState, det_smul, det_one, Fintype.card_fin, mul_one]
      exact (pow_pos hR n).ne'
    · simp [initState]
    · simp [initState]
    · intro x hx
      left
      have hxR : eucNorm x ≤ R := hXR hx
      have hxx : x ⬝ᵥ x ≤ R ^ 2 := by
        have h0 : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
        have := Real.sq_sqrt h0
        unfold eucNorm at hxR
        rw [← this]
        exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hxR 2
      refine ⟨R⁻¹ • x, ?_, ?_⟩
      · rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
        rw [← mul_assoc, ← sq, inv_pow]
        rw [inv_mul_le_iff₀ (by positivity)]; simpa using hxx
      · simp only [initState, smul_mulVec, one_mulVec, smul_smul, mul_inv_cancel₀ hR.ne',
          one_smul, zero_add]
  | succ t ih =>
    intro s h
    simp only [run] at h
    rcases hr : run sep O R r ε t with s0 | x
    · rw [hr] at h
      simp only at h
      rcases hst : step sep O R s0 with x | s'
      · rw [hst] at h; simp only at h; cases h
      · rw [hst] at h
        simp only at h
        split_ifs at h
        all_goals cases h
        exact g70mc1_step_inv hn hsep hO R s0 _ (ih s0 hr) hst
    · rw [hr] at h; simp only at h; cases h

lemma g70mc1_final {n : ℕ} (hn : 2 ≤ n) {f : (Fin n → ℝ) → ℝ} {X : Set (Fin n → ℝ)} {r R : ℝ}
    (hP : IsBlackBoxProgram f X r R)
    {O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)} (hO : IsFirstOrderOracle f O) (ε : ℝ) (hε : 0 < ε)
    (s : State n) (hI : g70mc1_Inv f X O R s) (hcond : radius s.B / r < ε / (s.L + ε)) :
    ∃ xhat : Fin n → ℝ, s.best = some xhat ∧ xhat ∈ X ∧ ∀ y ∈ X, f xhat - f y ≤ ε := by
  obtain ⟨_, hXconv, _, _, _, hr, _, hXR, xbar, hball⟩ := hP
  obtain ⟨_, hL, hbX, hcov⟩ := hI
  set L := s.L with hLdef
  set ν := ε / (L + ε) with hνdef
  have hLε : 0 < L + ε := by linarith
  have hν0 : 0 < ν := div_pos hε hLε
  have hν1 : ν ≤ 1 := by rw [div_le_one hLε]; linarith
  have h1 : (1 - ν) * (L + ε) = L := by rw [hνdef]; field_simp; ring
  have h2 : ν * (L + ε) = ε := by rw [hνdef]; field_simp
  have hlt : radius s.B < ν * r := by rwa [div_lt_iff₀ hr] at hcond
  have key : ∀ y ∈ X, ∃ b, s.best = some b ∧ f b - f y ≤ ε := by
    intro y hy
    obtain ⟨x, ⟨u, hu, hxu⟩, hxE⟩ :=
      g70mc1_not_sub (by omega) s.c (y + ν • (xbar - y)) s.B (ν * r) hlt
    set z := xbar + r • u with hz
    have hzX : z ∈ X := by
      apply hball
      show eucNorm (z - xbar) ≤ r
      have e : z - xbar = r • u := by rw [hz]; abel
      rw [e]
      unfold eucNorm
      rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq]
      rw [Real.sqrt_le_left hr.le]
      calc r ^ 2 * (u ⬝ᵥ u) ≤ r ^ 2 * 1 := mul_le_mul_of_nonneg_left hu (sq_nonneg r)
        _ = r ^ 2 := mul_one _
    have hxeq : x = (1 - ν) • y + ν • z := by
      rw [hxu, hz]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, smul_mulVec, one_mulVec]
      ring
    have hxX : x ∈ X := by
      rw [hxeq]; exact hXconv hy hzX (by linarith) hν0.le (by ring)
    rcases hcov x hxX with hE | ⟨c, hc, b, hb, hfb, hpos, hl⟩
    · exact absurd hE hxE
    refine ⟨b, hb, ?_⟩
    set a := (O c).2
    have hsub := (hO c).2 y
    have hcs : a ⬝ᵥ z ≤ eucNorm a * R := by
      have h0 : 0 ≤ eucNorm a := Real.sqrt_nonneg _
      exact (g70mc1_cs a z).trans (mul_le_mul_of_nonneg_left (hXR hzX) h0)
    have hdot : a ⬝ᵥ (x - c) = (1 - ν) * (a ⬝ᵥ y - a ⬝ᵥ c) + ν * (a ⬝ᵥ z - a ⬝ᵥ c) := by
      rw [hxeq]
      simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul]
      ring
    have hW : a ⬝ᵥ z - a ⬝ᵥ c ≤ L := by linarith
    rw [hdot] at hpos
    have hsub' : f c - f y ≤ a ⬝ᵥ c - a ⬝ᵥ y := by
      simp only [dotProduct_sub] at hsub; linarith
    set D := a ⬝ᵥ c - a ⬝ᵥ y
    have hm := mul_lt_mul_of_pos_right hpos hLε
    have e3 : ((1 - ν) * (a ⬝ᵥ y - a ⬝ᵥ c) + ν * (a ⬝ᵥ z - a ⬝ᵥ c)) * (L + ε)
        = -(L * D) + ε * (a ⬝ᵥ z - a ⬝ᵥ c) := by
      have : ((1 - ν) * (a ⬝ᵥ y - a ⬝ᵥ c) + ν * (a ⬝ᵥ z - a ⬝ᵥ c)) * (L + ε)
          = -((1 - ν) * (L + ε)) * D + (ν * (L + ε)) * (a ⬝ᵥ z - a ⬝ᵥ c) := by ring
      rw [this, h1, h2]; ring
    rw [e3, zero_mul] at hm
    have hεW := mul_le_mul_of_nonneg_left hW hε.le
    by_contra hcon
    push Not at hcon
    have hD : ε < D := by linarith
    have := mul_le_mul_of_nonneg_left hD.le hL
    nlinarith
  obtain ⟨b, hb, _⟩ := key xbar (hball (by simp [eucNorm, hr.le]))
  refine ⟨b, hb, hbX b hb, fun y hy => ?_⟩
  obtain ⟨b2, hb2, h⟩ := key y hy
  rw [hb] at hb2; cases hb2; exact h

theorem g70mc1_term {n : ℕ} (hn : 2 ≤ n)
    (f : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ)) (r R : ℝ) (hP : IsBlackBoxProgram f X r R)
    (sep : (Fin n → ℝ) → Option (Fin n → ℝ)) (hsep : IsSeparationOracle X sep)
    (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (hO : IsFirstOrderOracle f O)
    (ε : ℝ) (hε : 0 < ε)
    (t : ℕ) (result : Option (Fin n → ℝ)) (hterm : TerminatesAt sep O R r ε t result) :
    ∃ xhat : Fin n → ℝ, result = some xhat ∧ xhat ∈ X ∧ ∀ y ∈ X, f xhat - f y ≤ ε := by
  obtain ⟨ht1, ⟨s, hs⟩, hstop⟩ := hterm
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hs
  have hR : 0 < R := hP.2.2.2.2.2.2.1
  have hXR : X ⊆ {x | eucNorm x ≤ R} := hP.2.2.2.2.2.2.2.1
  have hI := g70mc1_run_inv hn hsep hO R r ε hR hXR t' s hs
  simp only [run, hs] at hstop
  rcases hst : step sep O R s with x | s'
  · rw [hst] at hstop
    simp only [Outcome.stopped.injEq] at hstop
    subst hstop
    unfold step at hst
    rcases hsc : sep s.c with _ | a
    · rw [hsc] at hst
      simp only at hst
      split_ifs at hst with h0
      cases hst
      refine ⟨s.c, rfl, ((hsep s.c).1).1 hsc, fun y _ => ?_⟩
      have := (hO s.c).2 y
      rw [h0, zero_dotProduct] at this
      linarith
    · rw [hsc] at hst; simp only at hst; cases hst
  · rw [hst] at hstop
    simp only at hstop
    split_ifs at hstop with hcond
    · simp only [Outcome.stopped.injEq] at hstop
      subst hstop
      exact g70mc1_final hn hP hO ε hε s' (g70mc1_step_inv hn hsep hO R s s' hI hst) hcond

lemma g69el_log_le (v : ℝ) (hv : 0 ≤ v) : Real.log (1 + v) ≤ v - v ^ 2 / 2 + v ^ 3 / 3 := by
  let g : ℝ → ℝ := fun t => t - t ^ 2 / 2 + t ^ 3 / 3 - Real.log (1 + t)
  have hd : ∀ t, 0 ≤ t → HasDerivAt g (t ^ 3 / (1 + t)) t := by
    intro t ht
    have h1 : (1 + t) ≠ 0 := by linarith
    have := ((((hasDerivAt_id t).sub ((hasDerivAt_pow 2 t).div_const 2)).add
      ((hasDerivAt_pow 3 t).div_const 3)).sub (((hasDerivAt_const t (1:ℝ)).add (hasDerivAt_id t)).log h1))
    refine this.congr_deriv ?_
    simp only [Pi.add_apply, id]
    field_simp; ring
  have hmono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro t ht; exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht; rw [interior_Ici] at ht; exact (hd t (le_of_lt ht)).differentiableAt.differentiableWithinAt
    · intro t ht; rw [interior_Ici] at ht; rw [(hd t (le_of_lt ht)).deriv]
      have : (0:ℝ) < t := ht; positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hv) hv
  simp only [g] at this; simp at this; linarith

lemma g69el_log_ge (x : ℝ) (hx : 0 ≤ x) : x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4 ≤ Real.log (1 + x) := by
  let g : ℝ → ℝ := fun t => Real.log (1 + t) - (t - t ^ 2 / 2 + t ^ 3 / 3 - t ^ 4 / 4)
  have hd : ∀ t, 0 ≤ t → HasDerivAt g (t ^ 4 / (1 + t)) t := by
    intro t ht
    have h1 : (1 + t) ≠ 0 := by linarith
    have := (((hasDerivAt_const t (1:ℝ)).add (hasDerivAt_id t)).log h1).sub
      ((((hasDerivAt_id t).sub ((hasDerivAt_pow 2 t).div_const 2)).add
        ((hasDerivAt_pow 3 t).div_const 3)).sub ((hasDerivAt_pow 4 t).div_const 4))
    refine this.congr_deriv ?_
    simp only [Pi.add_apply, id]
    field_simp; ring
  have hmono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro t ht; exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht; rw [interior_Ici] at ht; exact (hd t (le_of_lt ht)).differentiableAt.differentiableWithinAt
    · intro t ht; rw [interior_Ici] at ht; rw [(hd t (le_of_lt ht)).deriv]
      have : (0:ℝ) < t := ht; positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  simp only [g] at this; simp at this; linarith

/-- the rational inequality behind the volume decrease -/
lemma g69el_rat (n : ℝ) (hn : 2 ≤ n) :
    (n - 1) / 2 * (1 / (n ^ 2 - 1) - (1 / (n ^ 2 - 1)) ^ 2 / 2 + (1 / (n ^ 2 - 1)) ^ 3 / 3)
      - (1 / n - (1 / n) ^ 2 / 2 + (1 / n) ^ 3 / 3 - (1 / n) ^ 4 / 4) ≤ -1 / (2 * n) := by
  have h1 : 0 < n ^ 2 - 1 := by nlinarith
  have h2 : 0 < n := by linarith
  set P : ℝ := -n ^ 7 + 5 * n ^ 5 - 2 * n ^ 4 - 6 * n ^ 3 + 3 * n ^ 2 + 4 * n - 3 with hPdef
  have key : ((n - 1) / 2 * (1 / (n ^ 2 - 1) - (1 / (n ^ 2 - 1)) ^ 2 / 2 + (1 / (n ^ 2 - 1)) ^ 3 / 3)
      - (1 / n - (1 / n) ^ 2 / 2 + (1 / n) ^ 3 / 3 - (1 / n) ^ 4 / 4)) - (-1 / (2 * n))
      = P / (12 * (n ^ 2 - 1) ^ 3 * n ^ 4) := by
    rw [hPdef]; field_simp; ring
  have hP : P ≤ 0 := by
    have hm : 0 ≤ n - 2 := by linarith
    have e : P = -((n - 2) ^ 7 + 14 * (n - 2) ^ 6 + 79 * (n - 2) ^ 5 + 232 * (n - 2) ^ 4
      + 382 * (n - 2) ^ 3 + 353 * (n - 2) ^ 2 + 168 * (n - 2) + 31) := by rw [hPdef]; ring
    rw [e]; exact neg_nonpos.mpr (by positivity)
  have : P / (12 * (n ^ 2 - 1) ^ 3 * n ^ 4) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hP (by positivity)
  linarith

lemma g69el_bound (n : ℕ) (hn : 2 ≤ n) :
    ((n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1)) ^ (n - 1) * ((n:ℝ) / ((n:ℝ) + 1)) ≤
      Real.exp (-1 / (2 * (n:ℝ))) := by
  have hN : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hw : 0 < (n:ℝ) ^ 2 - 1 := by nlinarith
  have hs : 0 < Real.sqrt ((n:ℝ) ^ 2 - 1) := Real.sqrt_pos.2 hw
  have hκ : 0 < (n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1) := div_pos (by linarith) hs
  have hl0 : 0 < (n:ℝ) / ((n:ℝ) + 1) := div_pos (by linarith) (by linarith)
  have hκ2 : ((n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1)) ^ 2 = 1 + 1 / ((n:ℝ) ^ 2 - 1) := by
    rw [div_pow, Real.sq_sqrt hw.le]; field_simp; ring
  have hlogκ : Real.log ((n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1)) = Real.log (1 + 1 / ((n:ℝ) ^ 2 - 1)) / 2 := by
    rw [← hκ2, Real.log_pow]; push_cast; ring
  have hl : (n:ℝ) / ((n:ℝ) + 1) = (1 + 1 / (n:ℝ))⁻¹ := by field_simp
  have hlogl : Real.log ((n:ℝ) / ((n:ℝ) + 1)) = -Real.log (1 + 1 / (n:ℝ)) := by rw [hl, Real.log_inv]
  rw [← Real.log_le_iff_le_exp (mul_pos (pow_pos hκ _) hl0), Real.log_mul (pow_pos hκ _).ne' hl0.ne',
    Real.log_pow, hlogκ, hlogl]
  have h1 := g69el_log_le (1 / ((n:ℝ) ^ 2 - 1)) (by positivity)
  have h2 := g69el_log_ge (1 / (n:ℝ)) (by positivity)
  have h3 := g69el_rat (n:ℝ) hN
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n:ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hn1]
  have hN1 : 0 ≤ ((n:ℝ) - 1) / 2 := by linarith
  have := mul_le_mul_of_nonneg_left h1 hN1
  nlinarith

lemma g69el_step {n : ℕ} {X : Set (Fin n → ℝ)} {sep : (Fin n → ℝ) → Option (Fin n → ℝ)}
    (hsep : IsSeparationOracle X sep) (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (R : ℝ) (s s' : State n)
    (h : step sep O R s = StepResult.next s') : ∃ a : Fin n → ℝ, a ≠ 0 ∧ s'.B = nextMatrix s.B a := by
  unfold step at h
  rcases hs : sep s.c with _ | a
  · rw [hs] at h
    simp only at h
    split_ifs at h with h0
    all_goals cases h
    exact ⟨(O s.c).2, h0, rfl⟩
  · rw [hs] at h
    simp only at h
    cases h
    exact ⟨a, ((hsep s.c).2 a hs).1, rfl⟩

lemma g69el_inv {n : ℕ} (hn : 2 ≤ n) {X : Set (Fin n → ℝ)} {sep : (Fin n → ℝ) → Option (Fin n → ℝ)}
    (hsep : IsSeparationOracle X sep) (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (R r ε : ℝ) (hR : 0 < R) :
    ∀ (t : ℕ) (s : State n), run sep O R r ε t = Outcome.running s →
      s.B.det ≠ 0 ∧ |s.B.det| ≤ (((n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1)) ^ (n - 1) *
        ((n:ℝ) / ((n:ℝ) + 1))) ^ t * R ^ n := by
  have hN : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hw : 0 < (n:ℝ) ^ 2 - 1 := by nlinarith
  have hs : 0 < Real.sqrt ((n:ℝ) ^ 2 - 1) := Real.sqrt_pos.2 hw
  have hc : 0 < ((n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1)) ^ (n - 1) * ((n:ℝ) / ((n:ℝ) + 1)) :=
    mul_pos (pow_pos (div_pos (by linarith) hs) _) (div_pos (by linarith) (by linarith))
  intro t
  induction t with
  | zero =>
    intro s h
    simp only [run] at h
    cases h
    simp only [initState, det_smul, det_one, Fintype.card_fin, mul_one, pow_zero, one_mul]
    exact ⟨(pow_pos hR n).ne', (abs_of_pos (pow_pos hR n)).le⟩
  | succ t ih =>
    intro s h
    simp only [run] at h
    rcases hr : run sep O R r ε t with s0 | x
    · rw [hr] at h
      simp only at h
      rcases hst : step sep O R s0 with x | s'
      · rw [hst] at h; simp only at h; cases h
      · rw [hst] at h
        simp only at h
        split_ifs at h
        all_goals cases h
        obtain ⟨a, ha, hB⟩ := g69el_step hsep O R s0 _ hst
        obtain ⟨h0, hle⟩ := ih s0 hr
        rw [hB, g69el_det_next hn _ h0 a ha, abs_mul, abs_of_pos hc, pow_succ]
        refine ⟨mul_ne_zero h0 hc.ne', ?_⟩
        calc |s0.B.det| * _ ≤ (_ ^ t * R ^ n) * _ := mul_le_mul_of_nonneg_right hle hc.le
          _ = _ := by ring
    · rw [hr] at h; simp only at h; cases h


open Matrix MeasureTheory
open ModernConvex.EllipsoidMethod
/-- Ben-Tal–Nemirovski, p. 350, Eq. (5.2.21), in the proof of Theorem 5.2.1. Let the ellipsoid
method with accuracy `ε > 0` be applied to (5.2.9) of dimension `n ≥ 2` under assumption A,
with a separation oracle for `X` and a first order oracle for `f`. If the method is still
running after `t` steps and step `t + 1` performs rule 3 (it does not stop by rule 2), the
new ellipsoid `E_{t+1} = {c_{t+1} + B_{t+1}u | uᵀu ≤ 1}` satisfies
`ρ_{t+1} = |Det B_{t+1}|^{1/n} ≤ exp{−(t+1)/(2n²)} R`. -/
theorem g70mc1_rad {n : ℕ} (hn : 2 ≤ n)
    (f : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ)) (r R : ℝ) (hP : IsBlackBoxProgram f X r R)
    (sep : (Fin n → ℝ) → Option (Fin n → ℝ)) (hsep : IsSeparationOracle X sep)
    (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (hO : IsFirstOrderOracle f O)
    (ε : ℝ) (hε : 0 < ε)
    (t : ℕ) (s s' : State n) (hrun : run sep O R r ε t = Outcome.running s)
    (hstep : step sep O R s = StepResult.next s') :
    radius s'.B ≤ Real.exp (-((t : ℝ) + 1) / (2 * (n : ℝ) ^ 2)) * R := by
  have hR : 0 < R := hP.2.2.2.2.2.2.1
  have hN : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hw : 0 < (n:ℝ) ^ 2 - 1 := by nlinarith
  have hs : 0 < Real.sqrt ((n:ℝ) ^ 2 - 1) := Real.sqrt_pos.2 hw
  set c := ((n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1)) ^ (n - 1) * ((n:ℝ) / ((n:ℝ) + 1)) with hcdef
  have hc : 0 < c := mul_pos (pow_pos (div_pos (by linarith) hs) _) (div_pos (by linarith) (by linarith))
  obtain ⟨h0, hle⟩ := g69el_inv hn hsep O R r ε hR t s hrun
  obtain ⟨a, ha, hB⟩ := g69el_step hsep O R s s' hstep
  have hdet : |s'.B.det| ≤ Real.exp (-((t : ℝ) + 1) / (2 * (n : ℝ))) * R ^ n := by
    rw [hB, g69el_det_next hn _ h0 a ha, abs_mul, abs_of_pos hc]
    have hcb : c ≤ Real.exp (-1 / (2 * (n:ℝ))) := g69el_bound n hn
    have h1 : c ^ (t + 1) ≤ Real.exp (-1 / (2 * (n:ℝ))) ^ (t + 1) := pow_le_pow_left₀ hc.le hcb _
    have h2 : Real.exp (-1 / (2 * (n:ℝ))) ^ (t + 1) = Real.exp (-((t : ℝ) + 1) / (2 * (n : ℝ))) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    calc |s.B.det| * c ≤ (c ^ t * R ^ n) * c := mul_le_mul_of_nonneg_right hle hc.le
      _ = c ^ (t + 1) * R ^ n := by ring
      _ ≤ Real.exp (-1 / (2 * (n:ℝ))) ^ (t + 1) * R ^ n :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg hR.le _)
      _ = _ := by rw [h2]
  unfold radius
  calc |s'.B.det| ^ ((1:ℝ) / n) ≤ (Real.exp (-((t : ℝ) + 1) / (2 * (n : ℝ))) * R ^ n) ^ ((1:ℝ) / n) :=
        Real.rpow_le_rpow (abs_nonneg _) hdet (by positivity)
    _ = Real.exp (-((t : ℝ) + 1) / (2 * (n : ℝ))) ^ ((1:ℝ) / n) * (R ^ n) ^ ((1:ℝ) / n) :=
        Real.mul_rpow (Real.exp_pos _).le (pow_nonneg hR.le _)
    _ = Real.exp (-((t : ℝ) + 1) / (2 * (n : ℝ) ^ 2)) * R := by
        rw [← Real.exp_mul, one_div, Real.pow_rpow_inv_natCast hR.le (by omega)]
        congr 1; congr 1; field_simp



theorem g69a2_ell_le {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ)) (r R : ℝ) (hP : IsBlackBoxProgram f X r R)
    (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (hO : IsFirstOrderOracle f O)
    (Vmax Vmin : ℝ) (hVmax : IsGreatest (f '' {x | eucNorm x ≤ R}) Vmax)
    (hVmin : IsLeast (f '' {x | eucNorm x ≤ R}) Vmin) (c : Fin n → ℝ) (hc : c ∈ X)
    (ha : (O c).2 ≠ 0) :
    R * eucNorm (O c).2 - (O c).2 ⬝ᵥ c ≤ Vmax - Vmin := by
  obtain ⟨-, -, -, -, -, -, hR, hXR, -⟩ := hP
  set a := (O c).2
  have haa : 0 < a ⬝ᵥ a := by
    rcases (dotProduct_self_eq_zero (v := a)).not.mpr ha |> lt_or_gt_of_ne with h | h
    · exact absurd h (not_lt.mpr (dotProduct_self_star_nonneg a))
    · exact h
  have hN : 0 < eucNorm a := Real.sqrt_pos.mpr haa
  have hNsq : eucNorm a ^ 2 = a ⬝ᵥ a := Real.sq_sqrt haa.le
  set y := (R / eucNorm a) • a
  have hy : eucNorm y ≤ R := by
    unfold eucNorm
    rw [show y ⬝ᵥ y = R ^ 2 by
      simp only [y, smul_dotProduct, dotProduct_smul, smul_eq_mul, ← hNsq]
      field_simp]
    rw [Real.sqrt_sq hR.le]
  have hsub := (hO c).2 y
  have h1 : f y ≤ Vmax := hVmax.2 ⟨y, hy, rfl⟩
  have h2 : Vmin ≤ f c := hVmin.2 ⟨c, hXR hc, rfl⟩
  have hay : a ⬝ᵥ y = R * eucNorm a := by
    simp only [y, dotProduct_smul, smul_eq_mul, ← hNsq]
    field_simp
  rw [dotProduct_sub, hay] at hsub
  linarith

theorem g69a2_step_L {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ)) (r R : ℝ) (hP : IsBlackBoxProgram f X r R)
    (sep : (Fin n → ℝ) → Option (Fin n → ℝ)) (hsep : IsSeparationOracle X sep)
    (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (hO : IsFirstOrderOracle f O)
    (Vmax Vmin : ℝ) (hVmax : IsGreatest (f '' {x | eucNorm x ≤ R}) Vmax)
    (hVmin : IsLeast (f '' {x | eucNorm x ≤ R}) Vmin) (s s' : State n)
    (hs : s.L ≤ Vmax - Vmin) (hstep : step sep O R s = StepResult.next s') :
    s'.L ≤ Vmax - Vmin := by
  unfold step at hstep
  rcases hc : sep s.c with _ | a
  · rw [hc] at hstep
    simp only at hstep
    by_cases h0 : (O s.c).2 = 0
    · rw [if_pos h0] at hstep; cases hstep
    · rw [if_neg h0] at hstep
      cases hstep
      simp only
      refine max_le hs ?_
      exact g69a2_ell_le f X r R hP O hO Vmax Vmin hVmax hVmin s.c ((hsep s.c).1.mp hc) h0
  · rw [hc] at hstep
    simp only at hstep
    cases hstep
    exact hs

theorem g69a2_run_L {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ)) (r R : ℝ) (hP : IsBlackBoxProgram f X r R)
    (sep : (Fin n → ℝ) → Option (Fin n → ℝ)) (hsep : IsSeparationOracle X sep)
    (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (hO : IsFirstOrderOracle f O) (ε : ℝ)
    (Vmax Vmin : ℝ) (hVmax : IsGreatest (f '' {x | eucNorm x ≤ R}) Vmax)
    (hVmin : IsLeast (f '' {x | eucNorm x ≤ R}) Vmin) :
    ∀ (t : ℕ) (s : State n), run sep O R r ε t = Outcome.running s → s.L ≤ Vmax - Vmin := by
  intro t
  induction t with
  | zero =>
    intro s hs
    simp only [run] at hs
    cases hs
    simp only [initState]
    obtain ⟨x, hx, hxv⟩ := hVmin.1
    have := hVmax.2 ⟨x, hx, rfl⟩
    linarith
  | succ t ih =>
    intro s hs
    simp only [run] at hs
    rcases h : run sep O R r ε t with s0 | x
    · rw [h] at hs
      simp only at hs
      rcases hst : step sep O R s0 with x | s'
      · rw [hst] at hs; simp only at hs; cases hs
      · rw [hst] at hs
        simp only at hs
        split_ifs at hs
        cases hs
        exact g69a2_step_L f X r R hP sep hsep O hO Vmax Vmin hVmax hVmin s0 _ (ih s0 h) hst
    · rw [h] at hs; simp only at hs; cases hs


/-- Ben-Tal–Nemirovski, p. 352, Eq. (5.2.28), in the proof of Theorem 5.2.1. In the setting of
Theorem 5.2.1, let `Var_R(f) = max_{E₀} f − min_{E₀} f` over the ball `E₀ = {‖x‖₂ ≤ R}`
(the maximum `Vmax` and minimum `Vmin` of `f` on `E₀`). Every guess `L_{t+1}` computed at a
step `t + 1` of the method (the method still running after `t` steps, step `t + 1` not stopping
by rule 2) satisfies `L_{t+1} ≤ Var_R(f)` (and `L₀ = 0`). -/
theorem g70mc1_Lb {n : ℕ} (hn : 2 ≤ n)
    (f : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ)) (r R : ℝ) (hP : IsBlackBoxProgram f X r R)
    (sep : (Fin n → ℝ) → Option (Fin n → ℝ)) (hsep : IsSeparationOracle X sep)
    (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (hO : IsFirstOrderOracle f O)
    (ε : ℝ) (hε : 0 < ε)
    (Vmax Vmin : ℝ) (hVmax : IsGreatest (f '' {x | eucNorm x ≤ R}) Vmax)
    (hVmin : IsLeast (f '' {x | eucNorm x ≤ R}) Vmin)
    (t : ℕ) (s s' : State n) (hrun : run sep O R r ε t = Outcome.running s)
    (hstep : step sep O R s = StepResult.next s') :
    s'.L ≤ Vmax - Vmin := g69a2_step_L f X r R hP sep hsep O hO Vmax Vmin hVmax hVmin s s'
    (g69a2_run_L f X r R hP sep hsep O hO ε Vmax Vmin hVmax hVmin t s hrun) hstep


lemma g70mc1_run_succ {n : ℕ} (sep : (Fin n → ℝ) → Option (Fin n → ℝ))
    (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (R r ε : ℝ) (t : ℕ) (s : State n)
    (h : run sep O R r ε (t + 1) = Outcome.running s) :
    ∃ s0, run sep O R r ε t = Outcome.running s0 ∧ step sep O R s0 = StepResult.next s ∧
      ¬ (radius s.B / r < ε / (s.L + ε)) := by
  simp only [run] at h
  rcases hr : run sep O R r ε t with s0 | x
  · rw [hr] at h
    simp only at h
    rcases hst : step sep O R s0 with x | s'
    · rw [hst] at h; simp only at h; cases h
    · rw [hst] at h
      simp only at h
      split_ifs at h with hc
      cases h
      exact ⟨s0, rfl, hst, hc⟩
  · rw [hr] at h; simp only at h; cases h

lemma g70mc1_rR {n : ℕ} (hn : 2 ≤ n) {f : (Fin n → ℝ) → ℝ} {X : Set (Fin n → ℝ)} {r R : ℝ}
    (hP : IsBlackBoxProgram f X r R) : r ≤ R := by
  obtain ⟨_, _, _, _, _, hr, hR, hXR, xbar, hball⟩ := hP
  set i0 : Fin n := ⟨0, by omega⟩
  set σ : ℝ := if 0 ≤ xbar i0 then 1 else -1
  have hσ2 : σ ^ 2 = 1 := by simp only [σ]; split_ifs <;> norm_num
  have hσx : 0 ≤ σ * xbar i0 := by simp only [σ]; split_ifs with h <;> nlinarith
  set p := xbar + (σ * r) • (Pi.single i0 1 : Fin n → ℝ)
  have hp : p ∈ X := by
    apply hball
    show eucNorm (p - xbar) ≤ r
    have e : p - xbar = (σ * r) • (Pi.single i0 1 : Fin n → ℝ) := by simp [p]
    rw [e]; unfold eucNorm
    rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    simp only [dotProduct_single, Pi.single_eq_same, mul_one]
    rw [show σ * r * (σ * r) = r ^ 2 by nlinarith [hσ2], Real.sqrt_sq hr.le]
  have hpR : eucNorm p ≤ R := hXR hp
  have hpp : p ⬝ᵥ p ≤ R ^ 2 := by
    unfold eucNorm at hpR
    have h0 : 0 ≤ p ⬝ᵥ p := Finset.sum_nonneg fun i _ => mul_self_nonneg (p i)
    rw [← Real.sq_sqrt h0]; exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hpR 2
  have hsingle : p i0 * p i0 ≤ p ⬝ᵥ p :=
    Finset.single_le_sum (f := fun j => p j * p j) (fun j _ => mul_self_nonneg _) (Finset.mem_univ i0)
  have hpi : p i0 = xbar i0 + σ * r := by simp [p]
  rw [hpi] at hsingle
  have e : (xbar i0 + σ * r) * (xbar i0 + σ * r) =
      xbar i0 ^ 2 + 2 * r * (σ * xbar i0) + σ ^ 2 * r ^ 2 := by ring
  rw [e, hσ2] at hsingle
  have : r ^ 2 ≤ R ^ 2 := by nlinarith [mul_nonneg hr.le hσx, sq_nonneg (xbar i0)]
  nlinarith

theorem g70mc1_complexity {n : ℕ} (hn : 2 ≤ n)
    (f : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ)) (r R : ℝ) (hP : IsBlackBoxProgram f X r R)
    (sep : (Fin n → ℝ) → Option (Fin n → ℝ)) (hsep : IsSeparationOracle X sep)
    (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (hO : IsFirstOrderOracle f O)
    (ε : ℝ) (hε : 0 < ε)
    (Vmax Vmin : ℝ) (hVmax : IsGreatest (f '' {x | eucNorm x ≤ R}) Vmax)
    (hVmin : IsLeast (f '' {x | eucNorm x ≤ R}) Vmin) :
    ∃ (t : ℕ) (xhat : Fin n → ℝ),
      (t : ℤ) ≤ ⌈2 * (n : ℝ) ^ 2 *
          (Real.log (R / r) + Real.log ((ε + (Vmax - Vmin)) / ε))⌉ + 1 ∧
      TerminatesAt sep O R r ε t (some xhat) ∧
      xhat ∈ X ∧ ∀ y ∈ X, f xhat - f y ≤ ε := by
  classical
  have hr : 0 < r := hP.2.2.2.2.2.1
  have hR : 0 < R := hP.2.2.2.2.2.2.1
  have hXR : X ⊆ {x | eucNorm x ≤ R} := hP.2.2.2.2.2.2.2.1
  have hrR := g70mc1_rR hn hP
  set V := Vmax - Vmin
  have hV : 0 ≤ V := by
    obtain ⟨x0, hx0, hfx⟩ := hVmax.1
    have := hVmin.2 ⟨x0, hx0, hfx⟩; simp only [V]; linarith
  set x := 2 * (n : ℝ) ^ 2 * (Real.log (R / r) + Real.log ((ε + V) / ε)) with hxdef
  have hn2 : (0:ℝ) < 2 * (n:ℝ) ^ 2 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have hx0 : 0 ≤ x := by
    have h1 : 0 ≤ Real.log (R / r) := Real.log_nonneg (by rw [le_div_iff₀ hr]; linarith)
    have h2 : 0 ≤ Real.log ((ε + V) / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
    positivity
  -- every running step t+1 satisfies t+1 ≤ x
  have hbound : ∀ (t : ℕ) (s : State n), run sep O R r ε (t + 1) = Outcome.running s →
      ((t : ℝ) + 1) ≤ x := by
    intro t s h
    obtain ⟨s0, hr0, hst, hc⟩ := g70mc1_run_succ sep O R r ε t s h
    have hrad := g70mc1_rad hn f X r R hP sep hsep O hO ε hε t s0 s hr0 hst
    have hL := g70mc1_Lb hn f X r R hP sep hsep O hO ε hε Vmax Vmin hVmax hVmin t s0 s hr0 hst
    have hL0 : 0 ≤ s.L :=
      (g70mc1_step_inv hn hsep hO R s0 s (g70mc1_run_inv hn hsep hO R r ε hR hXR t s0 hr0) hst).2.1
    push Not at hc
    have h1 : ε / (V + ε) ≤ ε / (s.L + ε) :=
      div_le_div_of_nonneg_left hε.le (by linarith) (by linarith)
    have h2 : radius s.B / r ≤ Real.exp (-((t : ℝ) + 1) / (2 * (n : ℝ) ^ 2)) * (R / r) := by
      rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hrad hr.le
    have h3 := (h1.trans hc).trans h2
    have hpos : 0 < ε / (V + ε) := div_pos hε (by linarith)
    have hl := Real.log_le_log hpos h3
    rw [Real.log_mul (Real.exp_pos _).ne' (div_pos hR hr).ne', Real.log_exp] at hl
    have hinv : Real.log ((ε + V) / ε) = -Real.log (ε / (V + ε)) := by
      rw [← Real.log_inv, inv_div, add_comm]
    rw [hxdef, hinv]
    have : ((t : ℝ) + 1) / (2 * (n : ℝ) ^ 2) ≤ Real.log (R / r) - Real.log (ε / (V + ε)) := by
      rw [neg_div] at hl; linarith
    rw [div_le_iff₀ hn2] at this
    linarith
  have hstop : ∃ t, ∃ res, run sep O R r ε t = Outcome.stopped res := by
    refine ⟨⌊x⌋₊ + 1, ?_⟩
    rcases h : run sep O R r ε (⌊x⌋₊ + 1) with s | res
    · have := hbound _ s h
      have := Nat.lt_floor_add_one x
      push_cast at *
      linarith
    · exact ⟨res, rfl⟩
  set T := Nat.find hstop with hT
  obtain ⟨res, hres⟩ := Nat.find_spec hstop
  have hT0 : T ≠ 0 := by
    intro h0
    rw [← hT, h0] at hres
    simp [run] at hres
  have hprev : ∃ s, run sep O R r ε (T - 1) = Outcome.running s := by
    have := Nat.find_min hstop (show T - 1 < T by omega)
    rcases h : run sep O R r ε (T - 1) with s | res'
    · exact ⟨s, rfl⟩
    · exact absurd ⟨res', h⟩ this
  have hterm : TerminatesAt sep O R r ε T res := ⟨by omega, hprev, hres⟩
  obtain ⟨xhat, hx, hxX, hopt⟩ :=
    g70mc1_term hn f X r R hP sep hsep O hO ε hε T res hterm
  subst hx
  refine ⟨T, xhat, ?_, hterm, hxX, hopt⟩
  have hTx : ((T : ℝ) - 1) ≤ x := by
    rcases Nat.lt_or_ge T 2 with h2 | h2
    · have : T = 1 := by omega
      rw [this]; simp; exact hx0
    · obtain ⟨s, hs⟩ := hprev
      have e : T - 1 = (T - 2) + 1 := by omega
      rw [e] at hs
      have := hbound _ s hs
      have e2 : ((T - 2 : ℕ) : ℝ) = (T : ℝ) - 2 := by rw [Nat.cast_sub h2]; simp
      rw [e2] at this; linarith
  have hc := (hTx.trans (Int.le_ceil x))
  have : ((T : ℤ) : ℝ) - 1 ≤ (⌈x⌉ : ℝ) := by exact_mod_cast hc
  have h' : (T : ℤ) - 1 ≤ ⌈x⌉ := by exact_mod_cast this
  linarith

theorem solution {n : ℕ} (hn : 2 ≤ n)
    (f : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ)) (r R : ℝ) (hP : IsBlackBoxProgram f X r R)
    (sep : (Fin n → ℝ) → Option (Fin n → ℝ)) (hsep : IsSeparationOracle X sep)
    (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (hO : IsFirstOrderOracle f O)
    (ε : ℝ) (hε : 0 < ε)
    (Vmax Vmin : ℝ) (hVmax : IsGreatest (f '' {x | eucNorm x ≤ R}) Vmax)
    (hVmin : IsLeast (f '' {x | eucNorm x ≤ R}) Vmin) :
    ∃ (t : ℕ) (xhat : Fin n → ℝ),
      (t : ℤ) ≤ ⌈2 * (n : ℝ) ^ 2 *
          (Real.log (R / r) + Real.log ((ε + (Vmax - Vmin)) / ε))⌉ + 1 ∧
      TerminatesAt sep O R r ε t (some xhat) ∧
      xhat ∈ X ∧ ∀ y ∈ X, f xhat - f y ≤ ε := by
  exact g70mc1_complexity hn f X r R hP sep hsep O hO ε hε Vmax Vmin hVmax hVmin

