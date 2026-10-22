-- Prove2me | solution 1 for ModernConvex.EllipsoidMethod.termination_gives_solution
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:02:05.971914+00:00
-- url     : https://prove2.me/submissions/79e895bd-042c-4a80-8f6e-000912c4a720

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

theorem solution {n : ℕ} (hn : 2 ≤ n)
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
