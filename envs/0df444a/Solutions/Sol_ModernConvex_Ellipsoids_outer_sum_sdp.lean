-- Prove2me | solution 1 for ModernConvex.Ellipsoids.outer_sum_sdp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:01:33.792005+00:00
-- url     : https://prove2.me/submissions/928bb95d-b8e0-46c4-a513-4ff51447969f

import Mathlib
import Definitions.Def_ModernConvex_Ellipsoids_Ellipsoid
import Definitions.Def_ModernConvex_Ellipsoids_Programs

open Matrix

open ModernConvex.Ellipsoids

theorem g70mc2_blockSel_quad {m n : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ) (i : Fin m)
    (w : Fin m × Fin n → ℝ) :
    w ⬝ᵥ (blockSel B i *ᵥ w) = (fun a => w (i, a)) ⬝ᵥ (B i *ᵥ fun a => w (i, a)) := by
  simp only [dotProduct, mulVec, blockSel, of_apply, Fintype.sum_prod_type]
  simp [ite_and, Finset.mul_sum]

theorem g70mc2_blockAll_mulVec {m n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ)
    (w : Fin m × Fin n → ℝ) :
    blockAll Z *ᵥ w = fun r => (Z *ᵥ ∑ i, fun a => w (i, a)) r.2 := by
  ext r
  simp only [mulVec, dotProduct, blockAll, of_apply, Fintype.sum_prod_type, Finset.sum_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]

theorem g70mc2_blockAll_quad {m n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ)
    (w : Fin m × Fin n → ℝ) :
    w ⬝ᵥ (blockAll Z *ᵥ w) = (∑ i, fun a => w (i, a)) ⬝ᵥ (Z *ᵥ ∑ i, fun a => w (i, a)) := by
  rw [g70mc2_blockAll_mulVec]
  simp only [dotProduct, Fintype.sum_prod_type, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]


open scoped MatrixOrder in
theorem g70mc2_factor {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Z.PosSemidef) :
    ∃ M : Matrix (Fin n) (Fin n) ℝ, Z = Mᵀ * M := by
  obtain ⟨y, hy⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hZ.nonneg
  exact ⟨y, by rw [hy]; rfl⟩

theorem g70mc2_ball_meas {n : ℕ} :
    MeasureTheory.volume (unitBall n) ≠ 0 ∧ MeasureTheory.volume (unitBall n) ≠ ⊤ := by
  constructor
  · have hopen : IsOpen {u : Fin n → ℝ | u ⬝ᵥ u < 1} :=
      isOpen_lt (by fun_prop) continuous_const
    have hne : ({u : Fin n → ℝ | u ⬝ᵥ u < 1}).Nonempty := ⟨0, by simp⟩
    intro h
    have := hopen.measure_ne_zero MeasureTheory.volume hne
    apply this
    exact MeasureTheory.measure_mono_null (fun u (hu : u ⬝ᵥ u < 1) => (le_of_lt hu : u ⬝ᵥ u ≤ 1)) h
  · apply ne_of_lt
    refine lt_of_le_of_lt (MeasureTheory.measure_mono (t := Metric.closedBall 0 1) ?_)
      MeasureTheory.measure_closedBall_lt_top
    intro u (hu : u ⬝ᵥ u ≤ 1)
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs, ← abs_one, ← sq_le_sq]
    have : u i ^ 2 ≤ u ⬝ᵥ u := by
      unfold dotProduct
      rw [sq]
      exact Finset.single_le_sum (f := fun j => u j * u j) (fun j _ => mul_self_nonneg (u j))
        (Finset.mem_univ i)
    linarith

theorem g70mc2_vol_quad {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Z.PosDef) :
    Vol (quadSet Z) = ENNReal.ofReal (Z.det ^ (-(1:ℝ)/2)) := by
  obtain ⟨M, rfl⟩ := g70mc2_factor _ hZ.posSemidef
  have hdet : (Mᵀ * M).det = M.det ^ 2 := by rw [det_mul, det_transpose]; ring
  have hM : M.det ≠ 0 := by
    intro h; have := hZ.det_pos; rw [hdet, h] at this; simp at this
  have hU : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have himg : quadSet (Mᵀ * M) = Matrix.toLin' M⁻¹ '' unitBall n := by
    ext x
    simp only [quadSet, unitBall, Set.mem_setOf_eq, Set.mem_image, Matrix.toLin'_apply]
    constructor
    · intro hx
      refine ⟨M *ᵥ x, ?_, ?_⟩
      · rw [← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose] at hx
        simpa using hx
      · rw [mulVec_mulVec, nonsing_inv_mul _ hU, one_mulVec]
    · rintro ⟨u, hu, rfl⟩
      have hMu : M *ᵥ (M⁻¹ *ᵥ u) = u := by rw [mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]
      rw [← mulVec_mulVec, hMu, dotProduct_mulVec, ← mulVec_transpose, transpose_transpose,
        hMu]
      simpa using hu
  obtain ⟨h0, htop⟩ := g70mc2_ball_meas (n := n)
  unfold Vol
  rw [himg, MeasureTheory.Measure.addHaar_image_linearMap, LinearMap.det_toLin',
    ENNReal.mul_div_cancel_right h0 htop, hdet, det_nonsing_inv,
    Ring.inverse_eq_inv']
  congr 1
  rw [abs_inv, ← Real.sqrt_sq_eq_abs, Real.sqrt_eq_rpow, ← Real.rpow_neg_one,
    ← Real.rpow_mul (sq_nonneg _)]
  norm_num

theorem g70mc2_pow_le {n : ℕ} (hn : n ≠ 0) (a d : ℝ) (ha : 0 < a) (hd : 0 ≤ d)
    (h : a ≤ d ^ ((1 : ℝ) / n)) : a ^ (n : ℝ) ≤ d := by
  have := Real.rpow_le_rpow ha.le h (Nat.cast_nonneg n)
  rwa [← Real.rpow_mul hd, one_div_mul_cancel (by exact_mod_cast hn), Real.rpow_one] at this

theorem g70mc2_det_le {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Z.PosSemidef) (t : ℝ)
    (ht : 0 < t) (h : t ≤ Z.det ^ ((1 : ℝ) / n)) :
    Z.PosDef ∧ Z.det ^ (-(1:ℝ)/2) ≤ t ^ (-(n : ℝ) / 2) := by
  by_cases hn : n = 0
  · subst hn
    refine ⟨hZ.posDef_iff_det_ne_zero.mpr (by simp), ?_⟩
    simp
  · have hd := hZ.det_nonneg
    have h1 := g70mc2_pow_le hn t Z.det ht hd h
    have hpos : 0 < Z.det := lt_of_lt_of_le (Real.rpow_pos_of_pos ht _) h1
    refine ⟨hZ.posDef_iff_det_ne_zero.mpr hpos.ne', ?_⟩
    calc Z.det ^ (-(1:ℝ)/2) ≤ (t ^ (n : ℝ)) ^ (-(1:ℝ)/2) :=
          Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos ht _) h1 (by norm_num)
      _ = t ^ (-(n : ℝ) / 2) := by rw [← Real.rpow_mul ht.le]; ring_nf

theorem solution {m n : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ i, (B i).PosDef) :
    (∀ (t : ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) (lam : Fin m → ℝ), OFeasible B t Z lam → 0 < t →
      Z.PosDef ∧ minkowskiSum (fun i => quadSet (B i)) ⊆ quadSet Z ∧
        Vol (quadSet Z) ≤ ENNReal.ofReal (t ^ (-(n : ℝ) / 2))) ∧
    (∀ (t : ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) (lam : Fin m → ℝ), OOptimal B t Z lam →
      ∀ (t' : ℝ) (Z' : Matrix (Fin n) (Fin n) ℝ) (lam' : Fin m → ℝ), OFeasible B t' Z' lam' →
        0 < t' → Vol (quadSet Z) ≤ Vol (quadSet Z')) := by
  constructor
  · intro t Z lam hF ht
    obtain ⟨htZ, hPSD, hlam, hZ, hsum⟩ := hF
    obtain ⟨hZpd, hdet⟩ := g70mc2_det_le Z hZ t ht htZ
    refine ⟨hZpd, ?_, ?_⟩
    · rintro x ⟨w, hw, rfl⟩
      set W : Fin m × Fin n → ℝ := fun r => w r.1 r.2
      have h0 := hPSD.dotProduct_mulVec_nonneg W
      simp only [star_trivial] at h0
      rw [sub_mulVec, dotProduct_sub, Matrix.sum_mulVec, dotProduct_sum, g70mc2_blockAll_quad]
        at h0
      simp only [smul_mulVec, dotProduct_smul, g70mc2_blockSel_quad, smul_eq_mul] at h0
      have hW : (∑ i, fun a => W (i, a)) = ∑ i, w i := rfl
      rw [hW] at h0
      show (∑ i, w i) ⬝ᵥ (Z *ᵥ ∑ i, w i) ≤ 1
      have : ∑ i, lam i * (w i ⬝ᵥ (B i *ᵥ w i)) ≤ ∑ i, lam i := by
        apply Finset.sum_le_sum
        intro i _
        have := hw i
        simp only [quadSet, Set.mem_setOf_eq] at this
        nlinarith [hlam i]
      have h2 : ∑ i, lam i * ((fun a => W (i, a)) ⬝ᵥ (B i *ᵥ fun a => W (i, a))) =
          ∑ i, lam i * (w i ⬝ᵥ (B i *ᵥ w i)) := rfl
      linarith
    · rw [g70mc2_vol_quad Z hZpd]
      exact ENNReal.ofReal_le_ofReal hdet
  · intro t Z lam hO t' Z' lam' hF' ht'
    obtain ⟨htZ', hPSD', hlam', hZ', hsum'⟩ := hF'
    have hfeas : OFeasible B (Z'.det ^ ((1 : ℝ) / n)) Z' lam' :=
      ⟨le_refl _, hPSD', hlam', hZ', hsum'⟩
    have hle := hO.2 _ _ _ hfeas
    obtain ⟨htZ, -, -, hZ, -⟩ := hO.1
    have ht : 0 < t := lt_of_lt_of_le ht' (htZ'.trans hle)
    obtain ⟨hZpd, -⟩ := g70mc2_det_le Z hZ t ht htZ
    obtain ⟨hZpd', -⟩ := g70mc2_det_le Z' hZ' t' ht' htZ'
    rw [g70mc2_vol_quad Z hZpd, g70mc2_vol_quad Z' hZpd']
    apply ENNReal.ofReal_le_ofReal
    have hdd : Z'.det ≤ Z.det := by
      by_cases hn : n = 0
      · subst hn; simp
      · have h3 := hle.trans htZ
        have hn' : (0:ℝ) < 1 / n := by positivity
        exact (Real.rpow_le_rpow_iff hZ'.det_nonneg hZ.det_nonneg hn').mp h3
    exact Real.rpow_le_rpow_of_nonpos hZpd'.det_pos hdd (by norm_num)
