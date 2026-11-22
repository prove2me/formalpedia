-- Prove2me | solution 1 for NoHair.reissnerNordstrom_charge_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T20:39:05.014721+00:00
-- url     : https://prove2.me/submissions/f8c62ec4-e576-4bf9-aa5b-a5897df2f835

import Definitions.Def_NoHair_KerrNewmanEinstein_Atoms
import Definitions.Def_NoHair_KerrNewmanEinstein_MaxwellF

open NoHair NoHair.KNE
open scoped BigOperators

private lemma rnField (e : ℝ) (y : E4) (hy : 0 < ksRadius 0 y) (i j : Fin 4) :
    kerrNewmanField 0 e y i j =
      FA 0 e (ksRadius 0 y) (ksNull 0 y 1) (ksNull 0 y 2) (ksNull 0 y 3) (Wf 0 y) i j := by
  have hA : ∀ k, HasCP (fun z => kerrNewmanPotential 0 e z k) y
      (fun l => dHA 0 e (ksRadius 0 y) (ksNull 0 y 1) (ksNull 0 y 2) (ksNull 0 y 3)
          (Wf 0 y) l * ksNull 0 y k
        + e * ksRadius 0 y ^ 3 / (ksRadius 0 y ^ 4 + (0 : ℝ) ^ 2 * y 3 ^ 2)
          * dKt 0 (ksRadius 0 y) (ksNull 0 y 1) (ksNull 0 y 2) (ksNull 0 y 3)
            (Wf 0 y) k l) :=
    fun k => (hasCP_H 0 e y hy).mul (hasCP_K 0 y hy k)
  have hpot : e * ksRadius 0 y ^ 3 / (ksRadius 0 y ^ 4 + (0 : ℝ) ^ 2 * y 3 ^ 2) =
      HA 0 e (ksRadius 0 y) (Wf 0 y) := by
    simp [HA, Wf] <;> field_simp [hy.ne'] <;> ring
  unfold kerrNewmanField
  rw [(hA j).eq i, (hA i).eq j, hpot,
    ← fS 0 e _ _ _ _ _ (ks_rel 0 y hy) (ks_W 0 y hy) i j]
  simp only [FS, Kv, ← ksNull_eq_Kv 0 y]

private lemma rnRaisedField (m e : ℝ) (y : E4) (hy : 0 < ksRadius 0 y) (i j : Fin 4) :
    raiseBoth (kerrNewmanMetric m 0 e) (kerrNewmanField 0 e) y i j =
      FupA 0 m e (ksRadius 0 y) (ksNull 0 y 1) (ksNull 0 y 2) (ksNull 0 y 3)
        (Wf 0 y) i j := by
  unfold raiseBoth
  simp only [invMetric_eq m 0 e y hy, Matrix.of_apply, rnField e y hy]
  exact fU 0 m e _ _ _ _ _ (ks_rel 0 y hy) (ks_W 0 y hy) i j

private lemma leviCivita_perm (p : Equiv.Perm (Fin 4)) :
    leviCivita (p 0) (p 1) (p 2) (p 3) = ((Equiv.Perm.sign p : ℤ) : ℝ) := by
  have hf : ![p 0, p 1, p 2, p 3] = (p : Fin 4 → Fin 4) := by
    funext i
    fin_cases i <;> rfl
  have hp : Equiv.ofBijective (p : Fin 4 → Fin 4) p.bijective = p := by
    ext i
    rfl
  simp [leviCivita, hf, p.bijective, hp]

private lemma axisOrientation :
    leviCivita 0 3 0 3 = 0 ∧ leviCivita 0 3 3 0 = 0 ∧
    leviCivita 1 2 0 3 = 1 ∧ leviCivita 1 2 3 0 = -1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold leviCivita
    apply dif_neg
    intro h
    apply (by decide : (0 : Fin 4) ≠ 2)
    exact h.1 (show (![0,3,0,3] : Fin 4 → Fin 4) 0 = ![0,3,0,3] 2 from rfl)
  · unfold leviCivita
    apply dif_neg
    intro h
    apply (by decide : (0 : Fin 4) ≠ 3)
    exact h.1 (show (![0,3,3,0] : Fin 4 → Fin 4) 0 = ![0,3,3,0] 3 from rfl)
  · let p : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2
    have heps : leviCivita 1 2 0 3 = ((Equiv.Perm.sign p : ℤ) : ℝ) := leviCivita_perm p
    simpa [p] using heps
  · let p : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3
    have heps : leviCivita 1 2 3 0 = ((Equiv.Perm.sign p : ℤ) : ℝ) := leviCivita_perm p
    simpa [p] using heps

theorem solution (m e β : ℝ) (hp : IsKerrNewmanBlackHoleParams m 0 e)
    (hzero : ∀ y ∈ kerrNewmanDOC m 0 e,
      Real.cos β • kerrNewmanField 0 e y +
        Real.sin β • hodgeDual (kerrNewmanMetric m 0 e y) (kerrNewmanField 0 e y) = 0) :
    e = 0 := by
  let R := kerrNewmanOuterRadius m 0 e + 1
  have hplus : 0 < kerrNewmanOuterRadius m 0 e :=
    add_pos_of_pos_of_nonneg hp.1 (Real.sqrt_nonneg _)
  have hR : 0 < R := by dsimp only [R]; linarith
  let y : E4 := WithLp.toLp 2 ![0, 0, 0, R]
  have hx : y 1 = 0 := rfl
  have hy : y 2 = 0 := rfl
  have hz : y 3 = R := rfl
  have hr : ksRadius 0 y = R := by
    simp only [ksRadius, hx, hy, hz, zero_pow (by decide : 2 ≠ 0), zero_add, sub_zero,
      zero_mul, mul_zero, add_zero, Real.sqrt_sq (sq_nonneg R)]
    rw [show (R ^ 2 + R ^ 2) / 2 = R ^ 2 by ring, Real.sqrt_sq hR.le]
  have hpos : 0 < ksRadius 0 y := hr.symm ▸ hR
  have hmem : y ∈ kerrNewmanDOC m 0 e := by
    change kerrNewmanOuterRadius m 0 e < ksRadius 0 y
    rw [hr]
    dsimp only [R]
    linarith
  have hk1 : ksNull 0 y 1 = 0 := by simp [ksNull_one, hx, hy]
  have hk2 : ksNull 0 y 2 = 0 := by simp [ksNull_two, hx, hy]
  have hk3 : ksNull 0 y 3 = 1 := by rw [ksNull_three, hz, hr, div_self hR.ne']
  let W : ℝ := 1 / R ^ 2
  have hW : Wf 0 y = W := by simp [Wf, W, hr]
  let u := R ^ 4 * W ^ 3 * e
  let vol := Real.sqrt |(kerrNewmanMetric m 0 e y).det|
  have hfield (i j : Fin 4) :
      kerrNewmanField 0 e y i j = FA 0 e R 0 0 1 W i j := by
    simpa only [hr, hk1, hk2, hk3, hW] using rnField e y hpos i j
  have hraised (i j : Fin 4) :
      raiseBoth (kerrNewmanMetric m 0 e) (kerrNewmanField 0 e) y i j =
        FupA 0 m e R 0 0 1 W i j := by
    simpa only [hr, hk1, hk2, hk3, hW] using rnRaisedField m e y hpos i j
  have hdual (i j : Fin 4) :
      hodgeDual (kerrNewmanMetric m 0 e y) (kerrNewmanField 0 e y) i j =
        (1 / 2 : ℝ) * vol *
          (leviCivita i j 0 3 * (-u) + leviCivita i j 3 0 * u) := by
    change (1 / 2 : ℝ) * vol * (∑ k, ∑ l, leviCivita i j k l *
        raiseBoth (kerrNewmanMetric m 0 e) (kerrNewmanField 0 e) y k l) = _
    simp only [hraised, Fin.sum_univ_four]
    simp [FupA, Fu01, Fu02, Fu03, Fu12, Fu13, Fu23, u] <;> ring
  have helectric : kerrNewmanField 0 e y 0 3 = u := by
    rw [hfield]
    simp [FA, Fc03, u]
  have htransverse : kerrNewmanField 0 e y 1 2 = 0 := by
    rw [hfield]
    simp [FA, Fc12]
  obtain ⟨h0303, h0330, h1203, h1230⟩ := axisOrientation
  have hdual03 : hodgeDual (kerrNewmanMetric m 0 e y) (kerrNewmanField 0 e y) 0 3 = 0 := by
    rw [hdual, h0303, h0330]
    ring
  have hdual12 : hodgeDual (kerrNewmanMetric m 0 e y) (kerrNewmanField 0 e y) 1 2 =
      -vol * u := by
    rw [hdual, h1203, h1230]
    ring
  have hdet : (kerrNewmanMetric m 0 e y).det ≠ 0 :=
    Matrix.det_ne_zero_of_right_inverse (mul_inv_KS (ksProfile m 0 e y) _ (ks_null 0 y hpos))
  have hvol : vol ≠ 0 := (Real.sqrt_pos.2 (abs_pos.mpr hdet)).ne'
  have hcomponent (i j : Fin 4) :
      Real.cos β * kerrNewmanField 0 e y i j +
        Real.sin β * hodgeDual (kerrNewmanMetric m 0 e y) (kerrNewmanField 0 e y) i j = 0 :=
    congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A i j) (hzero y hmem)
  by_contra he
  have hWpos : 0 < W := by dsimp only [W]; positivity
  have hu : u ≠ 0 := mul_ne_zero (mul_ne_zero (pow_ne_zero 4 hR.ne')
    (pow_ne_zero 3 hWpos.ne')) he
  have hcos := hcomponent 0 3
  rw [helectric, hdual03, mul_zero, add_zero] at hcos
  have hc := (mul_eq_zero.mp hcos).resolve_right hu
  have hsin := hcomponent 1 2
  rw [htransverse, hdual12, mul_zero, zero_add] at hsin
  have hs := (mul_eq_zero.mp hsin).resolve_right (mul_ne_zero (neg_ne_zero.mpr hvol) hu)
  have hcircle := Real.sin_sq_add_cos_sq β
  norm_num [hs, hc] at hcircle
