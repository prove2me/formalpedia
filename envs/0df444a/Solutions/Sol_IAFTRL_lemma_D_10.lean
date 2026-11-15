-- Prove2me | solution 1 for IAFTRL.lemma_D_10
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T05:44:49.403761+00:00
-- url     : https://prove2.me/submissions/6b3a500b-e159-4df7-a743-c4c503eaa045

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsGOptLaw
import Definitions.Def_IAFTRL_IsFeasible2_3
import Theorems.Thm_IAFTRL_lemma_J_4

open Matrix Finset IAFTRL
set_option maxHeartbeats 1000000

namespace D10Proof

private lemma sym_bilin {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ)
    (hH : H.IsHermitian) (x y : Fin d → ℝ) :
    x ⬝ᵥ H *ᵥ y = y ⬝ᵥ H *ᵥ x := by
  have hs : Hᵀ = H := by simpa only [conjTranspose_eq_transpose_of_trivial] using hH.eq
  rw [dotProduct_mulVec, ← mulVec_transpose, hs, dotProduct_comm]

private lemma qnonneg {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ)
    (hH : H.PosSemidef) (x : Fin d → ℝ) : 0 ≤ x ⬝ᵥ H *ᵥ x := by
  simpa only [star_trivial] using hH.dotProduct_mulVec_nonneg x

private lemma qsub {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ)
    (hH : H.IsHermitian) (x y : Fin d → ℝ) :
    (x-y) ⬝ᵥ H *ᵥ (x-y) = x ⬝ᵥ H *ᵥ x - 2 * (x ⬝ᵥ H *ᵥ y) + y ⬝ᵥ H *ᵥ y := by
  simp only [mulVec_sub, sub_dotProduct, dotProduct_sub]
  rw [sym_bilin H hH y x]
  ring

private lemma qadd {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ)
    (hH : H.IsHermitian) (x y : Fin d → ℝ) :
    (x+y) ⬝ᵥ H *ᵥ (x+y) = x ⬝ᵥ H *ᵥ x + 2 * (x ⬝ᵥ H *ᵥ y) + y ⬝ᵥ H *ᵥ y := by
  simp only [mulVec_add, add_dotProduct, dotProduct_add]
  rw [sym_bilin H hH y x]
  ring

private lemma cross_bound {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ)
    (hH : H.PosSemidef) (x y : Fin d → ℝ) (c : ℝ)
    (hx : x ⬝ᵥ H *ᵥ x ≤ c) (hy : y ⬝ᵥ H *ᵥ y ≤ c) :
    |x ⬝ᵥ H *ᵥ y| ≤ c := by
  have hp := qnonneg H hH (x+y)
  have hm := qnonneg H hH (x-y)
  rw [qadd H hH.1] at hp
  rw [qsub H hH.1] at hm
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma inverse_le {d : ℕ} (M G : Matrix (Fin d) (Fin d) ℝ)
    (hM : M.PosDef) (hG : G.PosDef) (γ : ℝ) (hγ : 0 < γ)
    (hdom : ∀ y, γ * (y ⬝ᵥ G *ᵥ y) ≤ y ⬝ᵥ M *ᵥ y)
    (x : Fin d → ℝ) : γ * (x ⬝ᵥ M⁻¹ *ᵥ x) ≤ x ⬝ᵥ G⁻¹ *ᵥ x := by
  let y := M⁻¹ *ᵥ x
  let z := G⁻¹ *ᵥ x
  have hMy : M *ᵥ y = x := by
    dsimp [y]
    rw [mulVec_mulVec, mul_nonsing_inv M ((isUnit_iff_isUnit_det M).mp hM.isUnit), one_mulVec]
  have hGz : G *ᵥ z = x := by
    dsimp [z]
    rw [mulVec_mulVec, mul_nonsing_inv G ((isUnit_iff_isUnit_det G).mp hG.isUnit), one_mulVec]
  have hD := hdom y
  rw [hMy, dotProduct_comm y x] at hD
  have hn := qnonneg G hG.posSemidef (z - γ • y)
  rw [qsub G hG.1] at hn
  have hcross : z ⬝ᵥ G *ᵥ y = x ⬝ᵥ y := by
    rw [sym_bilin G hG.1, hGz, dotProduct_comm]
  simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, hcross, hGz] at hn
  change γ * (x ⬝ᵥ y) ≤ x ⬝ᵥ z
  have hmul := mul_le_mul_of_nonneg_left hD hγ.le
  rw [dotProduct_comm z x] at hn
  nlinarith

private lemma cov_bilin {d K : ℕ} (arms : Fin K → Fin d → ℝ) (p : Fin K → ℝ)
    (x y : Fin d → ℝ) :
    x ⬝ᵥ (∑ b, p b • vecMulVec (arms b) (arms b)) *ᵥ y =
      ∑ b, p b * (x ⬝ᵥ arms b) * (arms b ⬝ᵥ y) := by
  rw [sum_mulVec, dotProduct_sum]
  apply sum_congr rfl
  intro b _
  simp [smul_mulVec, vecMulVec_mulVec, dotProduct_smul, mul_comm, mul_left_comm]

private lemma cov_psd {d K : ℕ} (arms : Fin K → Fin d → ℝ)
    (p : Fin K → ℝ) (hp : ∀ b, 0 ≤ p b) :
    (∑ b, p b • vecMulVec (arms b) (arms b)).PosSemidef := by
  apply posSemidef_sum
  intro b _
  have h : (vecMulVec (arms b) (arms b)).PosSemidef := by
    simpa only [star_trivial] using posSemidef_vecMulVec_self_star (arms b)
  exact h.smul (hp b)

private lemma reconstruct {d K : ℕ} (arms : Fin K → Fin d → ℝ) (p : Fin K → ℝ)
    (hM : (∑ b, p b • vecMulVec (arms b) (arms b)).PosDef) :
    let M := ∑ b, p b • vecMulVec (arms b) (arms b)
    ∑ b, p b • vecMulVec (M⁻¹ *ᵥ arms b) (arms b) = 1 := by
  intro M
  simp_rw [← mul_vecMulVec, ← Matrix.mul_smul]
  rw [← Matrix.mul_sum]
  exact nonsing_inv_mul M ((isUnit_iff_isUnit_det M).mp hM.isUnit)

private lemma variance {d K : ℕ} (arms : Fin K → Fin d → ℝ) (p : Fin K → ℝ)
    (hM : (∑ b, p b • vecMulVec (arms b) (arms b)).PosDef) (x : Fin d → ℝ) :
    let M := ∑ b, p b • vecMulVec (arms b) (arms b)
    ∑ b, p b * (x ⬝ᵥ M⁻¹ *ᵥ arms b) ^ 2 = x ⬝ᵥ M⁻¹ *ᵥ x := by
  intro M
  have hMx : M *ᵥ (M⁻¹ *ᵥ x) = x := by
    rw [mulVec_mulVec, mul_nonsing_inv M ((isUnit_iff_isUnit_det M).mp hM.isUnit), one_mulVec]
  calc
    _ = (M⁻¹ *ᵥ x) ⬝ᵥ M *ᵥ (M⁻¹ *ᵥ x) := by
      rw [cov_bilin]
      apply sum_congr rfl
      intro b _
      rw [dotProduct_comm (M⁻¹ *ᵥ x) (arms b), sym_bilin M⁻¹ hM.inv.1 (arms b) x]
      ring
    _ = _ := by rw [hMx, dotProduct_comm]

private lemma leverage_sum {d K : ℕ} (arms : Fin K → Fin d → ℝ) (p : Fin K → ℝ)
    (hM : (∑ b, p b • vecMulVec (arms b) (arms b)).PosDef) :
    let M := ∑ b, p b • vecMulVec (arms b) (arms b)
    ∑ b, p b * (arms b ⬝ᵥ M⁻¹ *ᵥ arms b) = d := by
  have h := congrArg Matrix.trace (reconstruct arms p hM)
  simpa [trace_sum, trace_smul, trace_vecMulVec, dotProduct_comm] using h

private lemma centered_variance {d K : ℕ} (H : Matrix (Fin d) (Fin d) ℝ)
    (hH : H.IsHermitian) (arms : Fin K → Fin d → ℝ) (q : Fin K → ℝ)
    (hq : ∑ a, q a = 1) :
    let bar := ∑ a, q a • arms a
    ∑ a, q a * ((arms a - bar) ⬝ᵥ H *ᵥ (arms a - bar)) =
      (∑ a, q a * (arms a ⬝ᵥ H *ᵥ arms a)) - bar ⬝ᵥ H *ᵥ bar := by
  intro bar
  have hmean : ∑ a, q a * (arms a ⬝ᵥ H *ᵥ bar) = bar ⬝ᵥ H *ᵥ bar := by
    change _ = (∑ a, q a • arms a) ⬝ᵥ H *ᵥ bar
    rw [sum_dotProduct]
    simp only [smul_dotProduct, smul_eq_mul]
  have hpoint (a : Fin K) :
      q a * ((arms a - bar) ⬝ᵥ H *ᵥ (arms a - bar)) =
        q a * (arms a ⬝ᵥ H *ᵥ arms a) - 2 * (q a * (arms a ⬝ᵥ H *ᵥ bar)) +
          q a * (bar ⬝ᵥ H *ᵥ bar) := by
    rw [qsub H hH]; ring
  simp_rw [hpoint]
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul, hq, hmean]
  ring

private lemma weighted_scale {K : ℕ} (p q : Fin K → ℝ)
    (f : Fin K → Fin K → ℝ) (c : ℝ) :
    (∑ b, p b * ∑ a, q a * (c * f a b)) =
      c * ∑ b, p b * ∑ a, q a * f a b := by
  simp_rw [mul_sum]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro a _
  ring

private lemma q_prob {d K : ℕ} [Nonempty (Fin K)] (β : ℝ)
    (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) :
    (∀ a, 0 ≤ qSoft β arms S a) ∧ ∑ a, qSoft β arms S a = 1 := by
  have hp : 0 < ∑ a, Real.exp (-(arms a ⬝ᵥ S) / β) :=
    sum_pos (fun a _ => Real.exp_pos _) univ_nonempty
  constructor
  · intro a; exact div_nonneg (Real.exp_pos _).le hp.le
  · simp only [qSoft]
    rw [← sum_div, div_self (ne_of_gt hp)]

private lemma ref_spec {d K : ℕ} [Nonempty (Fin K)]
    (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) :
    ∃ j, refArm arms S = arms j ∧ ∀ a, 0 ≤ Zd arms S a := by
  classical
  let s := univ.filter fun j : Fin K => ∀ i, arms j ⬝ᵥ S ≤ arms i ⬝ᵥ S
  have hs : s.Nonempty := by
    obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image univ (fun j : Fin K => arms j ⬝ᵥ S) univ_nonempty
    exact ⟨j, mem_filter.mpr ⟨hj, fun i => hmin i (mem_univ i)⟩⟩
  have href : refArm arms S = arms (s.min' hs) := by
    unfold refArm
    rw [dif_pos hs]
  refine ⟨s.min' hs, href, ?_⟩
  intro a
  unfold Zd
  rw [href]
  exact sub_nonneg.mpr ((mem_filter.mp (s.min'_mem hs)).2 a)

private lemma schedules {d K t : ℕ} (hd : 1 ≤ d) (hK : 1 ≤ K) (ht : 1 ≤ t) :
    0 < beta d K t ∧ 0 < Gam d K t ∧ Gam d K t < 1/4 ∧
      Gam d K t * beta d K t = 4 * d ∧ 0 < Bc K := by
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast hd
  have ht0 : 0 < (t : ℝ) := by exact_mod_cast ht
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hlog := Real.log_nonneg hK1
  have hl : 0 < 1 + Real.log K := by linarith
  have hroot : 0 < Real.sqrt ((d : ℝ) * t / (1 + Real.log K)) :=
    Real.sqrt_pos.mpr (by positivity)
  have hb : 0 < beta d K t := by unfold beta; positivity
  have hg : 0 < Gam d K t := by unfold Gam; positivity
  have hless : Gam d K t < 1/4 := by
    rw [Gam, div_lt_iff₀ hb]
    unfold beta
    linarith
  have hident : Gam d K t * beta d K t = 4 * d := by
    rw [Gam, div_mul_cancel₀ _ (ne_of_gt hb)]
  have hc : (256 : ℝ) ≤ (⌈256 + Real.log (2 * (K : ℝ))⌉ : ℝ) := by
    have hlog2 : 0 ≤ Real.log (2 * (K : ℝ)) := Real.log_nonneg (by linarith)
    exact (by linarith : (256 : ℝ) ≤ 256 + Real.log (2 * (K : ℝ))).trans (Int.le_ceil _)
  refine ⟨hb, hg, hless, hident, ?_⟩
  unfold Bc
  exact mul_pos (by norm_num) (by linarith)


end D10Proof

theorem solution {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms)
    (t : ℕ) (ht : 1 ≤ t) (S : Fin d → ℝ) (π : Fin K → ℝ) (hπ : IsGOptLaw arms π) :
    let p0 : Fin K → ℝ := fun b => (1 - Gam d K t) * qSoft (beta d K t) arms S b + Gam d K t * π b
    IsFeasible2_3 arms t S p0 ∧
      ∑ b, p0 b • vecMulVec (vCoef arms p0 b) (arms b) = 1 ∧
      (∀ a, ∑ b, p0 b * ((arms a - refArm arms S) ⬝ᵥ vCoef arms p0 b) ^ 2 ≤ beta d K t) ∧
      proxyC arms t S p0 < 2 * (d : ℝ) / beta d K t := by
  classical
  have hK : 1 ≤ K := by
    by_contra hk
    have hz : K = 0 := by omega
    subst K
    have h := hπ.2.1
    simp at h
  let : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
  let β := beta d K t
  let γ := Gam d K t
  let q := qSoft β arms S
  let p : Fin K → ℝ := fun b => (1-γ) * q b + γ * π b
  let M := BanditAlgorithm.linearAllocationMatrix arms p
  let G := BanditAlgorithm.linearAllocationMatrix arms π
  let Q := BanditAlgorithm.linearAllocationMatrix arms q
  let N := M⁻¹
  let bar := abar arms q
  let u (a b : Fin K) := (arms a - bar) ⬝ᵥ N *ᵥ arms b
  obtain ⟨hβ, hγ, hγ4, hγβ, hB⟩ := D10Proof.schedules hd hK ht
  change 0 < β at hβ
  change 0 < γ at hγ
  change γ < 1/4 at hγ4
  change γ * β = 4 * d at hγβ
  have hγ1 : 0 < 1-γ := by linarith
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast hd
  obtain ⟨hq0, hq1⟩ := D10Proof.q_prob β arms S
  change (∀ a, 0 ≤ q a) at hq0
  change (∑ a, q a = 1) at hq1
  have hp0 (b : Fin K) : 0 ≤ p b :=
    add_nonneg (mul_nonneg hγ1.le (hq0 b)) (mul_nonneg hγ.le (hπ.1 b))
  have hp1 : ∑ b, p b = 1 := by
    dsimp [p]
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, hq1, hπ.2.1]
    ring
  have hMmix : M = (1-γ) • Q + γ • G := by
    dsimp [M, Q, G, BanditAlgorithm.linearAllocationMatrix, p]
    simp only [add_smul, mul_smul, sum_add_distrib, smul_sum]
  have hQ : Q.PosSemidef := D10Proof.cov_psd arms q hq0
  have hG : G.PosDef := hπ.2.2.1
  have hM : M.PosDef := by
    rw [hMmix]
    exact PosDef.posSemidef_add (hQ.smul hγ1.le) (hG.smul hγ)
  have hN : N.PosSemidef := hM.inv.posSemidef
  have hdom (x : Fin d → ℝ) : γ * (x ⬝ᵥ G *ᵥ x) ≤ x ⬝ᵥ M *ᵥ x := by
    simp only [hMmix, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
    have h := mul_nonneg hγ1.le (D10Proof.qnonneg Q hQ x)
    linarith
  have hlev (a : Fin K) : arms a ⬝ᵥ N *ᵥ arms a ≤ β/4 := by
    have h := (D10Proof.inverse_le M G hM hG γ hγ hdom (arms a)).trans (hπ.2.2.2 a)
    change γ * (arms a ⬝ᵥ N *ᵥ arms a) ≤ d at h
    apply (mul_le_mul_iff_right₀ hγ).mp
    nlinarith [hγβ]
  have hcross (a b : Fin K) : |arms a ⬝ᵥ N *ᵥ arms b| ≤ β/4 :=
    D10Proof.cross_bound N hN (arms a) (arms b) (β/4) (hlev a) (hlev b)
  have hrec : ∑ b, p b • vecMulVec (N *ᵥ arms b) (arms b) = 1 :=
    D10Proof.reconstruct arms p hM
  have hvar (x : Fin d → ℝ) : ∑ b, p b * (x ⬝ᵥ N *ᵥ arms b)^2 = x ⬝ᵥ N *ᵥ x :=
    D10Proof.variance arms p hM x
  obtain ⟨j, href, hZ⟩ := D10Proof.ref_spec arms S
  have hrow (a : Fin K) : (arms a-refArm arms S) ⬝ᵥ N *ᵥ (arms a-refArm arms S) ≤ β := by
    rw [href, D10Proof.qsub N hN.1]
    have h := D10Proof.qnonneg N hN (arms a + arms j)
    rw [D10Proof.qadd N hN.1] at h
    linarith [hlev a, hlev j]
  have hamp (a b : Fin K) : |(arms a-refArm arms S) ⬝ᵥ N *ᵥ arms b| ≤ β/2 := by
    rw [href, sub_dotProduct]
    exact (abs_sub _ _).trans (by linarith [hcross a b, hcross j b])
  have hbar (b : Fin K) : |bar ⬝ᵥ N *ᵥ arms b| ≤ β/4 := by
    change |(∑ a, q a • arms a) ⬝ᵥ N *ᵥ arms b| ≤ _
    rw [sum_dotProduct]
    simp only [smul_dotProduct, smul_eq_mul]
    calc
      _ ≤ ∑ a, |q a * (arms a ⬝ᵥ N *ᵥ arms b)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, q a * (β/4) := by
        apply sum_le_sum
        intro a _
        rw [abs_mul, abs_of_nonneg (hq0 a)]
        exact mul_le_mul_of_nonneg_left (hcross a b) (hq0 a)
      _ = β/4 := by rw [← sum_mul, hq1, one_mul]
  have hu (a b : Fin K) : |u a b| ≤ β/2 := by
    dsimp [u]
    rw [sub_dotProduct]
    exact (abs_sub _ _).trans (by linarith [hcross a b, hbar b])
  let X := ∑ a, q a * (arms a ⬝ᵥ N *ᵥ arms a)
  have hX0 : 0 ≤ X := sum_nonneg fun a _ =>
    mul_nonneg (hq0 a) (D10Proof.qnonneg N hN (arms a))
  have htrace : (1-γ) * X ≤ d := by
    calc
      _ = ∑ a, ((1-γ) * q a) * (arms a ⬝ᵥ N *ᵥ arms a) := by
        dsimp [X]; rw [mul_sum]; apply sum_congr rfl; intro a _; ring
      _ ≤ ∑ a, p a * (arms a ⬝ᵥ N *ᵥ arms a) := by
        apply sum_le_sum
        intro a _
        apply mul_le_mul_of_nonneg_right _ (D10Proof.qnonneg N hN (arms a))
        exact le_add_of_nonneg_right (mul_nonneg hγ.le (hπ.1 a))
      _ = d := D10Proof.leverage_sum arms p hM
  have htrace3 : 3 * X < 4 * d := by
    by_cases hx : X = 0
    · rw [hx]; nlinarith
    · have hxpos : 0 < X := lt_of_le_of_ne hX0 (Ne.symm hx)
      have hh := mul_lt_mul_of_pos_right (show (3/4 : ℝ) < 1-γ by linarith) hxpos
      linarith
  let V := ∑ b, p b * ∑ a, q a * (u a b)^2
  have hV : V ≤ X := by
    calc
      _ = ∑ a, q a * ((arms a-bar) ⬝ᵥ N *ᵥ (arms a-bar)) := by
        dsimp [V, u]
        simp_rw [mul_sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro a _
        rw [← hvar (arms a-bar), mul_sum]
        apply sum_congr rfl
        intro b _
        ring
      _ = X - bar ⬝ᵥ N *ᵥ bar := D10Proof.centered_variance N hN.1 arms q hq1
      _ ≤ X := sub_le_self _ (D10Proof.qnonneg N hN bar)
  have hchi (a b : Fin K) : β^2 * chi (u a b / β) ≤ (3/2 : ℝ) * (u a b)^2 := by
    have ha : |u a b / β| ≤ 1 := by
      rw [abs_div, abs_of_pos hβ]
      apply (div_le_one hβ).mpr
      linarith [hu a b]
    have hc := IAFTRL.lemma_J_4.{0}.2.2.2.2.2.2.1 (u a b / β) ha
    have hm := mul_le_mul_of_nonneg_left hc (sq_nonneg β)
    have heq : β^2 * ((3/2 : ℝ) * (u a b / β)^2) = (3/2 : ℝ) * (u a b)^2 := by
      field_simp [ne_of_gt hβ]
    exact hm.trans_eq heq
  have hproxy : β * proxyC arms t S p ≤ (3/2 : ℝ) * V := by
    have hs := sum_le_sum (fun b (_hb : b ∈ (univ : Finset (Fin K))) =>
      mul_le_mul_of_nonneg_left
        (sum_le_sum (fun a (_ha : a ∈ (univ : Finset (Fin K))) =>
          mul_le_mul_of_nonneg_left (hchi a b) (hq0 a))) (hp0 b))
    rw [D10Proof.weighted_scale, D10Proof.weighted_scale] at hs
    change β * (β * ∑ b, p b * ∑ a, q a * chi (u a b / β)) ≤ _
    simpa only [V, pow_two, mul_assoc] using hs
  have hproxyLt : proxyC arms t S p < 2 * d / β := by
    apply (lt_div_iff₀ hβ).mpr
    nlinarith [hproxy, hV, htrace3]
  change IsFeasible2_3 arms t S p ∧ _ ∧ _ ∧ _
  refine ⟨?_, hrec, ?_, hproxyLt⟩
  · refine ⟨hp0, hp1, ?_, ?_, ?_, hproxyLt.le⟩
    · refine ⟨fun b => γ * π b, fun b => mul_nonneg hγ.le (hπ.1 b), ?_, ?_⟩
      · rw [← mul_sum, hπ.2.1, mul_one]
      · rw [← mul_sum, hπ.2.1, mul_one]
    · intro a b
      exact (hamp a b).trans (by
        have h := div_nonneg (hZ a) hB.le
        change β/2 ≤ β + Zd arms S a / Bc K
        linarith)
    · intro a
      exact (hrow a).trans (le_add_of_nonneg_right
        (div_nonneg (sq_nonneg _) (mul_nonneg hB.le (by positivity))))
  · intro a
    change ∑ b, p b * ((arms a-refArm arms S) ⬝ᵥ N *ᵥ arms b)^2 ≤ β
    rw [hvar]
    exact hrow a

