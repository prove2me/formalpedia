-- Prove2me | solution 1 for MinimaxSLP.ObjExtremal.feasible9_approx
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T22:39:03.506633+00:00
-- url     : https://prove2.me/submissions/cf5d7643-d3a2-444c-9ade-1c975bd22cbf

import Mathlib
import Definitions.Def_MinimaxSLP_ObjExtremal_Model
import Theorems.Thm_MinimaxSLP_ObjExtremal_Qval_homogeneous_superadditive
import Theorems.Thm_MinimaxSLP_ObjExtremal_scaled_weak_duality

open MeasureTheory Matrix

namespace MSLP2Aux
open MinimaxSLP.ObjSDP MinimaxSLP.ObjExtremal

noncomputable def discMeas {d : ℕ} {ι : Type} [Fintype ι] (w : ι → ℝ) (z : ι → Fin d → ℝ) :
    Measure (Fin d → ℝ) :=
  ∑ a, ENNReal.ofReal (w a) • Measure.dirac (z a)

lemma discMeas_integrable {d : ℕ} {ι : Type} [Fintype ι] (w : ι → ℝ) (z : ι → Fin d → ℝ)
    (f : (Fin d → ℝ) → ℝ) : Integrable f (discMeas w z) := by
  unfold discMeas
  rw [integrable_finsetSum_measure]
  intro a _
  exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

lemma discMeas_integral {d : ℕ} {ι : Type} [Fintype ι] (w : ι → ℝ) (hw : ∀ a, 0 ≤ w a)
    (z : ι → Fin d → ℝ) (f : (Fin d → ℝ) → ℝ) :
    ∫ q, f q ∂(discMeas w z) = ∑ a, w a * f (z a) := by
  unfold discMeas
  rw [integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw a), smul_eq_mul]
  · intro a _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

lemma discMeas_prob {d : ℕ} {ι : Type} [Fintype ι] (w : ι → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hsum : ∑ a, w a = 1) (z : ι → Fin d → ℝ) : IsProbabilityMeasure (discMeas w z) := by
  constructor
  unfold discMeas
  simp only [Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hw a), hsum, ENNReal.ofReal_one]

lemma discMeas_memLp {d : ℕ} {ι : Type} [Fintype ι] (w : ι → ℝ) (z : ι → Fin d → ℝ)
    (i : Fin d) : MemLp (fun ξ : Fin d → ℝ => ξ i) 2 (discMeas w z) := by
  rw [memLp_two_iff_integrable_sq (continuous_apply i).aestronglyMeasurable]
  exact discMeas_integrable w z _

/-- weights of the mixture -/
noncomputable def wt {K L : ℕ} (v0 : Fin K → ℝ) (ε : ℝ) : Fin K × Option (Fin L × Bool) → ℝ
  | (k, none) => v0 k * (1 - ε)
  | (k, some _) => v0 k * ε / (2 * L)

/-- atoms of the mixture -/
noncomputable def pt {K L d : ℕ} (m : Fin K → Fin d → ℝ) (c : Fin L → Fin d → ℝ) (t : ℝ) :
    Fin K × Option (Fin L × Bool) → Fin d → ℝ
  | (k, none) => m k
  | (k, some (l, b)) => m k + t • (if b then c l else -c l)

lemma sum_idx {K L : ℕ} (F : Fin K × Option (Fin L × Bool) → ℝ) :
    ∑ a, F a = ∑ k, (F (k, none) + ∑ l, (F (k, some (l, true)) + F (k, some (l, false)))) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp [Fintype.sum_bool]

lemma wt_nonneg {K L : ℕ} (v0 : Fin K → ℝ) (hv0 : ∀ k, 0 ≤ v0 k) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (a : Fin K × Option (Fin L × Bool)) : 0 ≤ wt (L := L) v0 ε a := by
  rcases a with ⟨k, _ | _⟩
  · exact mul_nonneg (hv0 k) (by linarith)
  · simp only [wt]; have := hv0 k; positivity

lemma moments {K L d : ℕ} (hL : 0 < L) (v0 : Fin K → ℝ) (hv0 : ∀ k, 0 ≤ v0 k)
    (hsum : ∑ k, v0 k = 1) (m : Fin K → Fin d → ℝ) (c : Fin L → Fin d → ℝ) (ε t : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (ht : ε * t ^ 2 = L) :
    discMeas (wt (L := L) v0 ε) (pt m c t) ∈
      momentClass (fun i => ∑ k, v0 k * m k i)
        (Matrix.of fun i j => ∑ k, v0 k * (m k i * m k j) + ∑ l, c l i * c l j) := by
  have hw := wt_nonneg (L := L) v0 hv0 ε hε hε1
  have hLr : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hws : ∑ a, wt (L := L) v0 ε a = 1 := by
    rw [sum_idx]
    simp only [wt, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) hsum
    field_simp
    ring
  have := discMeas_prob _ hw hws (pt m c t)
  refine ⟨⟨inferInstance, discMeas_memLp _ _⟩, ?_, ?_⟩
  · funext i
    simp only [MomentDRO.Conf.meanVec]
    rw [discMeas_integral _ hw, sum_idx]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [wt, pt, if_true, if_false, Pi.add_apply, Pi.smul_apply, Pi.neg_apply,
      smul_eq_mul, Bool.false_eq_true]
    have : ∀ l : Fin L, v0 k * ε / (2 * L) * (m k i + t * c l i) +
        v0 k * ε / (2 * L) * (m k i + t * -c l i) = v0 k * ε / L * m k i := by
      intro l; field_simp; ring
    rw [Finset.sum_congr rfl fun l _ => this l, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  · ext i j
    simp only [MomentDRO.Conf.secondMomentAbout, of_apply, Pi.zero_apply, sub_zero]
    rw [discMeas_integral _ hw (pt m c t) (fun ξ => ξ i * ξ j), sum_idx]
    simp only [wt, pt, if_true, if_false, Pi.add_apply, Pi.smul_apply, Pi.neg_apply,
      smul_eq_mul, Bool.false_eq_true]
    have : ∀ k, ∀ l : Fin L, v0 k * ε / (2 * L) * ((m k i + t * c l i) * (m k j + t * c l j)) +
        v0 k * ε / (2 * L) * ((m k i + t * -c l i) * (m k j + t * -c l j)) =
        v0 k * ε / L * (m k i * m k j) + v0 k * (c l i * c l j) := by
      intro k l
      have : v0 k * ε / (2 * L) * (2 * t ^ 2 * (c l i * c l j)) = v0 k * (c l i * c l j) := by
        rw [show v0 k * ε / (2 * L) * (2 * t ^ 2 * (c l i * c l j)) =
          v0 k * (ε * t ^ 2) / L * (c l i * c l j) by ring, ht]
        field_simp
      linear_combination this
    simp only [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    rw [← Finset.sum_mul, hsum, Finset.mul_sum, one_mul, ← add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
    ring

lemma bordered_quad {d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) (v0 : ℝ)
    (z : Fin d → ℝ) (c : ℝ) :
    star (Sum.elim z (fun _ : Fin 1 => c)) ⬝ᵥ (bordered V v v0 *ᵥ Sum.elim z (fun _ => c)) =
      z ⬝ᵥ (V *ᵥ z) + 2 * c * (z ⬝ᵥ v) + c ^ 2 * v0 := by
  simp only [star_trivial, bordered, dotProduct, mulVec, Fintype.sum_sum_type, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Sum.elim_inl, Sum.elim_inr, of_apply,
    Fin.sum_univ_one]
  simp only [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  have : ∀ i, ∑ j, z i * (V i j * z j) = ∑ j, z i * V i j * z j := fun i =>
    Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun i _ => this i]
  have e1 : ∑ i, z i * (v i * c) = ∑ i, c * (z i * v i) := Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, c * (v i * z i) = ∑ i, c * (z i * v i) := Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2]
  simp only [← Finset.mul_sum]
  ring
open scoped MatrixOrder in
lemma psd_factor {d : ℕ} (R : Matrix (Fin d) (Fin d) ℝ) (hR : R.PosSemidef) :
    ∃ B : Matrix (Fin d) (Fin d) ℝ, R = Bᵀ * B := by
  have h0 : 0 ≤ R := hR.nonneg
  refine ⟨CFC.sqrt R, ?_⟩
  have hs := (CFC.sqrt_nonneg R).posSemidef.1
  have : (CFC.sqrt R)ᵀ = CFC.sqrt R := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hs
  rw [this, CFC.sqrt_mul_sqrt_self R h0]

/-- the main construction, for a fixed scale `se = √ε ∈ (0,1]` -/
theorem main_bound {n r d K : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty)
    (s : (Fin K → Matrix (Fin d) (Fin d) ℝ) × (Fin K → Fin d → ℝ) × (Fin K → ℝ) ×
      (Fin K → Fin r → ℝ))
    (hs : s ∈ feasible9 W α μ Q) :
    ∃ E : ℝ, ∀ se : ℝ, 0 < se → se ≤ 1 →
      ∃ P ∈ momentClass μ Q,
        Integrable (fun q => disutility α β (Qval W T h q x)) P ∧
        obj9 T h β x s + se * E ≤ ∫ q, disutility α β (Qval W T h q x) ∂P := by
  obtain ⟨V, v, v0, p⟩ := s
  obtain ⟨hsumB, hpsd, hdual⟩ := hs
  simp only at hsumB hpsd hdual
  obtain ⟨hhom, hsup⟩ := Qval_homogeneous_superadditive W T h hA3 x hrec
  set Qv : (Fin d → ℝ) → ℝ := fun q => Qval W T h q x with hQv
  have hQv0 : Qv 0 = 0 := by
    have := hhom 2 (by norm_num) 0
    simp only [smul_zero] at this
    show Qval W T h 0 x = 0
    linarith
  -- quadratic form facts
  have F1 : ∀ k z c, 0 ≤ z ⬝ᵥ (V k *ᵥ z) + 2 * c * (z ⬝ᵥ v k) + c ^ 2 * v0 k := by
    intro k z c
    rw [← bordered_quad]
    exact (hpsd k).dotProduct_mulVec_nonneg _
  have F2 : ∀ k, 0 ≤ v0 k := by
    intro k; have := F1 k 0 1; simpa using this
  have F3 : ∀ a b, ∑ k, V k a b = Q a b := by
    intro a b
    have := congrFun (congrFun hsumB (Sum.inl a)) (Sum.inl b)
    simpa [Matrix.sum_apply, bordered] using this
  have F3' : ∀ a, ∑ k, v k a = μ a := by
    intro a
    have := congrFun (congrFun hsumB (Sum.inl a)) (Sum.inr 0)
    simpa [Matrix.sum_apply, bordered] using this
  have F3'' : ∑ k, v0 k = 1 := by
    have := congrFun (congrFun hsumB (Sum.inr 0)) (Sum.inr 0)
    simpa [Matrix.sum_apply, bordered] using this
  have F4 : ∀ k, v0 k = 0 → v k = 0 := by
    intro k hk
    have hB : 0 ≤ v k ⬝ᵥ v k := by
      simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    rcases hB.lt_or_eq with hB | hB
    · exfalso
      set A := v k ⬝ᵥ (V k *ᵥ v k)
      have := F1 k (v k) (-(|A| + 1) / (2 * (v k ⬝ᵥ v k)))
      rw [hk] at this
      have e : 2 * (-(|A| + 1) / (2 * (v k ⬝ᵥ v k))) * (v k ⬝ᵥ v k) = -(|A| + 1) := by
        field_simp
      rw [e] at this
      have := le_abs_self A
      nlinarith
    · exact dotProduct_self_eq_zero.mp hB.symm
  set m : Fin K → Fin d → ℝ := fun k => (v0 k)⁻¹ • v k with hm
  have F6 : ∀ k, v0 k • m k = v k := by
    intro k
    rcases (F2 k).lt_or_eq with hk | hk
    · simp only [hm, smul_smul, mul_inv_cancel₀ hk.ne', one_smul]
    · rw [← hk, zero_smul, F4 k hk.symm]
  have F5 : ∀ k z, v0 k * (z ⬝ᵥ m k) ^ 2 ≤ z ⬝ᵥ (V k *ᵥ z) := by
    intro k z
    rcases (F2 k).lt_or_eq with hk | hk
    · have := F1 k z (-(z ⬝ᵥ m k))
      have e : z ⬝ᵥ v k = v0 k * (z ⬝ᵥ m k) := by
        rw [← F6 k, dotProduct_smul, smul_eq_mul]
      rw [e] at this
      nlinarith
    · rw [← hk, zero_mul]
      have := F1 k z 0
      simpa using this
  -- the residual covariance
  set R : Matrix (Fin d) (Fin d) ℝ := Q - ∑ k, v0 k • vecMulVec (m k) (m k) with hR
  have hRent : ∀ a b, R a b = Q a b - ∑ k, v0 k * (m k a * m k b) := by
    intro a b
    simp [hR, Matrix.sum_apply, vecMulVec_apply]
  have hVsym : ∀ k a b, V k a b = V k b a := by
    intro k a b
    have := congrFun (congrFun (hpsd k).1 (Sum.inl a)) (Sum.inl b)
    simpa [bordered, conjTranspose_apply] using this.symm
  have hRpsd : R.PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext a b
      simp only [conjTranspose_apply, star_trivial, hRent, ← F3]
      rw [Finset.sum_congr rfl fun k _ => hVsym k b a]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by ring
    · intro z
      simp only [star_trivial]
      have hQs : Q = ∑ k, V k := by
        ext a b; rw [Matrix.sum_apply, F3]
      have : z ⬝ᵥ (R *ᵥ z) = ∑ k, (z ⬝ᵥ (V k *ᵥ z) - v0 k * (z ⬝ᵥ m k) ^ 2) := by
        rw [hR, hQs, sub_mulVec, sum_mulVec, sum_mulVec, dotProduct_sub, dotProduct_sum,
          dotProduct_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, dotProduct_smul,
          smul_eq_mul, smul_eq_mul, dotProduct_comm (m k) z]
        ring
      rw [this]
      exact Finset.sum_nonneg fun k _ => sub_nonneg.mpr (F5 k z)
  obtain ⟨B, hB⟩ := psd_factor R hRpsd
  set c : Fin (d + 1) → Fin d → ℝ := fun l a => if hl : (l : ℕ) < d then B ⟨l, hl⟩ a else 0
    with hc
  have hcc : ∀ a b, ∑ l, c l a * c l b = R a b := by
    intro a b
    rw [hB, Fin.sum_univ_castSucc]
    simp [hc, Matrix.mul_apply, transpose_apply]
  have hLpos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
  set sL : ℝ := Real.sqrt ((d + 1 : ℕ) : ℝ) with hsL
  have hsLpos : 0 < sL := Real.sqrt_pos.mpr hLpos
  have hsL2 : sL ^ 2 = ((d + 1 : ℕ) : ℝ) := Real.sq_sqrt hLpos.le
  refine ⟨∑ k, v0 k * α k / (2 * sL) * ∑ l, (Qv (c l) + Qv (-c l)), ?_⟩
  intro se hse hse1
  set ε := se ^ 2 with hε
  set t := sL / se with ht
  have hεpos : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by nlinarith
  have hεt : ε * t ^ 2 = ((d + 1 : ℕ) : ℝ) := by
    rw [hε, ht, div_pow, hsL2]; field_simp
  have hw := wt_nonneg (L := d + 1) v0 F2 ε hεpos hε1
  refine ⟨discMeas (wt (L := d + 1) v0 ε) (pt m c t), ?_, discMeas_integrable _ _ _, ?_⟩
  · have hmc := moments (L := d + 1) (by omega) v0 F2 F3'' m c ε t hεpos hε1 hεt
    have hμ' : (fun i => ∑ k, v0 k * m k i) = μ := by
      funext i; rw [← F3' i]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← F6 k]; rfl
    have hQ' : (Matrix.of fun i j => ∑ k, v0 k * (m k i * m k j) + ∑ l, c l i * c l j) = Q := by
      ext i j; rw [of_apply, hcc, hRent]; ring
    rwa [hμ', hQ'] at hmc
  · rw [discMeas_integral _ hw, sum_idx]
    -- lower bound for the disutility
    have hU : ∀ k z, α k * Qv z + β k ≤ disutility α β (Qval W T h z x) := by
      intro k z
      exact Finset.le_sup' (fun k => α k * Qval W T h z x + β k) (Finset.mem_univ k)
    have hS : ∀ k u, α k * (Qv (m k) + t * Qv u) + β k ≤
        disutility α β (Qval W T h (m k + t • u) x) := by
      intro k u
      refine le_trans ?_ (hU k _)
      have h1 := hsup (m k) (t • u)
      rw [hhom t (by positivity) u] at h1
      have := hα k
      show α k * (Qv (m k) + t * Qv u) + β k ≤ α k * Qval W T h (m k + t • u) x + β k
      nlinarith
    have hdualk : ∀ k, (h - T *ᵥ x) ⬝ᵥ p k ≤ v0 k * (α k * Qv (m k)) := by
      intro k
      have := scaled_weak_duality W T h hA3 x hrec (α k) (hα k) (v k) (p k) (hdual k)
      refine this.trans (le_of_eq ?_)
      rcases (F2 k).lt_or_eq with hk | hk
      · rw [← F6 k]
        show α k * Qval W T h (v0 k • m k) x = v0 k * (α k * Qval W T h (m k) x)
        rw [hhom _ hk]; ring
      · rw [F4 k hk.symm, ← hk]
        show α k * Qval W T h 0 x = 0 * _
        rw [show Qval W T h 0 x = 0 from hQv0]; ring
    unfold obj9
    simp only
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    simp only [wt, pt, if_true, if_false, Bool.false_eq_true]
    have hws : 0 ≤ v0 k * ε / (2 * ((d + 1 : ℕ) : ℝ)) := by have := F2 k; positivity
    have hwn : 0 ≤ v0 k * (1 - ε) := mul_nonneg (F2 k) (by linarith)
    have lb : v0 k * (1 - ε) * (α k * Qv (m k) + β k) +
        ∑ l, (v0 k * ε / (2 * ((d + 1 : ℕ) : ℝ)) * (α k * (Qv (m k) + t * Qv (c l)) + β k) +
          v0 k * ε / (2 * ((d + 1 : ℕ) : ℝ)) * (α k * (Qv (m k) + t * Qv (-c l)) + β k)) ≤
        v0 k * (1 - ε) * disutility α β (Qval W T h (m k) x) +
        ∑ l, (v0 k * ε / (2 * ((d + 1 : ℕ) : ℝ)) * disutility α β (Qval W T h (m k + t • c l) x) +
          v0 k * ε / (2 * ((d + 1 : ℕ) : ℝ)) * disutility α β (Qval W T h (m k + t • -c l) x)) := by
      refine add_le_add (mul_le_mul_of_nonneg_left (hU k _) hwn)
        (Finset.sum_le_sum fun l _ => add_le_add (mul_le_mul_of_nonneg_left (hS k _) hws)
          (mul_le_mul_of_nonneg_left (hS k _) hws))
    refine le_trans ?_ lb
    have e2 : ∀ l, v0 k * ε / (2 * ((d + 1 : ℕ) : ℝ)) * (α k * (Qv (m k) + t * Qv (c l)) + β k) +
          v0 k * ε / (2 * ((d + 1 : ℕ) : ℝ)) * (α k * (Qv (m k) + t * Qv (-c l)) + β k) =
        2 * (v0 k * ε / (2 * ((d + 1 : ℕ) : ℝ))) * (α k * Qv (m k) + β k) +
          (v0 k * ε / (2 * ((d + 1 : ℕ) : ℝ))) * t * α k * (Qv (c l) + Qv (-c l)) := fun l => by ring
    have hdk := hdualk k
    have e3 : v0 k * (1 - ε) * (α k * Qv (m k) + β k) +
        ∑ l : Fin (d + 1), (2 * (v0 k * ε / (2 * ((d + 1 : ℕ) : ℝ))) * (α k * Qv (m k) + β k) +
          (v0 k * ε / (2 * ((d + 1 : ℕ) : ℝ))) * t * α k * (Qv (c l) + Qv (-c l))) =
        v0 k * (α k * Qv (m k)) + β k * v0 k +
          se * (v0 k * α k / (2 * sL) * ∑ l, (Qv (c l) + Qv (-c l))) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum, ht, hε, ← hsL2]
      field_simp
      ring
    rw [Finset.sum_congr rfl fun l _ => e2 l, e3]
    linarith

end MSLP2Aux

open MinimaxSLP.ObjExtremal in
theorem solution {n r d K : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (MinimaxSLP.ObjSDP.recourseSet W T h x).Nonempty)
    (s : (Fin K → Matrix (Fin d) (Fin d) ℝ) × (Fin K → Fin d → ℝ) × (Fin K → ℝ) ×
      (Fin K → Fin r → ℝ))
    (hs : s ∈ feasible9 W α μ Q) (δ : ℝ) (hδ : 0 < δ) :
    ∃ P ∈ MinimaxSLP.ObjSDP.momentClass μ Q,
      Integrable (fun q => MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.ObjSDP.Qval W T h q x)) P ∧
      obj9 T h β x s - δ ≤
        ∫ q, MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.ObjSDP.Qval W T h q x) ∂P := by
  obtain ⟨E, hE⟩ := MSLP2Aux.main_bound W T h α β hα μ Q hA3 x hrec s hs
  have hE1 : 0 < |E| + 1 := by positivity
  set se := min 1 (δ / (|E| + 1)) with hse
  have hse0 : 0 < se := lt_min one_pos (div_pos hδ hE1)
  have hse1 : se ≤ 1 := min_le_left _ _
  have hse2 : se ≤ δ / (|E| + 1) := min_le_right _ _
  obtain ⟨P, hP, hint, hb⟩ := hE se hse0 hse1
  refine ⟨P, hP, hint, le_trans ?_ hb⟩
  have h1 : se * (|E| + 1) ≤ δ := by rwa [le_div_iff₀ hE1] at hse2
  have h2 : -(se * |E|) ≤ se * E := by
    have := neg_abs_le E
    nlinarith
  nlinarith
