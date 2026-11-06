-- Prove2me | solution 1 for LinParamBandits.UEFinite.pull_count_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T20:48:41.01517+00:00
-- url     : https://prove2.me/submissions/3d67ce23-395a-4307-8150-b8f08a370d03
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LinParamBandits_UEFinite_Model
import Definitions.Def_LinParamBandits_UEFinite_UEPolicy
import Theorems.Thm_LinParamBandits_UEFinite_radius_deviation
import Theorems.Thm_LinParamBandits_UEFinite_chernoff_finite_arms
import Theorems.Thm_LinParamBandits_UEFinite_chernoff_infinite_arms

open MeasureTheory ProbabilityTheory

namespace UEFinPullAux

open LinParamBandits.UEFinite Matrix

variable {r : ℕ}

/-! ### Histories: prefixes, marginals, consistency -/

/-- The prefix of length `t` of a history of length `T`. -/
def pre {T t : ℕ} (hle : t ≤ T) (h : LinParamBandits.LowerBound.History r T) :
    LinParamBandits.LowerBound.History r t :=
  fun s => h (Fin.castLE hle s)

lemma measurable_pre {T t : ℕ} (hle : t ≤ T) :
    Measurable (pre (r := r) hle) := by
  rw [measurable_pi_iff]; intro s; exact measurable_pi_apply _

lemma pre_snoc {n t : ℕ} (hle : t ≤ n) (a : LinParamBandits.LowerBound.History r n)
    (x : LinParamBandits.LowerBound.Vec r × ℝ) :
    pre (hle.trans (Nat.le_succ n)) (Fin.snoc (α := fun _ => LinParamBandits.LowerBound.Vec r × ℝ) a x) =
      pre hle a := by
  funext s
  simp only [pre]
  rw [show Fin.castLE (hle.trans (Nat.le_succ n)) s = Fin.castSucc (Fin.castLE hle s) from Fin.ext rfl,
    Fin.snoc_castSucc]

lemma measurable_step (ψ : LinParamBandits.UEGeneral.Policy r) (z : LinParamBandits.LowerBound.Vec r) (n : ℕ) :
    Measurable (fun p : LinParamBandits.LowerBound.History r n × ℝ =>
      Fin.snoc (α := fun _ => LinParamBandits.LowerBound.Vec r × ℝ) p.1
        (ψ.act n p.1, inner ℝ (ψ.act n p.1) z + p.2)) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    have ha : Measurable (fun p : LinParamBandits.LowerBound.History r n × ℝ => ψ.act n p.1) :=
      (ψ.measurable_act n).comp measurable_fst
    refine ha.prodMk ?_
    exact (Measurable.inner ha measurable_const).add measurable_snd
  · simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp measurable_fst

lemma isProb_histMeasure (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) [IsMarkovKernel ν]
    (z : LinParamBandits.LowerBound.Vec r) (ψ : LinParamBandits.UEGeneral.Policy r) :
    ∀ n, IsProbabilityMeasure (LinParamBandits.UEGeneral.histMeasure ν z ψ n)
  | 0 => by
      simp only [LinParamBandits.UEGeneral.histMeasure]; infer_instance
  | n + 1 => by
      have := isProb_histMeasure ν z ψ n
      simp only [LinParamBandits.UEGeneral.histMeasure]
      exact Measure.isProbabilityMeasure_map (measurable_step ψ z n).aemeasurable

lemma map_pre_succ (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) [IsMarkovKernel ν]
    (z : LinParamBandits.LowerBound.Vec r) (ψ : LinParamBandits.UEGeneral.Policy r) (n : ℕ) :
    (LinParamBandits.UEGeneral.histMeasure ν z ψ (n + 1)).map (pre (Nat.le_succ n)) =
      LinParamBandits.UEGeneral.histMeasure ν z ψ n := by
  have := isProb_histMeasure ν z ψ n
  conv_lhs => rw [LinParamBandits.UEGeneral.histMeasure]
  rw [Measure.map_map (measurable_pre _) (measurable_step ψ z n)]
  have hcomp : (pre (r := r) (Nat.le_succ n)) ∘ (fun p : LinParamBandits.LowerBound.History r n × ℝ =>
      Fin.snoc (α := fun _ => LinParamBandits.LowerBound.Vec r × ℝ) p.1
        (ψ.act n p.1, inner ℝ (ψ.act n p.1) z + p.2)) = Prod.fst := by
    funext p
    simp only [Function.comp]
    have := pre_snoc (r := r) (le_refl n) p.1 (ψ.act n p.1, inner ℝ (ψ.act n p.1) z + p.2)
    rw [this]
    rfl
  rw [hcomp]
  exact Measure.fst_compProd _ _

lemma map_pre (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) [IsMarkovKernel ν]
    (z : LinParamBandits.LowerBound.Vec r) (ψ : LinParamBandits.UEGeneral.Policy r) (t : ℕ) :
    ∀ (k : ℕ), (LinParamBandits.UEGeneral.histMeasure ν z ψ (t + k)).map (pre (Nat.le_add_right t k)) =
      LinParamBandits.UEGeneral.histMeasure ν z ψ t
  | 0 => by
      have : (pre (r := r) (Nat.le_add_right t 0)) = id := by funext h s; rfl
      rw [this, Measure.map_id]
      rfl
  | k + 1 => by
      have hcomp : (pre (r := r) (Nat.le_add_right t (k + 1))) =
          (pre (Nat.le_add_right t k)) ∘ (pre (Nat.le_succ (t + k))) := by funext h s; rfl
      rw [hcomp, ← Measure.map_map (measurable_pre _) (measurable_pre _)]
      have h1 := map_pre_succ ν z ψ (t + k)
      change Measure.map _ (Measure.map _ (LinParamBandits.UEGeneral.histMeasure ν z ψ (t + k + 1))) = _
      rw [h1]
      exact map_pre ν z ψ t k

lemma map_pre' (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) [IsMarkovKernel ν]
    (z : LinParamBandits.LowerBound.Vec r) (ψ : LinParamBandits.UEGeneral.Policy r) {t T : ℕ}
    (hle : t ≤ T) :
    (LinParamBandits.UEGeneral.histMeasure ν z ψ T).map (pre hle) =
      LinParamBandits.UEGeneral.histMeasure ν z ψ t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact map_pre ν z ψ t k

/-- A history is consistent with the policy when each arm is the policy's choice on the prefix. -/
def Consistent (ψ : LinParamBandits.UEGeneral.Policy r) {T : ℕ} (h : LinParamBandits.LowerBound.History r T) : Prop :=
  ∀ (t : ℕ) (ht : t < T), (h ⟨t, ht⟩).1 = ψ.act t (pre ht.le h)

lemma measurableSet_consistent (ψ : LinParamBandits.UEGeneral.Policy r) (T : ℕ) :
    MeasurableSet {h : LinParamBandits.LowerBound.History r T | Consistent ψ h} := by
  have : {h : LinParamBandits.LowerBound.History r T | Consistent ψ h} =
      ⋂ (t : ℕ), ⋂ (ht : t < T), {h | (h ⟨t, ht⟩).1 = ψ.act t (pre ht.le h)} := by
    ext h; simp [Consistent]
  rw [this]
  refine MeasurableSet.iInter fun t => MeasurableSet.iInter fun ht => ?_
  exact measurableSet_eq_fun (measurable_fst.comp (measurable_pi_apply _))
    ((ψ.measurable_act t).comp (measurable_pre _))

lemma ae_consistent (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ)
    (z : LinParamBandits.LowerBound.Vec r) (ψ : LinParamBandits.UEGeneral.Policy r) :
    ∀ T, ∀ᵐ h ∂(LinParamBandits.UEGeneral.histMeasure ν z ψ T), Consistent ψ h
  | 0 => Filter.Eventually.of_forall (fun h t ht => absurd ht (Nat.not_lt_zero t))
  | n + 1 => by
      have ih := ae_consistent ν z ψ n
      simp only [LinParamBandits.UEGeneral.histMeasure]
      rw [ae_map_iff (measurable_step ψ z n).aemeasurable (measurableSet_consistent ψ (n + 1))]
      have hms : MeasurableSet {p : LinParamBandits.LowerBound.History r n × ℝ | Consistent ψ p.1} :=
        measurable_fst (measurableSet_consistent ψ n)
      have h2 : ∀ᵐ p ∂((LinParamBandits.UEGeneral.histMeasure ν z ψ n) ⊗ₘ
          (ν.comap (ψ.act n) (ψ.measurable_act n))), Consistent ψ p.1 := by
        apply Measure.ae_compProd_of_ae_ae hms
        filter_upwards [ih] with h hh
        exact Filter.Eventually.of_forall (fun _ => hh)
      filter_upwards [h2] with p hp
      intro t ht
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | ht'
      · have e1 : (⟨t, ht⟩ : Fin (n + 1)) = Fin.castSucc ⟨t, ht'⟩ := Fin.ext rfl
        rw [e1, Fin.snoc_castSucc]
        have := pre_snoc (r := r) ht'.le p.1 (ψ.act n p.1, inner ℝ (ψ.act n p.1) z + p.2)
        rw [this]
        exact hp t ht'
      · subst ht'
        have e1 : (⟨t, ht⟩ : Fin (t + 1)) = Fin.last t := Fin.ext rfl
        rw [e1, Fin.snoc_last]
        have := pre_snoc (r := r) (le_refl t) p.1 (ψ.act t p.1, inner ℝ (ψ.act t p.1) z + p.2)
        rw [this]
        rfl

/-! ### Counting -/

lemma pullCount_eq (u : LinParamBandits.LowerBound.Vec r) {T : ℕ} (h : LinParamBandits.LowerBound.History r T) :
    pullCount u h = (Finset.univ.filter (fun s : Fin T => (h s).1 = u)).card := by
  classical
  unfold pullCount
  congr 1

lemma pullCount_pre (u : LinParamBandits.LowerBound.Vec r) {t T : ℕ} (hle : t ≤ T)
    (h : LinParamBandits.LowerBound.History r T) :
    pullCount u (pre hle h) =
      (Finset.univ.filter (fun s : Fin T => s.val < t ∧ (h s).1 = u)).card := by
  classical
  rw [pullCount_eq]
  apply Finset.card_bij (fun s _ => Fin.castLE hle s)
  · intro s hs
    rw [Finset.mem_filter] at hs ⊢
    exact ⟨Finset.mem_univ _, s.isLt, hs.2⟩
  · intro a _ b _ hab
    exact Fin.castLE_injective hle hab
  · intro s hs
    rw [Finset.mem_filter] at hs
    exact ⟨⟨s.val, hs.2.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.2.2⟩, Fin.ext rfl⟩

lemma count_split (u : LinParamBandits.LowerBound.Vec r) {T : ℕ} (h : LinParamBandits.LowerBound.History r T)
    (θ : ℕ) :
    pullCount u h ≤ θ + (Finset.univ.filter (fun s : Fin T =>
      (h s).1 = u ∧ θ ≤ pullCount u (pre s.isLt.le h))).card := by
  classical
  rw [pullCount_eq]
  set S := Finset.univ.filter (fun s : Fin T => (h s).1 = u)
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := S) (p := fun s : Fin T => θ ≤ pullCount u (pre s.isLt.le h))
  have h1 : (S.filter (fun s : Fin T => ¬ θ ≤ pullCount u (pre s.isLt.le h))).card ≤ θ := by
    have := Finset.card_le_card_of_injOn (s := S.filter (fun s : Fin T => ¬ θ ≤ pullCount u (pre s.isLt.le h)))
      (t := Finset.range θ) (fun s => pullCount u (pre s.isLt.le h)) ?_ ?_
    · simpa using this
    · intro s hs
      simp only [Finset.coe_filter, Set.mem_setOf_eq, S, Finset.mem_filter, Finset.mem_univ,
        true_and] at hs
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
    · intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_setOf_eq, S, Finset.mem_filter, Finset.mem_univ,
        true_and] at ha hb
      simp only at hab
      by_contra hne
      have key : ∀ a b : Fin T, (h a).1 = u → a < b →
          pullCount u (pre a.isLt.le h) < pullCount u (pre b.isLt.le h) := by
        intro a b ha hab
        rw [pullCount_pre, pullCount_pre]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨a, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hab, ha⟩
          · simp
        · intro s hs
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
          exact ⟨lt_trans hs.1 hab, hs.2⟩
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have := key a b ha.1 hlt; omega
      · have := key b a hb.1 hlt; omega
  have h2 : (S.filter (fun s : Fin T => θ ≤ pullCount u (pre s.isLt.le h))).card =
      (Finset.univ.filter (fun s : Fin T => (h s).1 = u ∧ θ ≤ pullCount u (pre s.isLt.le h))).card := by
    rw [Finset.filter_filter]
  omega

/-! ### Linear algebra: `‖u‖²_{C_t} ≤ 1 / N^u` -/

lemma quad_eq_sum {r n : ℕ} (v : Fin n → Fin r → ℝ) (y : Fin r → ℝ) :
    y ⬝ᵥ ((∑ s, Matrix.vecMulVec (v s) (v s)) *ᵥ y) = ∑ s, (v s ⬝ᵥ y) ^ 2 := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Matrix.vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, smul_eq_mul, dotProduct_comm y]
  ring

lemma quad_le {r n : ℕ} (v : Fin n → Fin r → ℝ) (u : Fin r → ℝ) (N : ℕ)
    (hN : N ≤ (Finset.univ.filter (fun s => v s = u)).card) (hN1 : 1 ≤ N)
    (hinj : Function.Injective (∑ s, Matrix.vecMulVec (v s) (v s)).mulVec) :
    0 ≤ u ⬝ᵥ ((∑ s, Matrix.vecMulVec (v s) (v s))⁻¹ *ᵥ u) ∧
      u ⬝ᵥ ((∑ s, Matrix.vecMulVec (v s) (v s))⁻¹ *ᵥ u) ≤ 1 / N := by
  classical
  set G := ∑ s, Matrix.vecMulVec (v s) (v s) with hG
  have hunit : IsUnit G := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hunit
  set y := G⁻¹ *ᵥ u with hy
  have hGy : G *ᵥ y = u := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  set q := u ⬝ᵥ y with hq
  have hq_eq : q = ∑ s, (v s ⬝ᵥ y) ^ 2 := by
    rw [← quad_eq_sum, ← hG, hGy, hq, dotProduct_comm]
  have hq0 : 0 ≤ q := by rw [hq_eq]; positivity
  have hlow : (N : ℝ) * q ^ 2 ≤ q := by
    calc (N : ℝ) * q ^ 2 ≤ ((Finset.univ.filter (fun s => v s = u)).card : ℝ) * q ^ 2 := by
          gcongr
      _ = ∑ s ∈ Finset.univ.filter (fun s => v s = u), (v s ⬝ᵥ y) ^ 2 := by
          rw [Finset.sum_congr rfl (g := fun _ => q ^ 2)]
          · simp
          · intro s hs
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
            rw [hs]
      _ ≤ ∑ s, (v s ⬝ᵥ y) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
      _ = q := hq_eq.symm
  refine ⟨hq0, ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  rcases hq0.lt_or_eq with hqpos | hq00
  · rw [le_div_iff₀ hNpos]
    have : (N : ℝ) * q * q ≤ 1 * q := by nlinarith
    have := le_of_mul_le_mul_right this hqpos
    linarith
  · rw [← hq00]; positivity

/-! ### Elementary estimates -/

lemma kappa0_ge_two (ū lam₀ : ℝ) (hū : 0 < ū) (hlam₀ : 0 < lam₀) : 2 ≤ kappa0 ū lam₀ := by
  unfold kappa0
  have h1 : 0 ≤ Real.log (1 + 36 * ū ^ 2 / lam₀) := Real.log_nonneg (by
    have : 0 ≤ 36 * ū ^ 2 / lam₀ := by positivity
    linarith)
  have h2 : 1 ≤ Real.sqrt (1 + Real.log (1 + 36 * ū ^ 2 / lam₀)) := by
    rw [Real.one_le_sqrt]; linarith
  linarith

lemma bound_B1 (κ : ℝ) (hκ : 2 ≤ κ) (t n : ℕ) (ht : 2 ≤ t) (hn : 1 ≤ n) :
    (t : ℝ) ^ (5 * n) * Real.exp (-(4 * κ ^ 2 * Real.sqrt (Real.log t) * Real.sqrt n) ^ 2 / 2) ≤
      1 / (t : ℝ) ^ 2 := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hlog : 0 ≤ Real.log t := Real.log_natCast_nonneg t
  have hsq : (4 * κ ^ 2 * Real.sqrt (Real.log t) * Real.sqrt n) ^ 2 =
      16 * κ ^ 4 * Real.log t * n := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hlog, Real.sq_sqrt (by positivity)]; ring
  rw [hsq]
  have hpow : (t : ℝ) ^ (5 * n) = Real.exp ((5 * n : ℝ) * Real.log t) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos htpos]; push_cast; ring_nf
  have hinv : 1 / (t : ℝ) ^ 2 = Real.exp (-2 * Real.log t) := by
    rw [show (-2 : ℝ) * Real.log t = -(2 * Real.log t) by ring, Real.exp_neg,
      show (2 : ℝ) * Real.log t = Real.log ((t : ℝ) ^ 2) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity), one_div]
  rw [hpow, hinv, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hκ4 : 16 ≤ κ ^ 4 := by nlinarith [sq_nonneg κ, sq_nonneg (κ ^ 2 - 4)]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : (5 * n : ℝ) * Real.log t + -(16 * κ ^ 4 * Real.log t * n) / 2 =
      (n : ℝ) * Real.log t * (5 - 8 * κ ^ 4) := by ring
  rw [this]
  have h1 : (n : ℝ) * Real.log t * (5 - 8 * κ ^ 4) ≤ (n : ℝ) * Real.log t * (-2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
  nlinarith

lemma bound_B2 (κ : ℝ) (hκ : 2 ≤ κ) (t r : ℕ) (ht : 2 ≤ t) (hr : 2 ≤ r) :
    (t : ℝ) ^ ((r : ℝ) * κ ^ 2) * Real.exp (-(4 * κ * Real.sqrt ((r : ℝ) * Real.log t)) ^ 2 / 4) ≤
      1 / (t : ℝ) ^ 2 := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hlog : 0 ≤ Real.log t := Real.log_natCast_nonneg t
  have hsq : (4 * κ * Real.sqrt ((r : ℝ) * Real.log t)) ^ 2 = 16 * κ ^ 2 * (r * Real.log t) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
  rw [hsq, Real.rpow_def_of_pos htpos]
  have hinv : 1 / (t : ℝ) ^ 2 = Real.exp (-2 * Real.log t) := by
    rw [show (-2 : ℝ) * Real.log t = -(2 * Real.log t) by ring, Real.exp_neg,
      show (2 : ℝ) * Real.log t = Real.log ((t : ℝ) ^ 2) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity), one_div]
  rw [hinv, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have : Real.log t * (r * κ ^ 2) + -(16 * κ ^ 2 * (r * Real.log t)) / 4 =
      -(3 * r * κ ^ 2) * Real.log t := by ring
  rw [this]
  have h3 : 2 ≤ 3 * r * κ ^ 2 := by nlinarith
  nlinarith

lemma two_le_zeta2 (κ : ℝ) (hκ : 2 ≤ κ) (t r : ℕ) (ht : 2 ≤ t) (hr : 2 ≤ r) :
    2 ≤ 4 * κ * Real.sqrt ((r : ℝ) * Real.log t) := by
  have hlog2 : Real.log 2 ≤ Real.log t :=
    Real.log_le_log (by norm_num) (by exact_mod_cast ht)
  have hl2 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have h1 : 1 ≤ (r : ℝ) * Real.log t := by nlinarith
  have h2 : 1 ≤ Real.sqrt ((r : ℝ) * Real.log t) := by rw [Real.one_le_sqrt]; exact h1
  nlinarith

/-- `∑_{2 ≤ s < n} 1/s² ≤ 1`. -/
lemma sum_inv_sq_le : ∀ n : ℕ,
    ∑ s ∈ Finset.range (n + 2), (if 2 ≤ s then 1 / (s : ℝ) ^ 2 else 0) ≤ 1 - 1 / ((n : ℝ) + 1)
  | 0 => by simp [Finset.sum_range_succ]
  | n + 1 => by
      rw [Finset.sum_range_succ]
      have ih := sum_inv_sq_le n
      rw [if_pos (by omega)]
      have : 1 / ((n : ℝ) + 2) ^ 2 ≤ 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2) := by
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have e : (n : ℝ) + 1 + 1 = n + 2 := by ring
      push_cast
      rw [e]
      linarith


lemma measurable_pullCount (u : LinParamBandits.LowerBound.Vec r) (n : ℕ) :
    Measurable (fun h : LinParamBandits.LowerBound.History r n => (pullCount u h : ℝ)) := by
  classical
  have : (fun h : LinParamBandits.LowerBound.History r n => (pullCount u h : ℝ)) =
      fun h => ∑ s, (if (h s).1 = u then (1 : ℝ) else 0) := by
    funext h
    simp only [pullCount]
    rw [Finset.sum_boole]
  rw [this]
  refine Finset.measurable_sum _ (fun s _ => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurable_fst.comp (measurable_pi_apply s)) (measurableSet_singleton u)

/-- The case analysis of Lemma B.6 (p. 34): Theorems B.1 and B.2 give the `1/t²` bound. -/
lemma dev_of_chernoff (σ₀ ū lam₀ : ℝ) (hū : 0 < ū) (hlam₀ : 0 < lam₀)
    (hr : 2 ≤ r) (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰ne : 𝒰.Nonempty)
    (t : ℕ) (ht : r ≤ t) (μ : Measure (LinParamBandits.LowerBound.History r t))
    (D Nm : LinParamBandits.LowerBound.History r t → ℝ)
    (hB1 : ∀ ζ : ℝ, 0 < ζ → 𝒰.Finite →
      μ {h | D h > ζ * σ₀ * Nm h} ≤ ENNReal.ofReal ((t : ℝ) ^ (5 * 𝒰.ncard) * Real.exp (-ζ ^ 2 / 2)))
    (hB2 : ∀ ζ : ℝ, 2 ≤ ζ →
      μ {h | D h > ζ * kappa0 ū lam₀ * σ₀ * Real.sqrt (Real.log t) * Nm h} ≤
        ENNReal.ofReal ((t : ℝ) ^ ((r : ℝ) * kappa0 ū lam₀ ^ 2) * Real.exp (-ζ ^ 2 / 4))) :
    μ {h | D h > alpha σ₀ ū lam₀ * Real.sqrt (Real.log t) *
        Real.sqrt (LinParamBandits.UEGeneral.width 𝒰 t) * Nm h} ≤ ENNReal.ofReal (1 / (t : ℝ) ^ 2) := by
  set κ := kappa0 ū lam₀ with hκdef
  have hκ : 2 ≤ κ := kappa0_ge_two ū lam₀ hū hlam₀
  have ht2 : 2 ≤ t := le_trans hr ht
  have hα : alpha σ₀ ū lam₀ = 4 * σ₀ * κ ^ 2 := rfl
  have caseB2 : LinParamBandits.UEGeneral.width 𝒰 t = (r : ℝ) * Real.log t →
      μ {h | D h > alpha σ₀ ū lam₀ * Real.sqrt (Real.log t) *
        Real.sqrt (LinParamBandits.UEGeneral.width 𝒰 t) * Nm h} ≤ ENNReal.ofReal (1 / (t : ℝ) ^ 2) := by
    intro hw
    set ζ := 4 * κ * Real.sqrt ((r : ℝ) * Real.log t) with hζ
    have hcoef : alpha σ₀ ū lam₀ * Real.sqrt (Real.log t) *
        Real.sqrt (LinParamBandits.UEGeneral.width 𝒰 t) = ζ * κ * σ₀ * Real.sqrt (Real.log t) := by
      rw [hw, hα, hζ]; ring
    simp_rw [hcoef]
    refine (hB2 ζ (two_le_zeta2 κ hκ t r ht2 hr)).trans (ENNReal.ofReal_le_ofReal ?_)
    exact bound_B2 κ hκ t r ht2 hr
  by_cases hfin : 𝒰.Finite
  · have hwdef : LinParamBandits.UEGeneral.width 𝒰 t = min ((r : ℝ) * Real.log t) (𝒰.ncard : ℝ) := by
      unfold LinParamBandits.UEGeneral.width; rw [if_pos hfin]
    rcases le_total ((r : ℝ) * Real.log t) (𝒰.ncard : ℝ) with hle | hle
    · exact caseB2 (by rw [hwdef, min_eq_left hle])
    · have hw : LinParamBandits.UEGeneral.width 𝒰 t = (𝒰.ncard : ℝ) := by rw [hwdef, min_eq_right hle]
      have hn : 1 ≤ 𝒰.ncard := (Set.ncard_pos hfin).mpr h𝒰ne
      set ζ := 4 * κ ^ 2 * Real.sqrt (Real.log t) * Real.sqrt (𝒰.ncard : ℝ) with hζ
      have hlogpos : 0 < Real.log t := Real.log_pos (by exact_mod_cast (show 1 < t by omega))
      have hζpos : 0 < ζ := by
        have : (0 : ℝ) < 𝒰.ncard := by exact_mod_cast hn
        positivity
      have hcoef : alpha σ₀ ū lam₀ * Real.sqrt (Real.log t) *
          Real.sqrt (LinParamBandits.UEGeneral.width 𝒰 t) = ζ * σ₀ := by
        rw [hw, hα, hζ]; ring
      simp_rw [hcoef]
      refine (hB1 ζ hζpos hfin).trans (ENNReal.ofReal_le_ofReal ?_)
      exact bound_B1 κ hκ t _ ht2 hn
  · exact caseB2 (by unfold LinParamBandits.UEGeneral.width; rw [if_neg hfin])

end UEFinPullAux

set_option maxHeartbeats 1000000 in
open UEFinPullAux Matrix in
theorem solution
    (σ₀ ū lam₀ : ℝ) (hσ₀ : 0 < σ₀) (hū : 0 < ū) (hlam₀ : 0 < lam₀)
    (r : ℕ) (hr : 2 ≤ r) (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰fin : 𝒰.Finite) (h𝒰ne : 𝒰.Nonempty)
    (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) (hν : IsMarkovKernel ν) (hnoise : LinParamBandits.UEFinite.NoiseAssumption 𝒰 ν σ₀)
    (b : Fin r → LinParamBandits.LowerBound.Vec r) (harms : LinParamBandits.UEFinite.ArmAssumption 𝒰 b ū lam₀)
    (ψ : LinParamBandits.UEGeneral.Policy r) (hψ : LinParamBandits.UEFinite.IsUE 𝒰 b σ₀ ū lam₀ ψ)
    (T : ℕ) (hT : r + 1 ≤ T) (z u : LinParamBandits.LowerBound.Vec r) (hu : u ∈ 𝒰) (hgap : 0 < LinParamBandits.UEFinite.gap 𝒰 u z) :
    ∫ h, (LinParamBandits.UEFinite.pullCount u h : ℝ) ∂(LinParamBandits.UEGeneral.histMeasure ν z ψ T) ≤
      6 + 4 * LinParamBandits.UEFinite.alpha σ₀ ū lam₀ ^ 2 * (𝒰.ncard : ℝ) * Real.log T / LinParamBandits.UEFinite.gap 𝒰 u z ^ 2 := by
  haveI := hν
  classical
  set α := LinParamBandits.UEFinite.alpha σ₀ ū lam₀ with hαdef
  set Δ := LinParamBandits.UEFinite.gap 𝒰 u z with hΔdef
  set L := Real.log T with hLdef
  set n := 𝒰.ncard with hndef
  set x := 4 * α ^ 2 * (n : ℝ) * L / Δ ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  set θ : ℕ := ⌈x⌉₊ + 1 with hθ
  set μ := LinParamBandits.UEGeneral.histMeasure ν z ψ T with hμ
  have hμprob : IsProbabilityMeasure μ := isProb_histMeasure ν z ψ T
  have hT3 : 3 ≤ T := by omega
  -- an optimal arm
  obtain ⟨w, hw, hwz⟩ : ∃ w ∈ 𝒰, inner ℝ w z = LinParamBandits.UEGeneral.bestValue 𝒰 z := by
    have := (h𝒰ne.image (fun v => inner ℝ v z)).csSup_mem (h𝒰fin.image _)
    obtain ⟨w, hw, hwz⟩ := this
    exact ⟨w, hw, hwz⟩
  -- the two bad events at time s
  let A : (s : ℕ) → Set (LinParamBandits.LowerBound.History r s) := fun s =>
    {g | inner ℝ u (LinParamBandits.UEGeneral.Zhat g - z) > LinParamBandits.UEFinite.radius σ₀ ū lam₀ 𝒰 g u}
  let B : (s : ℕ) → Set (LinParamBandits.LowerBound.History r s) := fun s =>
    {g | inner ℝ w (LinParamBandits.UEGeneral.Zhat g - z) < -LinParamBandits.UEFinite.radius σ₀ ū lam₀ 𝒰 g w}
  have hA : ∀ s, r ≤ s → LinParamBandits.UEGeneral.histMeasure ν z ψ s (A s) ≤
      ENNReal.ofReal (1 / (s : ℝ) ^ 2) := fun s hs =>
    (LinParamBandits.UEFinite.radius_deviation σ₀ ū lam₀ hσ₀ hū hlam₀ r hr 𝒰 h𝒰fin.isCompact h𝒰ne
      ν hν hnoise b harms ψ hψ s hs z).1 u hu
  have hB : ∀ s, r ≤ s → LinParamBandits.UEGeneral.histMeasure ν z ψ s (B s) ≤
      ENNReal.ofReal (1 / (s : ℝ) ^ 2) := by
    intro s hs
    have hset : B s = {g | inner ℝ (-w) (LinParamBandits.UEGeneral.Zhat g - z) >
        α * Real.sqrt (Real.log s) * Real.sqrt (LinParamBandits.UEGeneral.width 𝒰 s) *
          LinParamBandits.UEFinite.normC g (-w)} := by
      ext g
      have hn : LinParamBandits.UEFinite.normC g (-w) = LinParamBandits.UEFinite.normC g w := by
        unfold LinParamBandits.UEFinite.normC
        simp [Matrix.mulVec_neg]
      simp only [B, Set.mem_setOf_eq, inner_neg_left, hn, LinParamBandits.UEFinite.radius]
      constructor <;> intro h <;> linarith
    rw [hset]
    exact dev_of_chernoff σ₀ ū lam₀ hū hlam₀ hr 𝒰 h𝒰ne s hs _ _ _
      (fun ζ hζ hfin => (LinParamBandits.UEFinite.chernoff_finite_arms σ₀ ū lam₀ hσ₀ hū hlam₀ r hr 𝒰 hfin h𝒰ne
        ν hν hnoise b harms ψ hψ s hs (-w) z ζ hζ).1)
      (fun ζ hζ => (LinParamBandits.UEFinite.chernoff_infinite_arms σ₀ ū lam₀ hσ₀ hū hlam₀ r hr 𝒰
        h𝒰fin.isCompact h𝒰ne ν hν hnoise b harms ψ hψ s hs (-w) z ζ hζ).1)
  -- the events on histories of length T
  let S : Fin T → Set (LinParamBandits.LowerBound.History r T) := fun s =>
    {h | r ≤ s.val ∧ (pre s.isLt.le h ∈ A s ∨ pre s.isLt.le h ∈ B s)}
  have hSμ : ∀ s : Fin T, μ (S s) ≤ if r ≤ s.val then ENNReal.ofReal (2 / (s.val : ℝ) ^ 2) else 0 := by
    intro s
    by_cases hrs : r ≤ s.val
    · rw [if_pos hrs]
      have hsub : S s ⊆ (pre s.isLt.le) ⁻¹' (A s) ∪ (pre s.isLt.le) ⁻¹' (B s) := by
        intro h hh; exact hh.2
      have hmap := map_pre' ν z ψ s.isLt.le
      calc μ (S s) ≤ μ ((pre s.isLt.le) ⁻¹' (A s) ∪ (pre s.isLt.le) ⁻¹' (B s)) := measure_mono hsub
        _ ≤ μ ((pre s.isLt.le) ⁻¹' (A s)) + μ ((pre s.isLt.le) ⁻¹' (B s)) := measure_union_le _ _
        _ ≤ μ.map (pre s.isLt.le) (A s) + μ.map (pre s.isLt.le) (B s) :=
            add_le_add (Measure.le_map_apply (measurable_pre _).aemeasurable _)
              (Measure.le_map_apply (measurable_pre _).aemeasurable _)
        _ ≤ ENNReal.ofReal (1 / (s.val : ℝ) ^ 2) + ENNReal.ofReal (1 / (s.val : ℝ) ^ 2) := by
            rw [hμ, hmap]; exact add_le_add (hA s hrs) (hB s hrs)
        _ = ENNReal.ofReal (2 / (s.val : ℝ) ^ 2) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
    · rw [if_neg hrs]
      have : S s = ∅ := by
        ext h; simp only [S, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro h'; exact absurd h' hrs
      rw [this, measure_empty]
  -- the deterministic core
  have hcore : ∀ h : LinParamBandits.LowerBound.History r T, Consistent ψ h → ∀ s : Fin T,
      (h s).1 = u ∧ θ ≤ LinParamBandits.UEFinite.pullCount u (pre s.isLt.le h) → h ∈ S s := by
    intro h hcons s ⟨hsu, hθs⟩
    set g := pre s.isLt.le h with hg
    have hθ1 : 1 ≤ θ := by omega
    have hact : ψ.act s g = u := by rw [← hsu]; exact (hcons s.val s.isLt).symm
    have hb_inj : Function.Injective b := harms.2.2.1.injective
    -- (i) the initialization periods
    have hrs : r ≤ s.val := by
      by_contra hlt
      push Not at hlt
      have hzero : LinParamBandits.UEFinite.pullCount u g = 0 := by
        rw [pullCount_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro s' _ hs'
        have h1 : (g s').1 = b ⟨s'.val, lt_trans s'.isLt hlt⟩ := by
          have := hcons s'.val (lt_trans s'.isLt s.isLt)
          rw [show g s' = h ⟨s'.val, lt_trans s'.isLt s.isLt⟩ from rfl, this]
          exact hψ.2.1 _ _ _
        have h2 : u = b ⟨s.val, hlt⟩ := by
          rw [← hact]; exact hψ.2.1 _ _ _
        rw [h1, h2] at hs'
        have := congrArg Fin.val (hb_inj hs')
        simp only at this
        exact absurd this (Nat.ne_of_lt s'.isLt)
      omega
    refine ⟨hrs, ?_⟩
    by_contra hne
    push Not at hne
    obtain ⟨hnA, hnB⟩ := hne
    simp only [A, B, Set.mem_setOf_eq, not_lt, inner_sub_right] at hnA hnB
    have hargmax := hψ.2.2 s g hrs w hw
    rw [hact] at hargmax
    have hΔle : Δ ≤ 2 * LinParamBandits.UEFinite.radius σ₀ ū lam₀ 𝒰 g u := by
      have : Δ = inner ℝ w z - inner ℝ u z := by
        rw [hΔdef, LinParamBandits.UEFinite.gap, hwz]
      rw [this]; linarith
    -- the radius bound
    set Ng := LinParamBandits.UEFinite.pullCount u g with hNg
    have hNgθ : θ ≤ Ng := hθs
    have hxN : x < Ng := by
      have : x < θ := by
        rw [hθ]; push_cast
        exact lt_of_le_of_lt (Nat.le_ceil x) (by linarith)
      exact lt_of_lt_of_le this (by exact_mod_cast hNgθ)
    have hNgpos : (0 : ℝ) < Ng := lt_of_le_of_lt hx0 hxN
    -- the first r arms of g are b_1, ..., b_r
    have hfirst : ∀ k : Fin r, (g ⟨k.val, lt_of_lt_of_le k.isLt hrs⟩).1 = b k := by
      intro k
      have := hcons k.val (lt_of_lt_of_le k.isLt (hrs.trans s.isLt.le))
      rw [show g ⟨k.val, lt_of_lt_of_le k.isLt hrs⟩ =
        h ⟨k.val, lt_of_lt_of_le k.isLt (hrs.trans s.isLt.le)⟩ from rfl, this]
      exact hψ.2.1 _ _ _
    set v : Fin s.val → Fin r → ℝ := fun s' => WithLp.ofLp (g s').1 with hv
    have hgram : LinParamBandits.UEFinite.gram g = ∑ s', Matrix.vecMulVec (v s') (v s') := rfl
    have hinj : Function.Injective (∑ s', Matrix.vecMulVec (v s') (v s')).mulVec := by
      intro a c hac
      have hz : (∑ s', Matrix.vecMulVec (v s') (v s')) *ᵥ (a - c) = 0 := by
        rw [Matrix.mulVec_sub, hac, sub_self]
      have hq := quad_eq_sum v (a - c)
      rw [hz, dotProduct_zero] at hq
      have hterm : ∀ s', (v s' ⬝ᵥ (a - c)) ^ 2 = 0 := by
        intro s'
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hq.symm s' (Finset.mem_univ _)
      have hmin := harms.2.2.2 (WithLp.toLp 2 (a - c))
      have hsum0 : ∑ k, (inner ℝ (b k) (WithLp.toLp 2 (a - c))) ^ 2 = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        have := hterm ⟨k.val, lt_of_lt_of_le k.isLt hrs⟩
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp only [star_trivial]
        rw [← hfirst k, dotProduct_comm]
        exact this
      rw [hsum0] at hmin
      have hnorm : ‖(WithLp.toLp 2 (a - c) : LinParamBandits.LowerBound.Vec r)‖ = 0 := by
        have : ‖(WithLp.toLp 2 (a - c) : LinParamBandits.LowerBound.Vec r)‖ ^ 2 ≤ 0 := by
          by_contra hc; push Not at hc; nlinarith
        nlinarith [norm_nonneg (WithLp.toLp 2 (a - c) : LinParamBandits.LowerBound.Vec r)]
      rw [norm_eq_zero] at hnorm
      have : a - c = 0 := by
        have := congrArg WithLp.ofLp hnorm
        simpa using this
      exact sub_eq_zero.mp this
    have hcountv : Ng ≤ (Finset.univ.filter (fun s' => v s' = WithLp.ofLp u)).card := by
      rw [hNg, pullCount_eq]
      apply le_of_eq
      congr 1
      apply Finset.filter_congr
      intro s' _
      simp only [hv]
      exact (WithLp.ofLp_injective 2).eq_iff.symm
    obtain ⟨hq0, hq1⟩ := quad_le v (WithLp.ofLp u) Ng hcountv (by exact_mod_cast hNgpos) hinj
    have hnormC : LinParamBandits.UEFinite.normC g u ^ 2 ≤ 1 / Ng := by
      unfold LinParamBandits.UEFinite.normC LinParamBandits.UEFinite.Cmat
      rw [hgram, Real.sq_sqrt hq0]
      exact hq1
    have hwidth : LinParamBandits.UEGeneral.width 𝒰 s ≤ n := by
      unfold LinParamBandits.UEGeneral.width; rw [if_pos h𝒰fin]; exact min_le_right _ _
    have hwidth0 : 0 ≤ LinParamBandits.UEGeneral.width 𝒰 s := by
      unfold LinParamBandits.UEGeneral.width; rw [if_pos h𝒰fin]
      have : (0 : ℝ) ≤ (r : ℝ) * Real.log s := by
        have := Real.log_natCast_nonneg s.val; positivity
      exact le_min this (by positivity)
    have hlogs : Real.log s ≤ L := by
      have hs0 : (0 : ℝ) < s.val := by exact_mod_cast (show 0 < s.val by omega)
      exact Real.log_le_log hs0 (by exact_mod_cast s.isLt.le)
    have hlogs0 : 0 ≤ Real.log s := Real.log_natCast_nonneg s.val
    set R := LinParamBandits.UEFinite.radius σ₀ ū lam₀ 𝒰 g u with hR
    have hR0 : 0 ≤ R := by
      rw [hR, LinParamBandits.UEFinite.radius]
      have : 0 ≤ α := by rw [hαdef, LinParamBandits.UEFinite.alpha]; positivity
      have : 0 ≤ LinParamBandits.UEFinite.normC g u := Real.sqrt_nonneg _
      positivity
    have hR2 : R ^ 2 ≤ α ^ 2 * L * n * (1 / Ng) := by
      rw [hR, LinParamBandits.UEFinite.radius, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hlogs0,
        Real.sq_sqrt hwidth0]
      have : 0 ≤ LinParamBandits.UEFinite.normC g u ^ 2 := sq_nonneg _
      have h1 : α ^ 2 * Real.log s ≤ α ^ 2 * L := mul_le_mul_of_nonneg_left hlogs (sq_nonneg _)
      apply mul_le_mul _ hnormC this (by positivity)
      exact mul_le_mul h1 hwidth hwidth0 (by positivity)
    have hΔ2 : 0 < Δ ^ 2 := by positivity
    have hxN' : 4 * α ^ 2 * n * L < Ng * Δ ^ 2 := by
      rw [hx, div_lt_iff₀ hΔ2] at hxN; linarith
    have hlt1 : (2 * R) ^ 2 ≤ (4 * α ^ 2 * n * L) / Ng := by
      rw [le_div_iff₀ hNgpos]
      have e : α ^ 2 * L * n * (1 / Ng) * Ng = α ^ 2 * L * n := by field_simp
      have := mul_le_mul_of_nonneg_right hR2 hNgpos.le
      rw [e] at this
      nlinarith
    have hlt2 : (4 * α ^ 2 * n * L) / Ng < Δ ^ 2 := by
      rw [div_lt_iff₀ hNgpos]; linarith
    have h2R : 2 * R < Δ := lt_of_pow_lt_pow_left₀ 2 hgap.le (lt_of_le_of_lt hlt1 hlt2)
    exact absurd hΔle (not_le.mpr h2R)
  -- the pointwise bound
  have hpt : ∀ᵐ h ∂μ, ENNReal.ofReal (LinParamBandits.UEFinite.pullCount u h : ℝ) ≤
      (θ : ENNReal) + ∑ s : Fin T, (toMeasurable μ (S s)).indicator 1 h := by
    filter_upwards [ae_consistent ν z ψ T] with h hcons
    rw [ENNReal.ofReal_natCast]
    have hc := count_split u h θ
    calc (LinParamBandits.UEFinite.pullCount u h : ENNReal)
        ≤ ((θ + (Finset.univ.filter (fun s : Fin T =>
          (h s).1 = u ∧ θ ≤ LinParamBandits.UEFinite.pullCount u (pre s.isLt.le h))).card : ℕ) : ENNReal) := by
          exact_mod_cast hc
      _ = (θ : ENNReal) + ∑ s ∈ Finset.univ.filter (fun s : Fin T =>
          (h s).1 = u ∧ θ ≤ LinParamBandits.UEFinite.pullCount u (pre s.isLt.le h)), (1 : ENNReal) := by
          push_cast; simp
      _ ≤ (θ : ENNReal) + ∑ s ∈ Finset.univ.filter (fun s : Fin T =>
          (h s).1 = u ∧ θ ≤ LinParamBandits.UEFinite.pullCount u (pre s.isLt.le h)),
            (toMeasurable μ (S s)).indicator 1 h := by
          gcongr with s hs
          rw [Finset.mem_filter] at hs
          rw [Set.indicator_of_mem (subset_toMeasurable μ (S s) (hcore h hcons s hs.2))]
          simp
      _ ≤ (θ : ENNReal) + ∑ s : Fin T, (toMeasurable μ (S s)).indicator 1 h := by
          gcongr
          exact Finset.filter_subset _ _
  have hlin : ∫⁻ h, ENNReal.ofReal (LinParamBandits.UEFinite.pullCount u h : ℝ) ∂μ ≤
      ENNReal.ofReal ((θ : ℝ) + 2) := by
    calc ∫⁻ h, ENNReal.ofReal (LinParamBandits.UEFinite.pullCount u h : ℝ) ∂μ
        ≤ ∫⁻ h, ((θ : ENNReal) + ∑ s : Fin T, (toMeasurable μ (S s)).indicator 1 h) ∂μ :=
          lintegral_mono_ae hpt
      _ = (θ : ENNReal) + ∑ s : Fin T, μ (S s) := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
          rw [lintegral_finsetSum _ (fun s _ =>
            (measurable_one.indicator (measurableSet_toMeasurable μ (S s))))]
          simp_rw [lintegral_indicator_one (measurableSet_toMeasurable μ _), measure_toMeasurable]
      _ ≤ (θ : ENNReal) + ∑ s : Fin T, (if r ≤ s.val then ENNReal.ofReal (2 / (s.val : ℝ) ^ 2) else 0) := by
          gcongr with s; exact hSμ s
      _ = (θ : ENNReal) + ENNReal.ofReal (∑ s : Fin T, (if r ≤ s.val then 2 / (s.val : ℝ) ^ 2 else 0)) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => by split_ifs <;> positivity)]
          congr 1
          refine Finset.sum_congr rfl (fun s _ => ?_)
          split_ifs <;> simp
      _ ≤ (θ : ENNReal) + ENNReal.ofReal 2 := by
          gcongr
          rw [Fin.sum_univ_eq_sum_range (fun s => if r ≤ s then 2 / (s : ℝ) ^ 2 else 0) T]
          calc ∑ s ∈ Finset.range T, (if r ≤ s then 2 / (s : ℝ) ^ 2 else 0)
              ≤ ∑ s ∈ Finset.range T, (if 2 ≤ s then 2 / (s : ℝ) ^ 2 else 0) := by
                apply Finset.sum_le_sum; intro s _
                split_ifs with h1 h2 <;> first | exact le_rfl | (exfalso; omega) | positivity
            _ = 2 * ∑ s ∈ Finset.range (T - 2 + 2), (if 2 ≤ s then 1 / (s : ℝ) ^ 2 else 0) := by
                rw [show T - 2 + 2 = T by omega, Finset.mul_sum]
                refine Finset.sum_congr rfl (fun s _ => ?_)
                split_ifs <;> ring
            _ ≤ 2 * (1 - 1 / ((T - 2 : ℕ) + 1 : ℝ)) := by
                gcongr; exact sum_inv_sq_le (T - 2)
            _ ≤ 2 := by
                have : (0 : ℝ) ≤ 1 / ((T - 2 : ℕ) + 1 : ℝ) := by positivity
                linarith
      _ = ENNReal.ofReal ((θ : ℝ) + 2) := by
          rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num), ENNReal.ofReal_natCast]
  have hnn : ∀ h : LinParamBandits.LowerBound.History r T, 0 ≤ (LinParamBandits.UEFinite.pullCount u h : ℝ) :=
    fun h => Nat.cast_nonneg _
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn)
    (measurable_pullCount u T).aestronglyMeasurable]
  have hθ0 : (0 : ℝ) ≤ (θ : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) θ; linarith
  have h1 := ENNReal.toReal_le_of_le_ofReal hθ0 hlin
  have h2 : (θ : ℝ) ≤ x + 2 := by
    rw [hθ]; push_cast
    have := Nat.ceil_lt_add_one hx0
    linarith
  calc _ ≤ (θ : ℝ) + 2 := h1
    _ ≤ 6 + x := by linarith
