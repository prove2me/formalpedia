-- Prove2me | solution 1 for LassoDantzig.Lasso.theorem_7_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T08:26:23.080872+00:00
-- url     : https://prove2.me/submissions/c4fa2ef9-1cda-4610-a855-4033bb8d34b8

import Mathlib
import Definitions.Def_LassoDantzig_Lasso_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace LassoEfe
open LassoDantzig.Lasso

def sqNN (c : ℝ) : NNReal := ⟨c ^ 2, sq_nonneg c⟩

lemma law_lin {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hWm : ∀ i, Measurable (W i))
    (hWind : iIndepFun W P) (hWlaw : ∀ i, P.map (W i) = gaussianReal 0 (σ ^ 2).toNNReal)
    (c : Fin n → ℝ) (S : Finset (Fin n)) :
    P.map (fun ω => ∑ i ∈ S, c i * W i ω) =
      gaussianReal 0 (∑ i ∈ S, sqNN (c i) * (σ ^ 2).toNNReal) := by
  classical
  have hY : iIndepFun (fun i ω => c i * W i ω) P :=
    hWind.comp (fun i x => c i * x) (fun i => measurable_const.mul measurable_id)
  have hYm : ∀ i, Measurable (fun ω => c i * W i ω) := fun i => measurable_const.mul (hWm i)
  have hlaw1 : ∀ i, P.map (fun ω => c i * W i ω) =
      gaussianReal 0 (sqNN (c i) * (σ ^ 2).toNNReal) := by
    intro i
    have : (fun ω => c i * W i ω) = (fun x => c i * x) ∘ W i := rfl
    have hmul : Measurable (fun x : ℝ => c i * x) := by fun_prop
    rw [this, ← Measure.map_map hmul (hWm i), hWlaw i,
      gaussianReal_map_const_mul]
    simp only [mul_zero]
    rfl
  induction S using Finset.induction_on with
  | empty =>
    simp [Measure.map_const]
  | insert a S ha ih =>
    have hind := hY.indepFun_finsetSum_of_notMem hYm ha
    have hfun : (fun ω => ∑ i ∈ insert a S, c i * W i ω) =
        (∑ j ∈ S, (fun ω => c j * W j ω)) + (fun ω => c a * W a ω) := by
      funext ω; simp [Finset.sum_insert ha, Finset.sum_apply, add_comm]
    rw [hfun]
    have ih' : P.map (∑ j ∈ S, (fun ω => c j * W j ω)) =
        gaussianReal 0 (∑ i ∈ S, sqNN (c i) * (σ ^ 2).toNNReal) := by
      have : (∑ j ∈ S, (fun ω => c j * W j ω)) = (fun ω => ∑ i ∈ S, c i * W i ω) := by
        funext ω; simp [Finset.sum_apply]
      rw [this, ih]
    rw [gaussianReal_add_gaussianReal_of_indepFun hind ih' (hlaw1 a), Finset.sum_insert ha]
    simp [add_comm]

lemma tail_int (v : ℝ) (hv : 0 < v) (t : ℝ) :
    IntegrableOn (fun x => x * exp (-x ^ 2 / (2 * v))) (Set.Ioi t) ∧
    ∫ x in Set.Ioi t, x * exp (-x ^ 2 / (2 * v)) = v * exp (-t ^ 2 / (2 * v)) := by
  set g : ℝ → ℝ := fun x => -v * exp (-x ^ 2 / (2 * v)) with hg
  have hderiv : ∀ x ∈ Set.Ici t, HasDerivAt g (x * exp (-x ^ 2 / (2 * v))) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => -x ^ 2 / (2 * v)) (-(2 * x) / (2 * v)) x := by
      have := ((hasDerivAt_pow 2 x).neg).div_const (2 * v)
      simpa using this
    have h2 := (h1.exp).const_mul (-v)
    have hv0 : v ≠ 0 := hv.ne'
    refine h2.congr_deriv ?_
    rw [show -v * (exp (-x ^ 2 / (2 * v)) * (-(2 * x) / (2 * v)))
        = x * exp (-x ^ 2 / (2 * v)) * (v / v) by ring, div_self hv0, mul_one]
  have hlim : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => -x ^ 2 / (2 * v)) atTop atBot := by
      have := (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop (α := ℝ) two_ne_zero)).atBot_div_const
        (show (0:ℝ) < 2 * v by positivity)
      simpa [Function.comp] using this
    have h2 := (tendsto_exp_atBot.comp h1).const_mul (-v)
    simpa [hg, Function.comp] using h2
  -- integrability on Ioi t: split nonnegativity issue by using Ioi (max t 0)
  have hint : IntegrableOn (fun x => x * exp (-x ^ 2 / (2 * v))) (Set.Ioi t) := by
    have hfull : Integrable (fun x : ℝ => x * exp (-(1 / (2 * v)) * x ^ 2)) :=
      integrable_mul_exp_neg_mul_sq (by positivity)
    refine (hfull.congr ?_).integrableOn
    exact Eventually.of_forall (fun x => by
      ring_nf)
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  simp [hg]

lemma gauss_tail (v : NNReal) (hv : v ≠ 0) (t : ℝ) (ht : 0 < t) (htv : 2 * (v : ℝ) / π ≤ t ^ 2) :
    gaussianReal 0 v {x | t < |x|} ≤ ENNReal.ofReal (exp (-t ^ 2 / (2 * v))) := by
  have hv' : (0 : ℝ) < v := by positivity
  set μ := gaussianReal 0 v with hμ
  have hsub : {x : ℝ | t < |x|} ⊆ Set.Ioi t ∪ (fun x => -x) ⁻¹' Set.Ioi t := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    rcases lt_abs.mp hx with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hneg : μ ((fun x => -x) ⁻¹' Set.Ioi t) = μ (Set.Ioi t) := by
    rw [← Measure.map_apply measurable_neg measurableSet_Ioi, hμ, gaussianReal_map_neg, neg_zero]
  set I := ∫ x in Set.Ioi t, gaussianPDFReal 0 v x with hI
  have hIoi : μ (Set.Ioi t) = ENNReal.ofReal I := gaussianReal_apply_eq_integral 0 hv _
  obtain ⟨hint, hval⟩ := tail_int v hv' t
  have hIle : I ≤ (√(2 * π * v))⁻¹ * (1 / t) * (v * exp (-t ^ 2 / (2 * v))) := by
    rw [hI, ← hval, ← integral_const_mul]
    refine setIntegral_mono_on (integrable_gaussianPDFReal 0 v).integrableOn
      (hint.const_mul _) measurableSet_Ioi ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    rw [gaussianPDFReal]
    simp only [sub_zero]
    have hxt : 1 ≤ 1 / t * x := by rw [one_div, inv_mul_eq_div, one_le_div ht]; linarith
    have hpos : 0 ≤ (√(2 * π * v))⁻¹ * exp (-x ^ 2 / (2 * v)) := by positivity
    calc (√(2 * π * v))⁻¹ * exp (-x ^ 2 / (2 * v))
        = 1 * ((√(2 * π * v))⁻¹ * exp (-x ^ 2 / (2 * v))) := by ring
      _ ≤ (1 / t * x) * ((√(2 * π * v))⁻¹ * exp (-x ^ 2 / (2 * v))) :=
          mul_le_mul_of_nonneg_right hxt hpos
      _ = (√(2 * π * v))⁻¹ * (1 / t) * (x * exp (-x ^ 2 / (2 * v))) := by ring
  have hkey : 2 * ((√(2 * π * v))⁻¹ * (1 / t) * (v * exp (-t ^ 2 / (2 * v))))
      ≤ exp (-t ^ 2 / (2 * v)) := by
    have hs : 2 * (v : ℝ) / t ≤ √(2 * π * v) := by
      apply Real.le_sqrt_of_sq_le
      rw [div_pow]
      rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left htv (show (0:ℝ) ≤ 2 * π * v by positivity)
      have hpi : 0 < π := pi_pos
      field_simp at this ⊢
      nlinarith [this]
    have hsq : 0 < √(2 * π * v) := Real.sqrt_pos.mpr (by positivity)
    have he : 0 < exp (-t ^ 2 / (2 * v)) := exp_pos _
    rw [show 2 * ((√(2 * π * v))⁻¹ * (1 / t) * (v * exp (-t ^ 2 / (2 * v))))
        = (2 * v / t) / √(2 * π * v) * exp (-t ^ 2 / (2 * v)) by field_simp]
    have : (2 * v / t) / √(2 * π * v) ≤ 1 := (div_le_one hsq).mpr hs
    nlinarith
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Ioi (fun x _ => gaussianPDFReal_nonneg _ _ x)
  calc μ {x | t < |x|} ≤ μ (Set.Ioi t ∪ (fun x => -x) ⁻¹' Set.Ioi t) := measure_mono hsub
    _ ≤ μ (Set.Ioi t) + μ ((fun x => -x) ⁻¹' Set.Ioi t) := measure_union_le _ _
    _ = ENNReal.ofReal (2 * I) := by
        rw [hneg, hIoi, ← ENNReal.ofReal_add hI0 hI0]; ring_nf
    _ ≤ ENNReal.ofReal (exp (-t ^ 2 / (2 * v))) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith


lemma mv {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (x : Fin M → ℝ) (i : Fin n) :
    X.mulVec x i = ∑ j, X i j * x j := rfl

lemma cross {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (w : Fin n → ℝ) (δ : Fin M → ℝ) :
    ∑ i, w i * X.mulVec δ i = ∑ j, δ j * ∑ i, X i j * w i := by
  simp_rw [mv, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))

lemma l1_split {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) :
    l1Norm δ = l1On δ J + l1On δ Jᶜ := by
  unfold l1Norm l1On
  rw [Finset.sum_add_sum_compl]

lemma l1_le_sqrt_card {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) :
    l1On δ J ≤ √(J.card : ℝ) * l2On δ J := by
  unfold l1On l2On
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  apply Real.le_sqrt_of_sq_le
  have := sq_sum_le_card_mul_sum_sq (s := J) (f := fun j => |δ j|)
  simpa [sq_abs] using this

lemma l1On_nonneg {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) : 0 ≤ l1On δ J :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma basic {n M : ℕ} (hn : 0 < (n : ℝ)) (X : Matrix (Fin n) (Fin M) ℝ)
    (βstar βhat : Fin M → ℝ) (w : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (hnoise : NoiseEventHalf X r w)
    (hL : IsLasso X (fun i => X.mulVec βstar i + w i) r βhat) :
    (1 / (n : ℝ)) * ∑ i, (X.mulVec (βhat - βstar) i) ^ 2 +
        r * (l1On (βhat - βstar) (supp βstar) + l1On (βhat - βstar) (supp βstar)ᶜ)
      ≤ 4 * r * l1On (βhat - βstar) (supp βstar) := by
  set δ := βhat - βstar with hδ
  set J := supp βstar with hJ
  have h := hL βstar
  have e1 : ∀ i, X.mulVec βstar i + w i - X.mulVec βhat i = w i - X.mulVec δ i := by
    intro i; simp only [hδ, Matrix.mulVec_sub, Pi.sub_apply]; ring
  have e2 : ∀ i, X.mulVec βstar i + w i - X.mulVec βstar i = w i := by intro i; ring
  simp only [e1, e2] at h
  set Q := ∑ i, (X.mulVec δ i) ^ 2 with hQ
  set C := ∑ i, w i * X.mulVec δ i with hC
  have hexp : ∑ i, (w i - X.mulVec δ i) ^ 2 = ∑ i, w i ^ 2 - 2 * C + Q := by
    have : ∀ i, (w i - X.mulVec δ i) ^ 2 = w i ^ 2 - 2 * (w i * X.mulVec δ i) + (X.mulVec δ i) ^ 2 := by
      intro i; ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hexp] at h
  have hdist : (1 / (n : ℝ)) * (∑ i, w i ^ 2 - 2 * C + Q) =
      (1 / (n : ℝ)) * ∑ i, w i ^ 2 - 2 * ((1 / (n : ℝ)) * C) + (1 / (n : ℝ)) * Q := by ring
  rw [hdist] at h
  -- cross term
  have hCb : (1 / (n : ℝ)) * C ≤ r / 2 * l1Norm δ := by
    rw [hC, cross, Finset.mul_sum, l1Norm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hj := hnoise j
    have : (1 / (n : ℝ)) * (δ j * ∑ i, X i j * w i) = δ j * ((1 / (n : ℝ)) * ∑ i, X i j * w i) := by ring
    rw [this]
    calc δ j * ((1 / (n : ℝ)) * ∑ i, X i j * w i)
        ≤ |δ j * ((1 / (n : ℝ)) * ∑ i, X i j * w i)| := le_abs_self _
      _ = |δ j| * |(1 / (n : ℝ)) * ∑ i, X i j * w i| := abs_mul _ _
      _ ≤ |δ j| * (r / 2) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = r / 2 * |δ j| := by ring
  -- l1 difference
  have hdiff : l1Norm βstar - l1Norm βhat ≤ l1On δ J - l1On δ Jᶜ := by
    rw [l1_split βstar J, l1_split βhat J]
    have h1 : l1On βstar J - l1On βhat J ≤ l1On δ J := by
      unfold l1On
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro j _
      have := abs_sub_abs_le_abs_sub (βstar j) (βhat j)
      rw [abs_sub_comm] at this
      simpa [hδ] using this
    have h2 : l1On βstar Jᶜ - l1On βhat Jᶜ = - l1On δ Jᶜ := by
      unfold l1On
      rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have : βstar j = 0 := by
        rw [Finset.mem_compl, hJ, supp, Finset.mem_filter] at hj
        simpa using hj
      simp [hδ, this]
    linarith
  have hsplit := l1_split δ J
  have hm1 : 2 * r * (l1Norm βstar - l1Norm βhat) ≤ 2 * r * (l1On δ J - l1On δ Jᶜ) :=
    mul_le_mul_of_nonneg_left hdiff (by linarith)
  have hm2 : r / 2 * l1Norm δ = r / 2 * (l1On δ J + l1On δ Jᶜ) := by rw [hsplit]
  nlinarith [hm1, hm2, hCb, h]

lemma core (r κ s q a b : ℝ) (hr : 0 < r) (hκ : 0 < κ) (hs : 0 ≤ s) (hq : 0 ≤ q)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1 : q ^ 2 + r * (a + b) ≤ 4 * r * a) (h2 : κ * a ≤ √s * q) :
    κ * q ≤ 4 * r * √s ∧ κ ^ 2 * (a + b) ≤ 16 * r * s := by
  have hss := Real.sq_sqrt hs
  have hss0 := Real.sqrt_nonneg s
  have k1 : κ * q ^ 2 ≤ 4 * r * √s * q := by
    have e1 := mul_le_mul_of_nonneg_left h1 hκ.le
    have e2 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 4 * r by linarith)
    have e3 : 0 ≤ κ * (r * (a + b)) := by positivity
    nlinarith
  have k2 : κ * q ≤ 4 * r * √s := by
    rcases hq.eq_or_lt with h0 | h0
    · rw [← h0]; simp; positivity
    · have : q * (κ * q) ≤ q * (4 * r * √s) := by nlinarith
      exact le_of_mul_le_mul_left this h0
  refine ⟨k2, ?_⟩
  have k3 : r * (κ ^ 2 * (a + b)) ≤ r * (16 * r * s) := by
    have e1 : κ ^ 2 * (r * (a + b)) ≤ κ ^ 2 * (4 * r * a - q ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e2 : κ ^ 2 * q ^ 2 ≥ 0 := by positivity
    have e3 : 4 * r * κ * (κ * a) ≤ 4 * r * κ * (√s * q) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have e4 : 4 * r * √s * (κ * q) ≤ 4 * r * √s * (4 * r * √s) :=
      mul_le_mul_of_nonneg_left k2 (by positivity)
    have e5 : 4 * r * √s * (4 * r * √s) = 16 * r * r * s := by
      rw [show 4 * r * √s * (4 * r * √s) = 16 * r * r * (√s ^ 2) by ring, hss]
    nlinarith [e1, e2, e3, e4, e5]
  exact le_of_mul_le_mul_left k3 hr

/-- Deterministic consequences on the noise event: the shared quantities. -/
lemma det_q {n M : ℕ} (hn : 0 < (n : ℝ)) (X : Matrix (Fin n) (Fin M) ℝ)
    (βstar βhat : Fin M → ℝ) (w : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (hnoise : NoiseEventHalf X r w)
    (hL : IsLasso X (fun i => X.mulVec βstar i + w i) r βhat)
    (s : ℕ) (hsparse : sparsity βstar ≤ s) (κ : ℝ) (hκ : 0 < κ)
    (L : ℝ) (hL0 : l2On (βhat - βstar) (supp βstar) ≤ L)
    (hREL : βhat - βstar ≠ 0 → ConeCond 3 (supp βstar) (βhat - βstar) →
      κ * √n * L ≤ euclNorm (X.mulVec (βhat - βstar))) :
    κ * (√(∑ i, (X.mulVec (βhat - βstar) i) ^ 2) / √n) ≤ 4 * r * √s ∧
    κ ^ 2 * l1Norm (βhat - βstar) ≤ 16 * r * s ∧
    l1On (βhat - βstar) (supp βstar)ᶜ ≤ 3 * l1On (βhat - βstar) (supp βstar) ∧
    l1On (βhat - βstar) (supp βstar) ≤ √s * L := by
  set δ := βhat - βstar with hδ
  set J := supp βstar with hJ
  set Q := ∑ i, (X.mulVec δ i) ^ 2 with hQ
  have hb := basic hn X βstar βhat w r hr hnoise hL
  rw [← hδ, ← hJ, ← hQ] at hb
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  set q := √Q / √n with hq
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn
  have hq2 : q ^ 2 = (1 / (n : ℝ)) * Q := by
    rw [hq, div_pow, Real.sq_sqrt hQ0, Real.sq_sqrt hn.le]; ring
  have hq0 : 0 ≤ q := by positivity
  have ha0 := l1On_nonneg δ J
  have hb0 := l1On_nonneg δ Jᶜ
  have hcone : l1On δ Jᶜ ≤ 3 * l1On δ J := by
    have : 0 ≤ (1 / (n : ℝ)) * Q := by positivity
    nlinarith
  have hcard : (J.card : ℝ) ≤ s := by exact_mod_cast hsparse
  have haL0 : l1On δ J ≤ √s * l2On δ J :=
    (l1_le_sqrt_card δ J).trans (mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt hcard) (Real.sqrt_nonneg _))
  have haL : l1On δ J ≤ √s * L :=
    haL0.trans (mul_le_mul_of_nonneg_left hL0 (Real.sqrt_nonneg _))
  have h2 : κ * l1On δ J ≤ √s * q := by
    by_cases h0 : δ = 0
    · have : l1On δ J = 0 := by simp [l1On, h0]
      rw [this, mul_zero]; positivity
    · have hre := hREL h0 hcone
      have hκL : κ * L ≤ q := by
        rw [hq, le_div_iff₀ hsn]
        unfold euclNorm at hre
        linarith [hre]
      calc κ * l1On δ J ≤ κ * (√s * L) := mul_le_mul_of_nonneg_left haL hκ.le
        _ = √s * (κ * L) := by ring
        _ ≤ √s * q := mul_le_mul_of_nonneg_left hκL (Real.sqrt_nonneg _)
  have h1 : q ^ 2 + r * (l1On δ J + l1On δ Jᶜ) ≤ 4 * r * l1On δ J := by rw [hq2]; exact hb
  obtain ⟨c1, c2⟩ := core r κ s q _ _ hr hκ (Nat.cast_nonneg _) hq0 ha0 hb0 h1 h2
  refine ⟨c1, ?_, hcone, haL⟩
  rw [l1_split δ J]; exact c2


lemma mv' {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (x : Fin M → ℝ) (i : Fin n) :
    X.mulVec x i = ∑ j, X i j * x j := rfl

lemma kkt {n M : ℕ} (hn : 0 < (n : ℝ)) (X : Matrix (Fin n) (Fin M) ℝ) (hX : UnitDiag X)
    (y : Fin n → ℝ) (r : ℝ) (βhat : Fin M → ℝ) (hL : IsLasso X y r βhat) (j : Fin M)
    (hj : βhat j ≠ 0) :
    r ≤ |(1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec βhat i)| := by
  classical
  set g := (1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec βhat i) with hg
  set b := βhat j with hb
  have key : ∀ t : ℝ, 0 ≤ -2 * t * g + t ^ 2 + 2 * r * (|b + t| - |b|) := by
    intro t
    have h := hL (βhat + Pi.single j t)
    have hmv : ∀ i, X.mulVec (βhat + Pi.single j t) i = X.mulVec βhat i + X i j * t := by
      intro i
      rw [Matrix.mulVec_add, Pi.add_apply]
      congr 1
      rw [mv']
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk; simp [Pi.single_apply, hk]
      · simp
    have hl1 : l1Norm (βhat + Pi.single j t) = l1Norm βhat + (|b + t| - |b|) := by
      unfold l1Norm
      have : ∑ k, |(βhat + Pi.single j t : Fin M → ℝ) k| - ∑ k, |βhat k| = |b + t| - |b| := by
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
        · simp [hb]
        · intro k _ hk; simp [Pi.single_apply, hk]
        · simp
      linarith
    simp only [hmv, hl1] at h
    have hsq : ∀ i, (y i - (X.mulVec βhat i + X i j * t)) ^ 2 =
        (y i - X.mulVec βhat i) ^ 2 - 2 * t * (X i j * (y i - X.mulVec βhat i)) + t ^ 2 * X i j ^ 2 := by
      intro i; ring
    simp_rw [hsq] at h
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h
    have hu := hX j
    have : (1 / (n : ℝ)) * (∑ i, (y i - X.mulVec βhat i) ^ 2 - 2 * t * ∑ i, X i j * (y i - X.mulVec βhat i)
        + t ^ 2 * ∑ i, X i j ^ 2) = (1 / (n : ℝ)) * ∑ i, (y i - X.mulVec βhat i) ^ 2
          - 2 * t * g + t ^ 2 * ((1 / (n : ℝ)) * ∑ i, X i j ^ 2) := by rw [hg]; ring
    rw [this, hu] at h
    nlinarith
  rcases lt_or_gt_of_ne hj with hneg | hpos
  · -- b < 0 : show -g ≥ r
    have : r ≤ -g := by
      by_contra hc
      rw [not_le] at hc
      set ε := min (-b) (r + g) with hε
      have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
      have hε1 : ε ≤ -b := min_le_left _ _
      have hε2 : ε ≤ r + g := min_le_right _ _
      have k := key ε
      have e1 : |b + ε| = -(b + ε) := abs_of_nonpos (by linarith)
      have e2 : |b| = -b := abs_of_neg hneg
      rw [e1, e2] at k
      nlinarith
    exact this.trans (neg_le_abs g)
  · have : r ≤ g := by
      by_contra hc
      rw [not_le] at hc
      set ε := min b (r - g) with hε
      have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
      have hε1 : ε ≤ b := min_le_left _ _
      have hε2 : ε ≤ r - g := min_le_right _ _
      have k := key (-ε)
      have e1 : |b + -ε| = b - ε := abs_of_nonneg (by linarith)
      have e2 : |b| = b := abs_of_pos hpos
      rw [e1, e2] at k
      nlinarith
    exact this.trans (le_abs_self g)

lemma phi_bdd {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) :
    BddAbove {t : ℝ | ∃ x : Fin M → ℝ, ∑ j, x j ^ 2 = 1 ∧
      t = (1 / (n : ℝ)) * ∑ i, (X.mulVec x i) ^ 2} := by
  refine ⟨(1 / (n : ℝ)) * ∑ i, ∑ j, X i j ^ 2, ?_⟩
  rintro t ⟨x, hx, rfl⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro i _
  rw [mv']
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => X i j) x
  rw [hx, mul_one] at this
  exact this

lemma phi_nonneg {n M : ℕ} (hM : 1 ≤ M) (X : Matrix (Fin n) (Fin M) ℝ) : 0 ≤ phiMax X := by
  classical
  unfold phiMax
  set x : Fin M → ℝ := Pi.single ⟨0, hM⟩ 1
  have hx : ∑ j, x j ^ 2 = 1 := by
    rw [Finset.sum_eq_single ⟨0, hM⟩]
    · simp [x]
    · intro k _ hk; simp [x, Pi.single_apply, hk]
    · simp
  have hmem : (1 / (n : ℝ)) * ∑ i, (X.mulVec x i) ^ 2 ∈ {t : ℝ | ∃ x : Fin M → ℝ, ∑ j, x j ^ 2 = 1 ∧
      t = (1 / (n : ℝ)) * ∑ i, (X.mulVec x i) ^ 2} := ⟨x, hx, rfl⟩
  exact le_trans (by positivity) (le_csSup (phi_bdd X) hmem)

lemma rayleigh {n M : ℕ} (hn : 0 < (n : ℝ)) (hM : 1 ≤ M) (X : Matrix (Fin n) (Fin M) ℝ)
    (x : Fin M → ℝ) :
    ∑ i, (X.mulVec x i) ^ 2 ≤ n * phiMax X * ∑ j, x j ^ 2 := by
  set N2 := ∑ j, x j ^ 2 with hN2
  have hN0 : 0 ≤ N2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rcases hN0.eq_or_lt with h0 | hpos
  · have hx0 : ∀ j, x j = 0 := by
      intro j
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x j))).mp h0.symm j
        (Finset.mem_univ _)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    have : ∀ i, X.mulVec x i = 0 := by intro i; simp [mv', hx0]
    simp [this, ← h0]
  · set N := √N2 with hN
    have hNpos : 0 < N := Real.sqrt_pos.mpr hpos
    have hNsq : N ^ 2 = N2 := Real.sq_sqrt hN0
    set y : Fin M → ℝ := fun j => x j / N
    have hy : ∑ j, y j ^ 2 = 1 := by
      simp only [y, div_pow]
      rw [← Finset.sum_div, hNsq, ← hN2, div_self hpos.ne']
    have hmem : (1 / (n : ℝ)) * ∑ i, (X.mulVec y i) ^ 2 ∈ {t : ℝ | ∃ x : Fin M → ℝ,
        ∑ j, x j ^ 2 = 1 ∧ t = (1 / (n : ℝ)) * ∑ i, (X.mulVec x i) ^ 2} := ⟨y, hy, rfl⟩
    have hle := le_csSup (phi_bdd X) hmem
    have hXy : ∀ i, X.mulVec y i = X.mulVec x i / N := by
      intro i; simp only [mv', y, mul_div_assoc', Finset.sum_div]
    simp only [hXy, div_pow] at hle
    rw [← Finset.sum_div, hNsq] at hle
    unfold phiMax
    rw [show (1 / (n : ℝ)) * ((∑ i, (X.mulVec x i) ^ 2) / N2) =
      (∑ i, (X.mulVec x i) ^ 2) / (n * N2) by field_simp] at hle
    rw [div_le_iff₀ (by positivity)] at hle
    linarith

lemma opbound {n M : ℕ} (hn : 0 < (n : ℝ)) (hM : 1 ≤ M) (X : Matrix (Fin n) (Fin M) ℝ)
    (u : Fin n → ℝ) :
    ∑ j, (∑ i, X i j * u i) ^ 2 ≤ n * phiMax X * ∑ i, u i ^ 2 := by
  set z : Fin M → ℝ := fun j => ∑ i, X i j * u i with hz
  set Z := ∑ j, z j ^ 2 with hZ
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hphi := phi_nonneg hM X
  have hU0 : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hZeq : Z = ∑ i, u i * X.mulVec z i := by
    rw [hZ]
    simp_rw [mv', Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [sq, hz]; simp only
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _; ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u (fun i => X.mulVec z i)
  rw [← hZeq] at hcs
  have hray := rayleigh hn hM X z
  rw [← hZ] at hray
  change Z ≤ n * phiMax X * ∑ i, u i ^ 2
  rcases hZ0.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have : Z * Z ≤ Z * (n * phiMax X * ∑ i, u i ^ 2) := by
      have e := mul_le_mul_of_nonneg_left hray hU0
      nlinarith
    exact le_of_mul_le_mul_left this hpos


lemma top_exists {M : ℕ} (δ : Fin M → ℝ) (S : Finset (Fin M)) (m : ℕ) (hm : m ≤ S.card) :
    ∃ J1 ⊆ S, J1.card = m ∧ ∀ j ∈ J1, ∀ k ∈ S \ J1, |δ k| ≤ |δ j| := by
  classical
  induction m with
  | zero => exact ⟨∅, Finset.empty_subset _, Finset.card_empty, by simp⟩
  | succ m ih =>
    obtain ⟨J1, hsub, hcard, hprop⟩ := ih (by omega)
    have hne : (S \ J1).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff_of_subset hsub]; omega
    obtain ⟨k0, hk0, hmax⟩ := Finset.exists_max_image (S \ J1) (fun k => |δ k|) hne
    have hk0S : k0 ∈ S := (Finset.mem_sdiff.mp hk0).1
    have hk0J : k0 ∉ J1 := (Finset.mem_sdiff.mp hk0).2
    refine ⟨insert k0 J1, Finset.insert_subset hk0S hsub, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hk0J, hcard]
    · intro j hj k hk
      have hkS : k ∈ S := (Finset.mem_sdiff.mp hk).1
      have hkI : k ∉ insert k0 J1 := (Finset.mem_sdiff.mp hk).2
      have hkJ : k ∉ J1 := fun h => hkI (Finset.mem_insert_of_mem h)
      have hkSJ : k ∈ S \ J1 := Finset.mem_sdiff.mpr ⟨hkS, hkJ⟩
      rcases Finset.mem_insert.mp hj with rfl | hjJ
      · exact hmax k hkSJ
      · exact hprop j hjJ k hkSJ

lemma tail_bound {M : ℕ} (δ : Fin M → ℝ) (J0 J1 : Finset (Fin M)) (m : ℕ) (hm : 0 < m)
    (hT : IsTopOutside m J0 δ J1) :
    ∑ k ∈ (J0 ∪ J1)ᶜ, δ k ^ 2 ≤ (l1On δ J0ᶜ) ^ 2 / m := by
  classical
  obtain ⟨hsub, hcard, hprop⟩ := hT
  set b := l1On δ J0ᶜ with hb
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hJ1b : ∑ j ∈ J1, |δ j| ≤ b :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
  have hpt : ∀ k ∈ (J0 ∪ J1)ᶜ, |δ k| ≤ b / m := by
    intro k hk
    have hk' : k ∈ J0ᶜ \ J1 := by
      simp only [Finset.mem_compl, Finset.mem_union, not_or] at hk
      simp [hk.1, hk.2]
    have : ∑ j ∈ J1, |δ k| ≤ ∑ j ∈ J1, |δ j| :=
      Finset.sum_le_sum (fun j hj => hprop j hj k hk')
    rw [Finset.sum_const, hcard, nsmul_eq_mul] at this
    rw [le_div_iff₀ hmR]; linarith
  have hsubc : (J0 ∪ J1)ᶜ ⊆ J0ᶜ := Finset.compl_subset_compl.mpr Finset.subset_union_left
  have hrest : ∑ k ∈ (J0 ∪ J1)ᶜ, |δ k| ≤ b :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubc (fun _ _ _ => abs_nonneg _)
  have hb0 : 0 ≤ b := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  calc ∑ k ∈ (J0 ∪ J1)ᶜ, δ k ^ 2 = ∑ k ∈ (J0 ∪ J1)ᶜ, |δ k| * |δ k| := by
        apply Finset.sum_congr rfl; intro k _; rw [abs_mul_abs_self, sq]
    _ ≤ ∑ k ∈ (J0 ∪ J1)ᶜ, b / m * |δ k| :=
        Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_right (hpt k hk) (abs_nonneg _))
    _ = b / m * ∑ k ∈ (J0 ∪ J1)ᶜ, |δ k| := by rw [Finset.mul_sum]
    _ ≤ b / m * b := mul_le_mul_of_nonneg_left hrest (by positivity)
    _ = b ^ 2 / m := by ring

lemma l2_split {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) :
    ∑ j, δ j ^ 2 = (l2On δ J) ^ 2 + ∑ k ∈ Jᶜ, δ k ^ 2 := by
  unfold l2On
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)), Finset.sum_add_sum_compl]

lemma l2On_mono {M : ℕ} (δ : Fin M → ℝ) {J K : Finset (Fin M)} (h : J ⊆ K) :
    l2On δ J ≤ l2On δ K := by
  unfold l2On
  exact Real.sqrt_le_sqrt (Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => sq_nonneg _))

lemma holder_interp {M : ℕ} (δ : Fin M → ℝ) (p : ℝ) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∑ j, |δ j| ^ p ≤ (∑ j, |δ j|) ^ (2 - p) * (∑ j, δ j ^ 2) ^ (p - 1) := by
  have hP : 1 ≤ (p - 1)⁻¹ := (one_le_inv₀ (by linarith)).mpr (by linarith)
  have h := inner_le_weight_mul_Lp_of_nonneg Finset.univ hP (fun j => |δ j|)
    (fun j => |δ j| ^ (p - 1)) (fun j => abs_nonneg _) (fun j => by positivity)
  have e1 : ∀ j, |δ j| * |δ j| ^ (p - 1) = |δ j| ^ p := by
    intro j
    rcases (abs_nonneg (δ j)).eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul, Real.zero_rpow (by linarith)]
    · rw [show p = 1 + (p - 1) by ring, Real.rpow_add hpos, Real.rpow_one]; ring_nf
  have e2 : ∀ j, |δ j| * (|δ j| ^ (p - 1)) ^ (p - 1)⁻¹ = δ j ^ 2 := by
    intro j
    rw [Real.rpow_rpow_inv (abs_nonneg _) (by linarith), abs_mul_abs_self, sq]
  simp only [e1, e2, inv_inv] at h
  rw [show (2 : ℝ) - p = 1 - (p - 1) by ring]
  exact h

lemma rpow_alg (s u C p : ℝ) (hs : 0 < s) (hu : 0 < u) (hC : 0 < C) :
    (16 * s * u) ^ (2 - p) * (16 * s * C ^ 2 * u ^ 2) ^ (p - 1) =
      16 * C ^ (2 * (p - 1)) * s * u ^ p := by
  have hK : 0 < 16 * s * u := by positivity
  have e1 : (16 * s * C ^ 2 * u ^ 2) ^ (p - 1) = (16 * s * u) ^ (p - 1) * (C ^ 2 * u) ^ (p - 1) := by
    rw [← Real.mul_rpow hK.le (by positivity)]; congr 1; ring
  have e2 : (16 * s * u) ^ (2 - p) * (16 * s * u) ^ (p - 1) = 16 * s * u := by
    rw [← Real.rpow_add hK, show 2 - p + (p - 1) = (1 : ℝ) by ring, Real.rpow_one]
  have e3 : (C ^ 2 * u) ^ (p - 1) = C ^ (2 * (p - 1)) * u ^ (p - 1) := by
    rw [Real.mul_rpow (by positivity) hu.le, Real.rpow_mul hC.le, Real.rpow_two]
  have e4 : u ^ p = u * u ^ (p - 1) := by
    conv_lhs => rw [show p = 1 + (p - 1) by ring]
    rw [Real.rpow_add hu, Real.rpow_one]
  rw [e1, ← mul_assoc, e2, e3, e4]; ring

lemma lp_final {M : ℕ} (δ : Fin M → ℝ) (p s u C : ℝ) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (hs : 0 < s) (hu : 0 < u) (hC : 0 < C)
    (h1 : l1Norm δ ≤ 16 * s * u) (h2 : ∑ j, δ j ^ 2 ≤ 16 * s * C ^ 2 * u ^ 2) :
    ∑ j, |δ j| ^ p ≤ 16 * C ^ (2 * (p - 1)) * s * u ^ p := by
  have hA0 : 0 ≤ ∑ j, |δ j| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hB0 : 0 ≤ ∑ j, δ j ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc ∑ j, |δ j| ^ p ≤ (∑ j, |δ j|) ^ (2 - p) * (∑ j, δ j ^ 2) ^ (p - 1) :=
        holder_interp δ p hp1 hp2
    _ ≤ (16 * s * u) ^ (2 - p) * (16 * s * C ^ 2 * u ^ 2) ^ (p - 1) :=
        mul_le_mul (Real.rpow_le_rpow hA0 h1 (by linarith))
          (Real.rpow_le_rpow hB0 h2 (by linarith)) (by positivity) (by positivity)
    _ = 16 * C ^ (2 * (p - 1)) * s * u ^ p := rpow_alg s u C p hs hu hC

lemma cfac (L s m : ℝ) (hs : 0 ≤ s) (hm : 0 < m) :
    L ^ 2 + 9 * s * L ^ 2 / m ≤ (1 + 3 * √(s / m)) ^ 2 * L ^ 2 := by
  have h := Real.sq_sqrt (div_nonneg hs hm.le)
  have h0 := Real.sqrt_nonneg (s / m)
  have : 9 * s * L ^ 2 / m = 9 * (s / m) * L ^ 2 := by ring
  rw [this]
  nlinarith [sq_nonneg L, mul_nonneg h0 (sq_nonneg L)]

lemma sqNN_coe (c : ℝ) : ((sqNN c : NNReal) : ℝ) = c ^ 2 := rfl

lemma event_prob {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M) (X : Matrix (Fin n) (Fin M) ℝ)
    (hX : UnitDiag X)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hWm : ∀ i, Measurable (W i))
    (hWind : iIndepFun W P) (hWlaw : ∀ i, P.map (W i) = gaussianReal 0 (σ ^ 2).toNNReal)
    (A : ℝ) (hA : 2 * Real.sqrt 2 < A) (r : ℝ)
    (hr : r = A * σ * Real.sqrt (Real.log M / n)) :
    MeasurableSet {ω | NoiseEventHalf X r (fun i => W i ω)} ∧
    1 - (M : ℝ) ^ (1 - A ^ 2 / 8) ≤ (P {ω | NoiseEventHalf X r (fun i => W i ω)}).toReal := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hlogM : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) hMR
  have hlog2 := Real.log_two_gt_d9
  have hlogpos : 0 < Real.log M := by linarith
  have hA2 : 8 < A ^ 2 := by
    have h8 : (2 * √2) ^ 2 = 8 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
    have hpos : 0 ≤ 2 * √2 := by positivity
    nlinarith
  have hr2 : r ^ 2 = A ^ 2 * σ ^ 2 * (Real.log M / n) := by
    rw [hr, mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hlogpos.le hnR.le)]
  have hApos : 0 < A := by
    have : 0 ≤ 2 * √2 := by positivity
    linarith
  have hrpos : 0 < r := by
    rw [hr]; have := Real.sqrt_pos.mpr (div_pos hlogpos hnR); positivity
  set V : Fin M → Ω → ℝ := fun j ω => ∑ i, (X i j / n) * W i ω with hV
  have hVeq : ∀ j ω, (1 / (n : ℝ)) * ∑ i, X i j * W i ω = V j ω := by
    intro j ω; simp only [hV, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  have hVm : ∀ j, Measurable (V j) := fun j =>
    Finset.measurable_sum _ (fun i _ => (hWm i).const_mul _)
  set E := {ω | NoiseEventHalf X r (fun i => W i ω)} with hEdef
  have hE : E = ⋂ j, {ω | 2 * |V j ω| ≤ r} := by
    ext ω
    simp only [hEdef, NoiseEventHalf, Set.mem_iInter, Set.mem_setOf_eq, hVeq]
  have hEm : MeasurableSet E := by
    rw [hE]
    exact MeasurableSet.iInter (fun j => measurableSet_le
      ((continuous_abs.measurable.comp (hVm j)).const_mul 2) measurable_const)
  refine ⟨hEm, ?_⟩
  -- variance of each projection
  set vj : Fin M → NNReal := fun j => ∑ i, sqNN (X i j / n) * (σ ^ 2).toNNReal with hvjdef
  have hlaw : ∀ j, P.map (V j) = gaussianReal 0 (vj j) := fun j =>
    law_lin P W σ hWm hWind hWlaw (fun i => X i j / n) Finset.univ
  have hvj : ∀ j, ((vj j : NNReal) : ℝ) = σ ^ 2 / n := by
    intro j
    simp only [hvjdef, NNReal.coe_sum, NNReal.coe_mul, sqNN_coe,
      Real.coe_toNNReal _ (sq_nonneg σ)]
    have hsum : ∑ i, X i j ^ 2 = n := by
      have := hX j
      field_simp at this
      linarith
    have : ∑ i, (X i j / n) ^ 2 * σ ^ 2 = σ ^ 2 / (n : ℝ) ^ 2 * ∑ i, X i j ^ 2 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [this, hsum]; field_simp
  have hvpos : ∀ j, (0 : ℝ) < vj j := by intro j; rw [hvj j]; positivity
  have hvne : ∀ j, vj j ≠ 0 := by
    intro j h; have := hvpos j; rw [h] at this; simp at this
  -- the tail of each coordinate
  have hprod : 8 ≤ A ^ 2 * Real.log M * π := by
    have h1 : 8 * 0.69 ≤ A ^ 2 * Real.log M := by nlinarith
    have h3 := Real.pi_gt_three
    nlinarith
  have hexp : Real.exp (-(r / 2) ^ 2 / (2 * (σ ^ 2 / n))) = (M : ℝ) ^ (-(A ^ 2) / 8) := by
    rw [Real.rpow_def_of_pos hM0, div_pow, hr2]
    congr 1
    field_simp
    ring
  have htail : ∀ j, P {ω | r < 2 * |V j ω|} ≤ ENNReal.ofReal ((M : ℝ) ^ (-(A ^ 2) / 8)) := by
    intro j
    have hset : {ω | r < 2 * |V j ω|} = V j ⁻¹' {x | r / 2 < |x|} := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage]
      constructor <;> intro h <;> linarith
    rw [hset, ← Measure.map_apply (hVm j)
      (measurableSet_lt measurable_const continuous_abs.measurable), hlaw j]
    have htv : 2 * ((vj j : NNReal) : ℝ) / π ≤ (r / 2) ^ 2 := by
      rw [hvj j, div_le_iff₀ Real.pi_pos, div_pow, hr2]
      have ht : 0 < σ ^ 2 / (n : ℝ) := by positivity
      have : A ^ 2 * σ ^ 2 * (Real.log M / n) / 2 ^ 2 * π =
          σ ^ 2 / n * (A ^ 2 * Real.log M * π) / 4 := by ring
      rw [this]
      nlinarith
    refine (gauss_tail (vj j) (hvne j) (r / 2) (by linarith) htv).trans ?_
    rw [hvj j, hexp]
  have hcomp : Eᶜ = ⋃ j, {ω | r < 2 * |V j ω|} := by
    rw [hE, Set.compl_iInter]
    congr 1; ext j ω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  have hEc : P Eᶜ ≤ ENNReal.ofReal ((M : ℝ) ^ (1 - A ^ 2 / 8)) := by
    rw [hcomp]
    calc P (⋃ j, {ω | r < 2 * |V j ω|}) ≤ ∑ j, P {ω | r < 2 * |V j ω|} :=
          measure_iUnion_fintype_le _ _
      _ ≤ ∑ _j : Fin M, ENNReal.ofReal ((M : ℝ) ^ (-(A ^ 2) / 8)) :=
          Finset.sum_le_sum (fun j _ => htail j)
      _ = ENNReal.ofReal ((M : ℝ) ^ (1 - A ^ 2 / 8)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1
          rw [show (1 : ℝ) - A ^ 2 / 8 = 1 + (-(A ^ 2) / 8) by ring,
            Real.rpow_add hM0, Real.rpow_one]
  have hadd : P E + P Eᶜ = 1 := by rw [measure_add_measure_compl hEm, measure_univ]
  have hreal : (P E).toReal + (P Eᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hadd, ENNReal.toReal_one]
  have hle : (P Eᶜ).toReal ≤ (M : ℝ) ^ (1 - A ^ 2 / 8) :=
    ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hM0.le _) hEc
  linarith

end LassoEfe

set_option maxHeartbeats 400000 in
open MeasureTheory ProbabilityTheory LassoDantzig.Lasso in
theorem solution {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hX : UnitDiag X) (βstar : Fin M → ℝ)
    (s : ℕ) (hs1 : 1 ≤ s) (hsM : s ≤ M) (hsparse : sparsity βstar ≤ s)
    (κ : ℝ) (hκ : 0 < κ) (hRE : RE X s 3 κ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hWm : ∀ i, Measurable (W i))
    (hWind : iIndepFun W P) (hWlaw : ∀ i, P.map (W i) = gaussianReal 0 (σ ^ 2).toNNReal)
    (A : ℝ) (hA : 2 * Real.sqrt 2 < A) (r : ℝ) (hr : r = A * σ * Real.sqrt (Real.log M / n)) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - (M : ℝ) ^ (1 - A ^ 2 / 8) ≤ (P E).toReal ∧
      ∀ ω ∈ E, ∀ βhat : Fin M → ℝ,
        IsLasso X (fun i => X.mulVec βstar i + W i ω) r βhat →
        -- (7.7)
        l1Norm (βhat - βstar) ≤ 16 * A / κ ^ 2 * σ * s * Real.sqrt (Real.log M / n) ∧
        -- (7.8)
        ∑ i, (X.mulVec (βhat - βstar) i) ^ 2 ≤ 16 * A ^ 2 / κ ^ 2 * σ ^ 2 * s * Real.log M ∧
        -- (7.9)
        (sparsity βhat : ℝ) ≤ 64 * phiMax X / κ ^ 2 * s ∧
        -- (7.10), under Assumption RE(s, m, 3) with witness κ', for all 1 < p ≤ 2
        (∀ (m : ℕ) (κ' : ℝ), 2 * s ≤ M → s ≤ m → s + m ≤ M → 0 < κ' → REm X s m 3 κ' →
          ∀ p : ℝ, 1 < p → p ≤ 2 →
            ∑ j, |βhat j - βstar j| ^ p ≤
              16 * (1 + 3 * Real.sqrt ((s : ℝ) / m)) ^ (2 * (p - 1)) * s *
                (A * σ / κ' ^ 2 * Real.sqrt (Real.log M / n)) ^ p) := by
  obtain ⟨hEm, hEP⟩ := LassoEfe.event_prob hn hM X hX P W σ hσ hWm hWind hWlaw A hA r hr
  refine ⟨_, hEm, hEP, ?_⟩
  intro ω hω βhat hL
  have hnoise : NoiseEventHalf X r (fun i => W i ω) := hω
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hlogpos : 0 < Real.log M := Real.log_pos (by linarith)
  have hApos : 0 < A := by
    have : 0 ≤ 2 * √2 := by positivity
    linarith
  have hrpos : 0 < r := by
    rw [hr]; have := Real.sqrt_pos.mpr (div_pos hlogpos hnR); positivity
  have hr2 : r ^ 2 * n = A ^ 2 * σ ^ 2 * Real.log M := by
    rw [hr, mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hlogpos.le hnR.le)]
    field_simp
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  set δ := βhat - βstar with hδ
  set J := supp βstar with hJ
  set Q := ∑ i, (X.mulVec δ i) ^ 2 with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hnR
  have hq2 : (√Q / √n) ^ 2 = Q / n := by
    rw [div_pow, Real.sq_sqrt hQ0, Real.sq_sqrt hnR.le]
  have hq0 : 0 ≤ √Q / √n := by positivity
  obtain ⟨c1, c2, hcone, _⟩ := LassoEfe.det_q hnR X βstar βhat (fun i => W i ω) r hrpos hnoise hL s
    hsparse κ hκ (l2On δ J) le_rfl (fun h0 hc => hRE J hsparse δ h0 hc)
  have hQn : κ ^ 2 * (Q / n) ≤ 16 * r ^ 2 * s := by
    have := pow_le_pow_left₀ (by positivity) c1 2
    rw [mul_pow, hq2] at this
    have e : (4 * r * √(s : ℝ)) ^ 2 = 16 * r ^ 2 * s := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (7.7)
    have : l1Norm δ ≤ 16 * r * s / κ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    calc l1Norm δ ≤ 16 * r * s / κ ^ 2 := this
      _ = 16 * A / κ ^ 2 * σ * s * Real.sqrt (Real.log M / n) := by rw [hr]; ring
  · -- (7.8)
    have hQle : Q ≤ 16 * r ^ 2 * s * n / κ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have : κ ^ 2 * (Q / n) * n = Q * κ ^ 2 := by field_simp
      nlinarith
    calc Q ≤ 16 * r ^ 2 * s * n / κ ^ 2 := hQle
      _ = 16 * (r ^ 2 * n) / κ ^ 2 * s := by ring
      _ = 16 * A ^ 2 / κ ^ 2 * σ ^ 2 * s * Real.log M := by rw [hr2]; ring
  · -- (7.9)
    set K := supp βhat with hK
    have hphi := LassoEfe.phi_nonneg (by omega : 1 ≤ M) X
    set z : Fin M → ℝ := fun j => ∑ i, X i j * X.mulVec δ i with hz
    have hlow : ∀ j ∈ K, r ^ 2 / 4 ≤ ((1 / (n : ℝ)) * z j) ^ 2 := by
      intro j hj
      have hbj : βhat j ≠ 0 := by
        rw [hK, supp, Finset.mem_filter] at hj; exact hj.2
      have hk := LassoEfe.kkt hnR X hX _ r βhat hL j hbj
      have hres : ∀ i, X.mulVec βstar i + W i ω - X.mulVec βhat i = W i ω - X.mulVec δ i := by
        intro i; simp only [hδ, Matrix.mulVec_sub, Pi.sub_apply]; ring
      simp only [hres] at hk
      have hsplit : (1 / (n : ℝ)) * ∑ i, X i j * (W i ω - X.mulVec δ i) =
          (1 / (n : ℝ)) * ∑ i, X i j * W i ω - (1 / (n : ℝ)) * z j := by
        rw [hz]; simp only [mul_sub, Finset.sum_sub_distrib]
      rw [hsplit] at hk
      have hnj := hnoise j
      have h1 : r / 2 ≤ |(1 / (n : ℝ)) * z j| := by
        have := abs_sub (((1 / (n : ℝ)) * ∑ i, X i j * W i ω)) ((1 / (n : ℝ)) * z j)
        linarith
      have h2 : (r / 2) ^ 2 ≤ |(1 / (n : ℝ)) * z j| ^ 2 :=
        pow_le_pow_left₀ (by linarith) h1 2
      rw [sq_abs] at h2
      linarith [show (r / 2) ^ 2 = r ^ 2 / 4 by ring]
    have hsumK : (K.card : ℝ) * (r ^ 2 / 4) ≤ ∑ j ∈ K, ((1 / (n : ℝ)) * z j) ^ 2 := by
      have := Finset.sum_le_sum hlow
      rw [Finset.sum_const, nsmul_eq_mul] at this
      exact this
    have hall : ∑ j ∈ K, ((1 / (n : ℝ)) * z j) ^ 2 ≤ ∑ j, ((1 / (n : ℝ)) * z j) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    have hop := LassoEfe.opbound hnR (by omega : 1 ≤ M) X (fun i => X.mulVec δ i)
    have hall2 : ∑ j, ((1 / (n : ℝ)) * z j) ^ 2 = (1 / (n : ℝ)) ^ 2 * ∑ j, z j ^ 2 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    have hzQ : ∑ j, z j ^ 2 ≤ n * phiMax X * Q := hop
    have hfin : (K.card : ℝ) * (r ^ 2 / 4) ≤ phiMax X * (Q / n) := by
      have e : (1 / (n : ℝ)) ^ 2 * (n * phiMax X * Q) = phiMax X * (Q / n) := by
        field_simp
      have := mul_le_mul_of_nonneg_left hzQ (show 0 ≤ (1 / (n : ℝ)) ^ 2 by positivity)
      linarith
    have hQn' : Q / n ≤ 16 * r ^ 2 * s / κ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have h3 : phiMax X * (Q / n) ≤ phiMax X * (16 * r ^ 2 * s / κ ^ 2) :=
      mul_le_mul_of_nonneg_left hQn' hphi
    have hcardK : (sparsity βhat : ℝ) = K.card := rfl
    rw [hcardK, show 64 * phiMax X / κ ^ 2 * (s : ℝ) = (phiMax X * (16 * r ^ 2 * s / κ ^ 2)) / (r ^ 2 / 4)
      by field_simp; ring]
    rw [le_div_iff₀ (by positivity)]
    linarith
  · -- (7.10)
    intro m κ' h2s hsm hsmM hκ' hREm p hp1 hp2
    have hmpos : 0 < m := by omega
    have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
    have hcardJ : J.card ≤ s := hsparse
    have hcardS : m ≤ Jᶜ.card := by
      rw [Finset.card_compl, Fintype.card_fin]; omega
    obtain ⟨J1, hsub, hcard1, hprop⟩ := LassoEfe.top_exists δ Jᶜ m hcardS
    have hT : IsTopOutside m J δ J1 := ⟨hsub, hcard1, hprop⟩
    set L := l2On δ (J ∪ J1) with hLdef
    have hL0 : l2On δ J ≤ L := LassoEfe.l2On_mono δ Finset.subset_union_left
    have hL0' : 0 ≤ L := Real.sqrt_nonneg _
    obtain ⟨d1, d2, dcone, da⟩ := LassoEfe.det_q hnR X βstar βhat (fun i => W i ω) r hrpos hnoise hL s
      hsparse κ' hκ' L hL0 (fun h0 hc => hREm J hsparse δ h0 hc J1 hT)
    have hκL : κ' * L ≤ √Q / √n := by
      by_cases h0 : δ = 0
      · have : L = 0 := by simp [hLdef, l2On, h0]
        rw [this, mul_zero]; exact hq0
      · have hre := hREm J hsparse δ h0 dcone J1 hT
        rw [le_div_iff₀ hsn]
        unfold euclNorm at hre
        linarith
    have htail := LassoEfe.tail_bound δ J J1 m hmpos hT
    have hsplit := LassoEfe.l2_split δ (J ∪ J1)
    have hb0 := LassoEfe.l1On_nonneg δ Jᶜ
    have ha0 := LassoEfe.l1On_nonneg δ J
    have hb2 : (l1On δ Jᶜ) ^ 2 ≤ 9 * s * L ^ 2 := by
      have h1 : l1On δ Jᶜ ≤ 3 * (√(s : ℝ) * L) := by linarith
      have h2 := pow_le_pow_left₀ hb0 h1 2
      have e : (3 * (√(s : ℝ) * L)) ^ 2 = 9 * s * L ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring
      linarith
    have hsum2 : ∑ j, δ j ^ 2 ≤ (1 + 3 * √((s : ℝ) / m)) ^ 2 * L ^ 2 := by
      have := LassoEfe.cfac L s m (Nat.cast_nonneg _) hmR
      have e : (l1On δ Jᶜ) ^ 2 / m ≤ 9 * s * L ^ 2 / m := div_le_div_of_nonneg_right hb2 hmR.le
      linarith
    set u := r / κ' ^ 2 with hu
    have hupos : 0 < u := by positivity
    have hLu : L ^ 2 ≤ 16 * s * u ^ 2 := by
      have e1 : (κ' * L) ^ 2 ≤ (√Q / √n) ^ 2 := pow_le_pow_left₀ (by positivity) hκL 2
      have e2 : (κ' * (√Q / √n)) ^ 2 ≤ (4 * r * √(s : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) d1 2
      have e3 : (4 * r * √(s : ℝ)) ^ 2 = 16 * r ^ 2 * s := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring
      rw [mul_pow] at e1 e2
      have f1 : κ' ^ 2 * (κ' ^ 2 * L ^ 2) ≤ κ' ^ 2 * (√Q / √n) ^ 2 :=
        mul_le_mul_of_nonneg_left e1 (by positivity)
      have f2 : κ' ^ 4 * L ^ 2 ≤ 16 * r ^ 2 * s := by linarith
      have f3 : 16 * (s : ℝ) * u ^ 2 = 16 * r ^ 2 * s / κ' ^ 4 := by rw [hu]; field_simp
      rw [f3, le_div_iff₀ (by positivity)]
      linarith
    have hC : 0 < 1 + 3 * √((s : ℝ) / m) := by positivity
    have hl1 : l1Norm δ ≤ 16 * s * u := by
      rw [hu, show 16 * (s : ℝ) * (r / κ' ^ 2) = 16 * r * s / κ' ^ 2 by ring,
        le_div_iff₀ (by positivity)]
      linarith
    have hl2 : ∑ j, δ j ^ 2 ≤ 16 * s * (1 + 3 * √((s : ℝ) / m)) ^ 2 * u ^ 2 := by
      have := mul_le_mul_of_nonneg_left hLu (sq_nonneg (1 + 3 * √((s : ℝ) / m)))
      linarith
    have key := LassoEfe.lp_final δ p s u _ hp1 hp2 (by linarith) hupos hC hl1 hl2
    have hu' : A * σ / κ' ^ 2 * Real.sqrt (Real.log M / n) = u := by rw [hu, hr]; ring
    rw [hu']
    simpa [hδ] using key
