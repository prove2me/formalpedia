-- Prove2me | solution 1 for LassoDantzig.Lasso.lemma_B1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T17:32:26.043985+00:00
-- url     : https://prove2.me/submissions/25071886-e80b-49d0-b1db-97a9b99bda74

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

lemma basic_gen {n M : ℕ} (hn : 0 < (n : ℝ)) (X : Matrix (Fin n) (Fin M) ℝ)
    (βstar βhat : Fin M → ℝ) (w : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (hnoise : NoiseEventHalf X r w)
    (hL : IsLasso X (fun i => X.mulVec βstar i + w i) r βhat) (β : Fin M → ℝ) :
    predLoss X (X.mulVec βstar) βhat + r * l1Norm (βhat - β) ≤
      predLoss X (X.mulVec βstar) β + 4 * r * l1On (βhat - β) (supp β) := by
  have h : (1 / (n : ℝ)) * ∑ i, (X.mulVec βstar i + w i - X.mulVec βhat i) ^ 2 + 2 * r * l1Norm βhat ≤
      (1 / (n : ℝ)) * ∑ i, (X.mulVec βstar i + w i - X.mulVec β i) ^ 2 + 2 * r * l1Norm β := hL β
  have e : ∀ b : Fin M → ℝ, ∑ i, (X.mulVec βstar i + w i - X.mulVec b i) ^ 2 =
      ∑ i, (X.mulVec b i - X.mulVec βstar i) ^ 2 - 2 * ∑ i, w i * X.mulVec b i
        + 2 * ∑ i, w i * X.mulVec βstar i + ∑ i, w i ^ 2 := by
    intro b
    have : ∀ i, (X.mulVec βstar i + w i - X.mulVec b i) ^ 2 =
        (X.mulVec b i - X.mulVec βstar i) ^ 2 - 2 * (w i * X.mulVec b i)
          + 2 * (w i * X.mulVec βstar i) + w i ^ 2 := by intro i; ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
  rw [e βhat, e β] at h
  have hCdiff : ∑ i, w i * X.mulVec βhat i - ∑ i, w i * X.mulVec β i =
      ∑ i, w i * X.mulVec (βhat - β) i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [Matrix.mulVec_sub, Pi.sub_apply]; ring
  have hCb : (1 / (n : ℝ)) * ∑ i, w i * X.mulVec (βhat - β) i ≤ r / 2 * l1Norm (βhat - β) := by
    rw [cross, Finset.mul_sum, l1Norm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hj : 2 * |(1 / (n : ℝ)) * ∑ i, X i j * w i| ≤ r := hnoise j
    have : (1 / (n : ℝ)) * ((βhat - β) j * ∑ i, X i j * w i) =
        (βhat - β) j * ((1 / (n : ℝ)) * ∑ i, X i j * w i) := by ring
    rw [this]
    calc (βhat - β) j * ((1 / (n : ℝ)) * ∑ i, X i j * w i)
        ≤ |(βhat - β) j * ((1 / (n : ℝ)) * ∑ i, X i j * w i)| := le_abs_self _
      _ = |(βhat - β) j| * |(1 / (n : ℝ)) * ∑ i, X i j * w i| := abs_mul _ _
      _ ≤ |(βhat - β) j| * (r / 2) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = r / 2 * |(βhat - β) j| := by ring
  have hdiff : l1Norm β - l1Norm βhat ≤ l1On (βhat - β) (supp β) - l1On (βhat - β) (supp β)ᶜ := by
    rw [l1_split β (supp β), l1_split βhat (supp β)]
    have h1 : l1On β (supp β) - l1On βhat (supp β) ≤ l1On (βhat - β) (supp β) := by
      unfold l1On
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro j _
      have := abs_sub_abs_le_abs_sub (β j) (βhat j)
      rw [abs_sub_comm] at this
      simpa using this
    have h2 : l1On β (supp β)ᶜ - l1On βhat (supp β)ᶜ = - l1On (βhat - β) (supp β)ᶜ := by
      unfold l1On
      rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have : β j = 0 := by
        rw [Finset.mem_compl, supp, Finset.mem_filter] at hj
        simpa using hj
      simp [this]
    linarith
  have hsplit := l1_split (βhat - β) (supp β)
  unfold predLoss
  rw [← hCdiff] at hCb
  nlinarith [hCb, hdiff, hsplit, h]

lemma kkt_upper {n M : ℕ} (hn : 0 < (n : ℝ)) (X : Matrix (Fin n) (Fin M) ℝ) (hX : UnitDiag X)
    (y : Fin n → ℝ) (r : ℝ) (hr0 : 0 ≤ r) (βhat : Fin M → ℝ) (hL : IsLasso X y r βhat) (j : Fin M) :
    |(1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec βhat i)| ≤ r := by
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
  have key' : ∀ t : ℝ, 0 ≤ -2 * t * g + t ^ 2 + 2 * r * |t| := by
    intro t
    have h1 := key t
    have h2 : |b + t| - |b| ≤ |t| := by
      have := abs_add_le b t; linarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hr0]
  rw [abs_le]
  constructor
  · by_contra hc
    rw [not_le] at hc
    have k := key' (g + r)
    have e : |g + r| = -(g + r) := abs_of_neg (by linarith)
    rw [e] at k
    nlinarith
  · by_contra hc
    rw [not_le] at hc
    have k := key' (g - r)
    have e : |g - r| = g - r := abs_of_pos (by linarith)
    rw [e] at k
    nlinarith

end LassoEfe

set_option maxHeartbeats 400000 in
open MeasureTheory ProbabilityTheory LassoDantzig.Lasso in
theorem solution {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hX : UnitDiag X) (βstar : Fin M → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hWm : ∀ i, Measurable (W i))
    (hWind : iIndepFun W P) (hWlaw : ∀ i, P.map (W i) = gaussianReal 0 (σ ^ 2).toNNReal)
    (A : ℝ) (hA : 2 * Real.sqrt 2 < A) (r : ℝ) (hr : r = A * σ * Real.sqrt (Real.log M / n)) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - (M : ℝ) ^ (1 - A ^ 2 / 8) ≤ (P E).toReal ∧
      ∀ ω ∈ E, ∀ βhat : Fin M → ℝ,
        IsLasso X (fun i => X.mulVec βstar i + W i ω) r βhat →
        -- (B.1), for every β ∈ ℝ^M
        (∀ β : Fin M → ℝ,
          predLoss X (X.mulVec βstar) βhat + r * ∑ j, |βhat j - β j| ≤
              predLoss X (X.mulVec βstar) β + 4 * r * ∑ j ∈ supp β, |βhat j - β j| ∧
          predLoss X (X.mulVec βstar) β + 4 * r * ∑ j ∈ supp β, |βhat j - β j| ≤
              predLoss X (X.mulVec βstar) β +
                4 * r * Real.sqrt (sparsity β) *
                  Real.sqrt (∑ j ∈ supp β, (βhat j - β j) ^ 2)) ∧
        -- (B.2)
        (∀ j : Fin M,
          |(1 / (n : ℝ)) * ∑ i, X i j * (X.mulVec βstar i - X.mulVec βhat i)| ≤ 3 * r / 2) ∧
        -- (B.3)
        (sparsity βhat : ℝ) ≤ 4 * phiMax X * (predLoss X (X.mulVec βstar) βhat / r ^ 2) := by
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
  refine ⟨?_, ?_, ?_⟩
  · -- (B.1)
    intro β
    constructor
    · have := LassoEfe.basic_gen hnR X βstar βhat (fun i => W i ω) r hrpos hnoise hL β
      simpa only [l1Norm, l1On, Pi.sub_apply] using this
    · have hcs : ∑ j ∈ supp β, |βhat j - β j| ≤
          √(sparsity β : ℝ) * √(∑ j ∈ supp β, (βhat j - β j) ^ 2) := by
        simpa only [l1On, l2On, Pi.sub_apply, sparsity] using
          LassoEfe.l1_le_sqrt_card (βhat - β) (supp β)
      have := mul_le_mul_of_nonneg_left hcs (by linarith : (0 : ℝ) ≤ 4 * r)
      linarith
  · -- (B.2)
    intro j
    have hk : |(1 / (n : ℝ)) * ∑ i, X i j * (X.mulVec βstar i + W i ω - X.mulVec βhat i)| ≤ r :=
      LassoEfe.kkt_upper hnR X hX _ r hrpos.le βhat hL j
    have hnj : 2 * |(1 / (n : ℝ)) * ∑ i, X i j * W i ω| ≤ r := hnoise j
    have hsplit : (1 / (n : ℝ)) * ∑ i, X i j * (X.mulVec βstar i - X.mulVec βhat i) =
        (1 / (n : ℝ)) * ∑ i, X i j * (X.mulVec βstar i + W i ω - X.mulVec βhat i) -
          (1 / (n : ℝ)) * ∑ i, X i j * W i ω := by
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl; intro i _; ring
    rw [hsplit]
    have := abs_sub ((1 / (n : ℝ)) * ∑ i, X i j * (X.mulVec βstar i + W i ω - X.mulVec βhat i))
      ((1 / (n : ℝ)) * ∑ i, X i j * W i ω)
    linarith
  · -- (B.3)
    have hphi := LassoEfe.phi_nonneg (by omega : 1 ≤ M) X
    have hlow : ∀ j ∈ supp βhat, r ^ 2 / 4 ≤
        ((1 / (n : ℝ)) * ∑ i, X i j * X.mulVec (βhat - βstar) i) ^ 2 := by
      intro j hj
      have hbj : βhat j ≠ 0 := by
        rw [supp, Finset.mem_filter] at hj; exact hj.2
      have hk : r ≤ |(1 / (n : ℝ)) * ∑ i, X i j * (X.mulVec βstar i + W i ω - X.mulVec βhat i)| :=
        LassoEfe.kkt hnR X hX _ r βhat hL j hbj
      have hsplit : (1 / (n : ℝ)) * ∑ i, X i j * (X.mulVec βstar i + W i ω - X.mulVec βhat i) =
          (1 / (n : ℝ)) * ∑ i, X i j * W i ω -
            (1 / (n : ℝ)) * ∑ i, X i j * X.mulVec (βhat - βstar) i := by
        rw [← mul_sub, ← Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl; intro i _
        rw [Matrix.mulVec_sub, Pi.sub_apply]; ring
      rw [hsplit] at hk
      have hnj : 2 * |(1 / (n : ℝ)) * ∑ i, X i j * W i ω| ≤ r := hnoise j
      have h1 : r / 2 ≤ |(1 / (n : ℝ)) * ∑ i, X i j * X.mulVec (βhat - βstar) i| := by
        have := abs_sub ((1 / (n : ℝ)) * ∑ i, X i j * W i ω)
          ((1 / (n : ℝ)) * ∑ i, X i j * X.mulVec (βhat - βstar) i)
        linarith
      have h2 := pow_le_pow_left₀ (by linarith) h1 2
      rw [sq_abs] at h2
      linarith [show (r / 2) ^ 2 = r ^ 2 / 4 by ring]
    have hsumK : ((supp βhat).card : ℝ) * (r ^ 2 / 4) ≤
        ∑ j ∈ supp βhat, ((1 / (n : ℝ)) * ∑ i, X i j * X.mulVec (βhat - βstar) i) ^ 2 := by
      have := Finset.sum_le_sum hlow
      rw [Finset.sum_const, nsmul_eq_mul] at this
      exact this
    have hall : ∑ j ∈ supp βhat, ((1 / (n : ℝ)) * ∑ i, X i j * X.mulVec (βhat - βstar) i) ^ 2 ≤
        ∑ j, ((1 / (n : ℝ)) * ∑ i, X i j * X.mulVec (βhat - βstar) i) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    have hop := LassoEfe.opbound hnR (by omega : 1 ≤ M) X (fun i => X.mulVec (βhat - βstar) i)
    have hall2 : ∑ j, ((1 / (n : ℝ)) * ∑ i, X i j * X.mulVec (βhat - βstar) i) ^ 2 =
        (1 / (n : ℝ)) ^ 2 * ∑ j, (∑ i, X i j * X.mulVec (βhat - βstar) i) ^ 2 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    have hP : predLoss X (X.mulVec βstar) βhat =
        (1 / (n : ℝ)) * ∑ i, (X.mulVec (βhat - βstar) i) ^ 2 := by
      unfold predLoss
      congr 1
      apply Finset.sum_congr rfl; intro i _
      rw [Matrix.mulVec_sub, Pi.sub_apply]
    have hfin : ((supp βhat).card : ℝ) * (r ^ 2 / 4) ≤
        phiMax X * ((1 / (n : ℝ)) * ∑ i, (X.mulVec (βhat - βstar) i) ^ 2) := by
      have e : (1 / (n : ℝ)) ^ 2 * (n * phiMax X * ∑ i, (X.mulVec (βhat - βstar) i) ^ 2) =
          phiMax X * ((1 / (n : ℝ)) * ∑ i, (X.mulVec (βhat - βstar) i) ^ 2) := by
        field_simp
      have := mul_le_mul_of_nonneg_left hop (show 0 ≤ (1 / (n : ℝ)) ^ 2 by positivity)
      linarith
    rw [hP]
    generalize (1 / (n : ℝ)) * ∑ i, (X.mulVec (βhat - βstar) i) ^ 2 = Lq at hfin ⊢
    have e : 4 * phiMax X * (Lq / r ^ 2) = (phiMax X * Lq) / (r ^ 2 / 4) := by
      rw [div_div_eq_mul_div]; ring
    rw [e, le_div_iff₀ (by positivity)]
    exact hfin
