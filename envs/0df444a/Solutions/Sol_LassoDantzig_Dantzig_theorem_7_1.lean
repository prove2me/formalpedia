-- Prove2me | solution 1 for LassoDantzig.Dantzig.theorem_7_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T08:50:41.198972+00:00
-- url     : https://prove2.me/submissions/e5c94207-2dd4-49b6-9658-b4bf72cec49c

import Mathlib
import Definitions.Def_LassoDantzig_Dantzig_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real Filter Topology

namespace Dz291
open LassoDantzig.Dantzig

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
    ∑ j, |δ j| = l1On δ J + l1On δ Jᶜ := by
  unfold l1On
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

lemma l2On_nonneg {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) : 0 ≤ l2On δ J :=
  Real.sqrt_nonneg _

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
    (hT : IsTopBlock δ J0 J1 m) :
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
    (8 * s * u) ^ (2 - p) * (16 * s * C ^ 2 * u ^ 2) ^ (p - 1) =
      (2 : ℝ) ^ (p - 1) * 8 * C ^ (2 * (p - 1)) * s * u ^ p := by
  have hK : 0 < 8 * s * u := by positivity
  have e1 : (16 * s * C ^ 2 * u ^ 2) ^ (p - 1) =
      (8 * s * u) ^ (p - 1) * ((2 : ℝ) ^ (p - 1) * (C ^ 2 * u) ^ (p - 1)) := by
    rw [← Real.mul_rpow (by norm_num) (by positivity), ← Real.mul_rpow hK.le (by positivity)]
    congr 1; ring
  have e2 : (8 * s * u) ^ (2 - p) * (8 * s * u) ^ (p - 1) = 8 * s * u := by
    rw [← Real.rpow_add hK, show 2 - p + (p - 1) = (1 : ℝ) by ring, Real.rpow_one]
  have e3 : (C ^ 2 * u) ^ (p - 1) = C ^ (2 * (p - 1)) * u ^ (p - 1) := by
    rw [Real.mul_rpow (by positivity) hu.le, Real.rpow_mul hC.le, Real.rpow_two]
  have e4 : u ^ p = u * u ^ (p - 1) := by
    conv_lhs => rw [show p = 1 + (p - 1) by ring]
    rw [Real.rpow_add hu, Real.rpow_one]
  rw [e1, ← mul_assoc, e2, e3, e4]; ring

lemma lp_final {M : ℕ} (δ : Fin M → ℝ) (p s u C : ℝ) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (hs : 0 < s) (hu : 0 < u) (hC : 0 < C)
    (h1 : ∑ j, |δ j| ≤ 8 * s * u) (h2 : ∑ j, δ j ^ 2 ≤ 16 * s * C ^ 2 * u ^ 2) :
    ∑ j, |δ j| ^ p ≤ (2 : ℝ) ^ (p - 1) * 8 * C ^ (2 * (p - 1)) * s * u ^ p := by
  have hA0 : 0 ≤ ∑ j, |δ j| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hB0 : 0 ≤ ∑ j, δ j ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc ∑ j, |δ j| ^ p ≤ (∑ j, |δ j|) ^ (2 - p) * (∑ j, δ j ^ 2) ^ (p - 1) :=
        holder_interp δ p hp1 hp2
    _ ≤ (8 * s * u) ^ (2 - p) * (16 * s * C ^ 2 * u ^ 2) ^ (p - 1) :=
        mul_le_mul (Real.rpow_le_rpow hA0 h1 (by linarith))
          (Real.rpow_le_rpow hB0 h2 (by linarith)) (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (p - 1) * 8 * C ^ (2 * (p - 1)) * s * u ^ p := rpow_alg s u C p hs hu hC

/-- Shared deterministic facts on the noise event for a Dantzig selector. -/
lemma det_base {n M : ℕ} (hn : 0 < (n : ℝ)) (X : Matrix (Fin n) (Fin M) ℝ)
    (βstar βD : Fin M → ℝ) (w : Fin n → ℝ) (r : ℝ) (hr0 : 0 ≤ r)
    (hnoise : ∀ j, |(1 / (n : ℝ)) * ∑ i, X i j * w i| ≤ r)
    (hD : IsDantzig X (fun i => X.mulVec βstar i + w i) r βD) :
    l1On (βD - βstar) (supp βstar)ᶜ ≤ l1On (βD - βstar) (supp βstar) ∧
    (1 / (n : ℝ)) * ∑ i, X.mulVec (βD - βstar) i ^ 2 ≤ 4 * r * l1On (βD - βstar) (supp βstar) := by
  set δ := βD - βstar with hδ
  set J := supp βstar with hJ
  have hin : InLambda X (fun i => X.mulVec βstar i + w i) r βstar := by
    intro j
    have : ∀ i, X.mulVec βstar i + w i - X.mulVec βstar i = w i := by intro i; ring
    simp only [this]
    exact hnoise j
  have hl1 := hD.2 βstar hin
  have hdiff : ∑ j, |βstar j| - ∑ j, |βD j| ≤ l1On δ J - l1On δ Jᶜ := by
    rw [l1_split βstar J, l1_split βD J]
    have h1 : l1On βstar J - l1On βD J ≤ l1On δ J := by
      unfold l1On
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro j _
      have := abs_sub_abs_le_abs_sub (βstar j) (βD j)
      rw [abs_sub_comm] at this
      simpa [hδ] using this
    have h2 : l1On βstar Jᶜ - l1On βD Jᶜ = - l1On δ Jᶜ := by
      unfold l1On
      rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have : βstar j = 0 := by
        rw [Finset.mem_compl, hJ, supp, Finset.mem_filter] at hj
        simpa using hj
      simp [hδ, this]
    linarith
  have hcone : l1On δ Jᶜ ≤ l1On δ J := by linarith
  refine ⟨hcone, ?_⟩
  -- correlation bound
  have hcorr : ∀ j, |(1 / (n : ℝ)) * ∑ i, X i j * X.mulVec δ i| ≤ 2 * r := by
    intro j
    have e : (1 / (n : ℝ)) * ∑ i, X i j * X.mulVec δ i =
        (1 / (n : ℝ)) * ∑ i, X i j * ((X.mulVec βstar i + w i) - X.mulVec βstar i) -
        (1 / (n : ℝ)) * ∑ i, X i j * ((X.mulVec βstar i + w i) - X.mulVec βD i) := by
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [hδ, Matrix.mulVec_sub, Pi.sub_apply]
      ring
    rw [e]
    have h1 := hin j
    have h2 := hD.1 j
    calc _ ≤ |(1 / (n : ℝ)) * ∑ i, X i j * ((X.mulVec βstar i + w i) - X.mulVec βstar i)| +
          |(1 / (n : ℝ)) * ∑ i, X i j * ((X.mulVec βstar i + w i) - X.mulVec βD i)| :=
          abs_sub _ _
      _ ≤ 2 * r := by linarith
  have hQ : (1 / (n : ℝ)) * ∑ i, X.mulVec δ i ^ 2 ≤ 2 * r * (l1On δ J + l1On δ Jᶜ) := by
    have e : ∑ i, X.mulVec δ i ^ 2 = ∑ i, X.mulVec δ i * X.mulVec δ i := by
      apply Finset.sum_congr rfl; intro i _; ring
    rw [e, cross, ← l1_split, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have : (1 / (n : ℝ)) * (δ j * ∑ i, X i j * X.mulVec δ i) =
        δ j * ((1 / (n : ℝ)) * ∑ i, X i j * X.mulVec δ i) := by ring
    rw [this]
    calc δ j * ((1 / (n : ℝ)) * ∑ i, X i j * X.mulVec δ i)
        ≤ |δ j * ((1 / (n : ℝ)) * ∑ i, X i j * X.mulVec δ i)| := le_abs_self _
      _ = |δ j| * |(1 / (n : ℝ)) * ∑ i, X i j * X.mulVec δ i| := abs_mul _ _
      _ ≤ |δ j| * (2 * r) := mul_le_mul_of_nonneg_left (hcorr j) (abs_nonneg _)
      _ = 2 * r * |δ j| := by ring
  nlinarith [hQ, hcone]


lemma sqNN_coe (c : ℝ) : ((sqNN c : NNReal) : ℝ) = c ^ 2 := rfl

lemma core2 (r κ s q a : ℝ) (hr : 0 ≤ r) (hκ : 0 < κ) (hq : 0 ≤ q) (ha : 0 ≤ a)
    (h1 : q ^ 2 ≤ 4 * r * a) (h2 : κ * a ≤ √s * q) : κ * q ≤ 4 * r * √s := by
  have k1 : κ * q ^ 2 ≤ 4 * r * √s * q := by
    have e1 := mul_le_mul_of_nonneg_left h1 hκ.le
    have e2 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 4 * r by linarith)
    nlinarith
  rcases hq.eq_or_lt with h0 | h0
  · rw [← h0]; simp; positivity
  · have : q * (κ * q) ≤ q * (4 * r * √s) := by nlinarith
    exact le_of_mul_le_mul_left this h0

set_option maxHeartbeats 800000 in
lemma det_main {n M : ℕ} (hn : 0 < (n : ℝ)) (X : Matrix (Fin n) (Fin M) ℝ)
    (βstar βD : Fin M → ℝ) (w : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (s : ℕ) (hs : 1 ≤ s) (hsparse : sparsity βstar ≤ s)
    (κ : ℝ) (hκ : 0 < κ) (hRE : RE X s 1 κ)
    (hnoise : ∀ j, |(1 / (n : ℝ)) * ∑ i, X i j * w i| ≤ r)
    (hD : IsDantzig X (fun i => X.mulVec βstar i + w i) r βD) :
    (∑ j, |βD j - βstar j| ≤ 8 * r * s / κ ^ 2) ∧
    (∑ i, X.mulVec (βD - βstar) i ^ 2 ≤ 16 * r ^ 2 * s * n / κ ^ 2) ∧
    (∀ (m : ℕ) (κ' : ℝ), s ≤ m → s + m ≤ M → 0 < κ' → REm X s m 1 κ' →
      ∀ p : ℝ, 1 < p → p ≤ 2 →
        ∑ j, |βD j - βstar j| ^ p ≤
          (2 : ℝ) ^ (p - 1) * 8 * (1 + Real.sqrt ((s : ℝ) / m)) ^ (2 * (p - 1)) * s *
            (r / κ' ^ 2) ^ p) := by
  classical
  obtain ⟨hcone, hQa⟩ := det_base hn X βstar βD w r hr.le hnoise hD
  set δ := βD - βstar with hδ
  have hδj : ∀ j, βD j - βstar j = δ j := fun j => rfl
  simp only [hδj]
  set J := supp βstar with hJ
  set a := l1On δ J with hadef
  set b := l1On δ Jᶜ with hbdef
  set Q := ∑ i, X.mulVec δ i ^ 2 with hQdef
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hJcardN : J.card ≤ s := hsparse
  have hJcard : (J.card : ℝ) ≤ s := by exact_mod_cast hJcardN
  have ha0 : 0 ≤ a := l1On_nonneg _ _
  have hb0 : 0 ≤ b := l1On_nonneg _ _
  have ha : a ≤ √(s : ℝ) * l2On δ J :=
    (l1_le_sqrt_card δ J).trans
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hJcard) (l2On_nonneg _ _))
  have hsplit : ∑ j, |δ j| = a + b := l1_split δ J
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hss : √(s : ℝ) * √(s : ℝ) = s := Real.mul_self_sqrt (by positivity)
  by_cases hδ0 : δ = 0
  · have hz : ∀ j, δ j = 0 := fun j => by rw [hδ0]; rfl
    have hQz : Q = 0 := by
      rw [hQdef, hδ0]; simp
    refine ⟨?_, ?_, ?_⟩
    · simp only [hz, abs_zero, Finset.sum_const_zero]; positivity
    · rw [hQz]; positivity
    · intro m κ' _ _ _ _ p hp1 _
      simp only [hz, abs_zero, Real.zero_rpow (by linarith : p ≠ 0), Finset.sum_const_zero]
      positivity
  -- nonzero δ
  set q := √((1 / (n : ℝ)) * Q) with hqdef
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = (1 / (n : ℝ)) * Q := Real.sq_sqrt (by positivity)
  have hsqQ : euclNorm (X.mulVec δ) = √(n : ℝ) * q := by
    unfold euclNorm
    rw [hqdef, ← Real.sqrt_mul hn.le]
    congr 1
    rw [← hQdef]; field_simp
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn
  have hqa : q ^ 2 ≤ 4 * r * a := by rw [hq2]; exact hQa
  -- RE(s,1)
  have hREJ := hRE J hJcardN δ hδ0 (by unfold ConeCond; linarith)
  rw [hsqQ] at hREJ
  have hkl : κ * l2On δ J ≤ q := by
    have : √(n : ℝ) * (κ * l2On δ J) ≤ √(n : ℝ) * q := by linarith
    exact le_of_mul_le_mul_left this hsn
  have hka : κ * a ≤ √(s : ℝ) * q := by
    have := mul_le_mul_of_nonneg_left ha hκ.le
    have h2 := mul_le_mul_of_nonneg_left hkl (Real.sqrt_nonneg (s : ℝ))
    nlinarith
  have hkq := core2 r κ s q a hr.le hκ hq0 ha0 hqa hka
  refine ⟨?_, ?_, ?_⟩
  · -- (7.4)
    rw [hsplit, le_div_iff₀ (by positivity)]
    have : κ ^ 2 * a ≤ 4 * r * s := by
      have e1 : κ ^ 2 * a = κ * (κ * a) := by ring
      have e2 := mul_le_mul_of_nonneg_left hka hκ.le
      have e3 := mul_le_mul_of_nonneg_left hkq (Real.sqrt_nonneg (s : ℝ))
      nlinarith
    nlinarith
  · -- (7.5)
    rw [le_div_iff₀ (by positivity)]
    have hQn : Q = n * q ^ 2 := by rw [hq2]; field_simp
    have hk2 : κ ^ 2 * q ^ 2 ≤ 16 * r ^ 2 * s := by
      have e1 : 0 ≤ κ * q := by positivity
      have e2 : (κ * q) ^ 2 ≤ (4 * r * √(s : ℝ)) ^ 2 := pow_le_pow_left₀ e1 hkq 2
      have e3 : (4 * r * √(s : ℝ)) ^ 2 = 16 * r ^ 2 * s := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
      nlinarith
    rw [hQn]
    nlinarith
  · -- (7.6)
    intro m κ' hsm hsmM hκ' hREm p hp1 hp2
    have hm0 : 0 < m := by omega
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
    have hcardc : m ≤ Jᶜ.card := by
      rw [Finset.card_compl, Fintype.card_fin]; omega
    obtain ⟨J1, hsub, hcard, hprop⟩ := top_exists δ Jᶜ m hcardc
    have hT : IsTopBlock δ J J1 m := ⟨hsub, hcard, hprop⟩
    have hR := hREm J hJcardN δ hδ0 (by unfold ConeCond; linarith) J1 hT
    rw [hsqQ] at hR
    set L := l2On δ (J ∪ J1) with hLdef
    have hL0 : 0 ≤ L := l2On_nonneg _ _
    have hkL : κ' * L ≤ q := by
      have : √(n : ℝ) * (κ' * L) ≤ √(n : ℝ) * q := by linarith
      exact le_of_mul_le_mul_left this hsn
    have haL : a ≤ √(s : ℝ) * L :=
      ha.trans (mul_le_mul_of_nonneg_left (l2On_mono δ Finset.subset_union_left)
        (Real.sqrt_nonneg _))
    have hka' : κ' * a ≤ √(s : ℝ) * q := by
      have h1 := mul_le_mul_of_nonneg_left haL hκ'.le
      have h2 := mul_le_mul_of_nonneg_left hkL (Real.sqrt_nonneg (s : ℝ))
      calc κ' * a ≤ κ' * (√(s : ℝ) * L) := h1
        _ = √(s : ℝ) * (κ' * L) := by ring
        _ ≤ √(s : ℝ) * q := h2
    have hkq' := core2 r κ' s q a hr.le hκ' hq0 ha0 hqa hka'
    have hK2L : κ' ^ 2 * L ≤ 4 * r * √(s : ℝ) := by
      have e1 : κ' ^ 2 * L = κ' * (κ' * L) := by ring
      have e2 := mul_le_mul_of_nonneg_left hkL hκ'.le
      rw [e1]; exact e2.trans hkq'
    set u := r / κ' ^ 2 with hudef
    have hu : 0 < u := by positivity
    have hK : 0 < κ' ^ 2 := by positivity
    set C := 1 + √((s : ℝ) / m) with hCdef
    have hC : 0 < C := by positivity
    have h1 : ∑ j, |δ j| ≤ 8 * s * u := by
      rw [hsplit, hudef, mul_div_assoc', le_div_iff₀ hK]
      have e0 : a + b ≤ 2 * (√(s : ℝ) * L) := by linarith
      have e1' := mul_le_mul_of_nonneg_right e0 hK.le
      have e1 : (a + b) * κ' ^ 2 ≤ 2 * √(s : ℝ) * (κ' ^ 2 * L) := by
        calc (a + b) * κ' ^ 2 ≤ 2 * (√(s : ℝ) * L) * κ' ^ 2 := e1'
          _ = 2 * √(s : ℝ) * (κ' ^ 2 * L) := by ring
      have e2 := mul_le_mul_of_nonneg_left hK2L (show 0 ≤ 2 * √(s : ℝ) by positivity)
      have e3 : 2 * √(s : ℝ) * (4 * r * √(s : ℝ)) = 8 * s * r := by
        calc 2 * √(s : ℝ) * (4 * r * √(s : ℝ)) = 8 * r * (√(s : ℝ) * √(s : ℝ)) := by ring
          _ = 8 * s * r := by rw [hss]; ring
      linarith
    have h2 : ∑ j, δ j ^ 2 ≤ 16 * s * C ^ 2 * u ^ 2 := by
      have hsp := l2_split δ (J ∪ J1)
      have ht := tail_bound δ J J1 m hm0 hT
      have hbsq : b ^ 2 / m ≤ s * L ^ 2 / m := by
        apply div_le_div_of_nonneg_right _ hmR.le
        have e1 : b ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hb0 hcone 2
        have e2 : a ^ 2 ≤ (√(s : ℝ) * L) ^ 2 := pow_le_pow_left₀ ha0 haL 2
        have e3 : (√(s : ℝ) * L) ^ 2 = s * L ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]
        linarith
      have hCL : L ^ 2 + s * L ^ 2 / m ≤ C ^ 2 * L ^ 2 := by
        have h := Real.sq_sqrt (div_nonneg (show (0 : ℝ) ≤ s by positivity) hmR.le)
        have h0 := Real.sqrt_nonneg ((s : ℝ) / m)
        have : s * L ^ 2 / m = ((s : ℝ) / m) * L ^ 2 := by ring
        rw [this, hCdef]
        nlinarith [sq_nonneg L, mul_nonneg h0 (sq_nonneg L)]
      have hL2 : L ^ 2 ≤ 16 * s * u ^ 2 := by
        rw [hudef, div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
        have e1 : 0 ≤ κ' ^ 2 * L := by positivity
        have e2 : (κ' ^ 2 * L) ^ 2 ≤ (4 * r * √(s : ℝ)) ^ 2 := pow_le_pow_left₀ e1 hK2L 2
        have e3 : (4 * r * √(s : ℝ)) ^ 2 = 16 * r ^ 2 * s := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
        nlinarith
      have hCL2 : C ^ 2 * L ^ 2 ≤ C ^ 2 * (16 * s * u ^ 2) :=
        mul_le_mul_of_nonneg_left hL2 (by positivity)
      have hct : ∑ k ∈ (J ∪ J1)ᶜ, δ k ^ 2 ≤ s * L ^ 2 / m := by
        have : l1On δ Jᶜ = b := rfl
        rw [this] at ht
        linarith
      have e4 : C ^ 2 * (16 * s * u ^ 2) = 16 * s * C ^ 2 * u ^ 2 := by ring
      linarith
    exact lp_final δ p s u C hp1 hp2 (by positivity) hu hC h1 h2

lemma event_prob {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M) (X : Matrix (Fin n) (Fin M) ℝ)
    (hX : ∀ j, (1 / (n : ℝ)) * ∑ i, X i j ^ 2 = 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hWm : ∀ i, Measurable (W i))
    (hWind : iIndepFun W P) (hWlaw : ∀ i, P.map (W i) = gaussianReal 0 (σ ^ 2).toNNReal)
    (A : ℝ) (hA : Real.sqrt 2 < A) (r : ℝ)
    (hr : r = A * σ * Real.sqrt (Real.log M / n)) :
    MeasurableSet {ω | ∀ j, |(1 / (n : ℝ)) * ∑ i, X i j * W i ω| ≤ r} ∧
    1 - (M : ℝ) ^ (1 - A ^ 2 / 2) ≤
      (P {ω | ∀ j, |(1 / (n : ℝ)) * ∑ i, X i j * W i ω| ≤ r}).toReal := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hlogM : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) hMR
  have hlog2 := Real.log_two_gt_d9
  have hlogpos : 0 < Real.log M := by linarith
  have hA2 : 2 < A ^ 2 := by
    have h8 : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hpos : 0 ≤ √2 := by positivity
    nlinarith
  have hr2 : r ^ 2 = A ^ 2 * σ ^ 2 * (Real.log M / n) := by
    rw [hr, mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hlogpos.le hnR.le)]
  have hApos : 0 < A := by
    have : 0 ≤ √2 := by positivity
    linarith
  have hrpos : 0 < r := by
    rw [hr]; have := Real.sqrt_pos.mpr (div_pos hlogpos hnR); positivity
  set V : Fin M → Ω → ℝ := fun j ω => ∑ i, (X i j / n) * W i ω with hV
  have hVeq : ∀ j ω, (1 / (n : ℝ)) * ∑ i, X i j * W i ω = V j ω := by
    intro j ω; simp only [hV, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  have hVm : ∀ j, Measurable (V j) := fun j =>
    Finset.measurable_sum _ (fun i _ => (hWm i).const_mul _)
  set E := {ω | ∀ j, |(1 / (n : ℝ)) * ∑ i, X i j * W i ω| ≤ r} with hEdef
  have hE : E = ⋂ j, {ω | |V j ω| ≤ r} := by
    ext ω
    simp only [hEdef, Set.mem_iInter, Set.mem_setOf_eq, hVeq]
  have hEm : MeasurableSet E := by
    rw [hE]
    exact MeasurableSet.iInter (fun j => measurableSet_le
      (continuous_abs.measurable.comp (hVm j)) measurable_const)
  refine ⟨hEm, ?_⟩
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
  have hprod : 2 ≤ A ^ 2 * Real.log M * π := by
    have h1 : 2 * 0.69 ≤ A ^ 2 * Real.log M := by nlinarith
    have h3 := Real.pi_gt_three
    nlinarith
  have hexp : Real.exp (-r ^ 2 / (2 * (σ ^ 2 / n))) = (M : ℝ) ^ (-(A ^ 2) / 2) := by
    rw [Real.rpow_def_of_pos hM0, hr2]
    congr 1
    field_simp
  have htail : ∀ j, P {ω | r < |V j ω|} ≤ ENNReal.ofReal ((M : ℝ) ^ (-(A ^ 2) / 2)) := by
    intro j
    have hset : {ω | r < |V j ω|} = V j ⁻¹' {x | r < |x|} := rfl
    rw [hset, ← Measure.map_apply (hVm j)
      (measurableSet_lt measurable_const continuous_abs.measurable), hlaw j]
    have htv : 2 * ((vj j : NNReal) : ℝ) / π ≤ r ^ 2 := by
      rw [hvj j, div_le_iff₀ Real.pi_pos, hr2]
      have ht : 0 < σ ^ 2 / (n : ℝ) := by positivity
      have : A ^ 2 * σ ^ 2 * (Real.log M / n) * π =
          σ ^ 2 / n * (A ^ 2 * Real.log M * π) := by ring
      rw [this]
      nlinarith
    refine (gauss_tail (vj j) (hvne j) r hrpos htv).trans ?_
    rw [hvj j, hexp]
  have hcomp : Eᶜ = ⋃ j, {ω | r < |V j ω|} := by
    rw [hE, Set.compl_iInter]
    congr 1; ext j ω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  have hEc : P Eᶜ ≤ ENNReal.ofReal ((M : ℝ) ^ (1 - A ^ 2 / 2)) := by
    rw [hcomp]
    calc P (⋃ j, {ω | r < |V j ω|}) ≤ ∑ j, P {ω | r < |V j ω|} :=
          measure_iUnion_fintype_le _ _
      _ ≤ ∑ _j : Fin M, ENNReal.ofReal ((M : ℝ) ^ (-(A ^ 2) / 2)) :=
          Finset.sum_le_sum (fun j _ => htail j)
      _ = ENNReal.ofReal ((M : ℝ) ^ (1 - A ^ 2 / 2)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1
          rw [show (1 : ℝ) - A ^ 2 / 2 = 1 + (-(A ^ 2) / 2) by ring,
            Real.rpow_add hM0, Real.rpow_one]
  have hadd : P E + P Eᶜ = 1 := by rw [measure_add_measure_compl hEm, measure_univ]
  have hreal : (P E).toReal + (P Eᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hadd, ENNReal.toReal_one]
  have hle : (P Eᶜ).toReal ≤ (M : ℝ) ^ (1 - A ^ 2 / 2) :=
    ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hM0.le _) hEc
  linarith

end Dz291

open MeasureTheory ProbabilityTheory LassoDantzig.Dantzig in
theorem solution {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hdiag : ∀ j, (1 / (n : ℝ)) * ∑ i, X i j ^ 2 = 1)
    (βstar : Fin M → ℝ) (s : ℕ) (hs : 1 ≤ s) (hsM : s ≤ M) (hsparse : sparsity βstar ≤ s)
    (κ : ℝ) (hκ : 0 < κ) (hRE : RE X s 1 κ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hWm : ∀ i, Measurable (W i))
    (hWind : iIndepFun W P) (hWlaw : ∀ i, P.map (W i) = gaussianReal 0 (σ ^ 2).toNNReal)
    (A : ℝ) (hA : Real.sqrt 2 < A) (r : ℝ) (hr : r = A * σ * Real.sqrt (Real.log M / n)) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - (M : ℝ) ^ (1 - A ^ 2 / 2) ≤ (P E).toReal ∧
      ∀ ω ∈ E, ∀ βD : Fin M → ℝ,
        IsDantzig X (fun i => X.mulVec βstar i + W i ω) r βD →
        (∑ j, |βD j - βstar j| ≤ 8 * A / κ ^ 2 * σ * s * Real.sqrt (Real.log M / n)) ∧
        (∑ i, X.mulVec (βD - βstar) i ^ 2 ≤ 16 * A ^ 2 / κ ^ 2 * σ ^ 2 * s * Real.log M) ∧
        (∀ (m : ℕ) (κ' : ℝ), s ≤ m → s + m ≤ M → 0 < κ' → REm X s m 1 κ' →
          ∀ p : ℝ, 1 < p → p ≤ 2 →
            ∑ j, |βD j - βstar j| ^ p ≤
              (2 : ℝ) ^ (p - 1) * 8 * (1 + Real.sqrt ((s : ℝ) / m)) ^ (2 * (p - 1)) * s *
                (A * σ / κ' ^ 2 * Real.sqrt (Real.log M / n)) ^ p) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hlogpos : 0 < Real.log M := Real.log_pos (by linarith)
  have hApos : 0 < A := by
    have : 0 ≤ √2 := by positivity
    linarith
  have hrpos : 0 < r := by
    rw [hr]; have := Real.sqrt_pos.mpr (div_pos hlogpos hnR); positivity
  obtain ⟨hEm, hprob⟩ := Dz291.event_prob hn hM X hdiag P W σ hσ hWm hWind hWlaw A hA r hr
  refine ⟨_, hEm, hprob, ?_⟩
  intro ω hω βD hD
  obtain ⟨d1, d2, d3⟩ := Dz291.det_main hnR X βstar βD (fun i => W i ω) r hrpos s hs hsparse
    κ hκ hRE hω hD
  refine ⟨?_, ?_, ?_⟩
  · refine d1.trans (le_of_eq ?_)
    rw [hr]; ring
  · refine d2.trans (le_of_eq ?_)
    rw [hr, mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hlogpos.le hnR.le)]
    field_simp
  · intro m κ' h1 h2 h3 h4 p hp1 hp2
    have hu : r / κ' ^ 2 = A * σ / κ' ^ 2 * Real.sqrt (Real.log M / n) := by rw [hr]; ring
    rw [← hu]
    exact d3 m κ' h1 h2 h3 h4 p hp1 hp2
