-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_forall_integrable_unfoldedTorusPairIntegrand_jacquetVector3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/647112c5-2613-5385-80e9-4deb55c7eac0

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar

import Theorems.Thm_LanglandsTunnell_CubicInduction_godementInner3_mulShift_polyGauss3_continuousOn_and_decay
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_norm_W_diagOne_mul_inv_le_of_iwasawa
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_Wr_mul_abs_cpow_mul_inv_sq
import Theorems.Thm_LanglandsTunnell_CubicInduction_re_eq_zero_of_isArchCompAt_of_isUnitaryChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_unfoldedTorusPairIntegrand_jacquetVector3

set_option autoImplicit false

namespace W4DOM
open MeasureTheory Set Real

theorem integrable_abs_rpow_mul_exp_neg_mul_sq {b s : ℝ} (hb : 0 < b) (hs : -1 < s) :
    Integrable (fun x : ℝ => |x| ^ s * Real.exp (-b * x ^ 2)) := by
  have h0 : IntegrableOn (fun x : ℝ => |x| ^ s * Real.exp (-b * x ^ 2)) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_sq hb hs).congr_fun
      (fun x hx => by rw [abs_of_pos (mem_Ioi.mp hx)]) measurableSet_Ioi
  rw [← integrableOn_univ, ← Iio_union_Ici (a := (0:ℝ)), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, h0⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
  simp only [Function.comp_def, neg_sq, abs_neg]
  have : Neg.neg ⁻¹' Iio (0:ℝ) = Ioi 0 := by
    ext x; simp
  rw [this]; exact h0

theorem integrable_abs_rpow_mul_pow_mul_exp {s : ℝ} (hs : -1 < s) (n : ℕ) :
    Integrable (fun x : ℝ => |x| ^ s * (1 + x ^ 2) ^ n * Real.exp (-Real.pi * x ^ 2)) := by
  have hexp : ∀ x : ℝ, (1 + x ^ 2) ^ n =
      ∑ m ∈ Finset.range (n + 1), x ^ (2 * m) * (n.choose m : ℝ) := by
    intro x
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [one_pow, mul_one, pow_mul]
  have hterm : ∀ m : ℕ,
      Integrable (fun x : ℝ => |x| ^ s * x ^ (2 * m) * Real.exp (-Real.pi * x ^ 2)) := by
    intro m
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    have h := integrable_abs_rpow_mul_exp_neg_mul_sq Real.pi_pos (s := s + 2 * m) (by linarith)
    refine (integrable_congr (Filter.Eventually.of_forall fun x => ?_)).mp h
    show |x| ^ (s + 2 * (m:ℝ)) * Real.exp (-Real.pi * x ^ 2) = |x| ^ s * x ^ (2 * m) * Real.exp (-Real.pi * x ^ 2)
    rcases eq_or_ne x 0 with rfl | hx
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
      · have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
        have hne : s + 2 * (m:ℝ) ≠ 0 := by intro h0; linarith
        simp [Real.zero_rpow hne, hm.ne']
    · congr 1
      rw [Real.rpow_add (abs_pos.mpr hx), show (2 * (m:ℝ)) = ((2 * m : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast, pow_mul, pow_mul, sq_abs]
  have : (fun x : ℝ => |x| ^ s * (1 + x ^ 2) ^ n * Real.exp (-Real.pi * x ^ 2)) =
      fun x => ∑ m ∈ Finset.range (n + 1),
        (n.choose m : ℝ) * (|x| ^ s * x ^ (2 * m) * Real.exp (-Real.pi * x ^ 2)) := by
    funext x
    rw [hexp, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [this]
  exact integrable_finsetSum _ fun m _ => (hterm m).const_mul _

noncomputable def phi (s : ℝ) (n : ℕ) (x : ℝ) : ℝ := |x| ^ s * (1 + x ^ 2) ^ n * Real.exp (-Real.pi * x ^ 2)

theorem phi_nonneg (s : ℝ) (n : ℕ) (x : ℝ) : 0 ≤ phi s n x := by
  unfold phi; positivity

theorem integrable_phi {s : ℝ} (hs : -1 < s) (n : ℕ) : Integrable (phi s n) :=
  integrable_abs_rpow_mul_pow_mul_exp hs n

theorem integrable_prod_phi (s : Fin 2 → Fin 2 → ℝ) (hs : ∀ i j, -1 < s i j) (n : ℕ) :
    Integrable (fun e : Fin 2 → Fin 2 → ℝ => ∏ i, ∏ j, phi (s i j) n (e i j))
      (volume : Measure (Fin 2 → Fin 2 → ℝ)) := by
  have hrow : ∀ i : Fin 2, Integrable (fun r : Fin 2 → ℝ => ∏ j, phi (s i j) n (r j))
      (volume : Measure (Fin 2 → ℝ)) := by
    intro i
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun j => phi (s i j) n) fun j => integrable_phi (hs i j) n
  rw [volume_pi]
  exact Integrable.fintype_prod (f := fun i => fun r : Fin 2 → ℝ => ∏ j, phi (s i j) n (r j)) hrow

theorem ae_mem_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] {A : Set α} {B : Set β}
    (hA : ∀ᵐ x ∂μ, x ∈ A) (hB : ∀ᵐ y ∂ν, y ∈ B) :
    ∀ᵐ z ∂(μ.prod ν), z ∈ A ×ˢ B := by
  rw [ae_iff] at hA hB ⊢
  have hsub : {z : α × β | ¬ z ∈ A ×ˢ B} ⊆ {x | ¬ x ∈ A} ×ˢ (univ : Set β) ∪ (univ : Set α) ×ˢ {y | ¬ y ∈ B} := by
    intro z hz
    simp only [mem_prod, not_and_or, mem_setOf_eq] at hz
    rcases hz with h | h
    · exact Or.inl ⟨h, mem_univ _⟩
    · exact Or.inr ⟨mem_univ _, h⟩
  refine measure_mono_null hsub ?_
  refine le_antisymm ?_ bot_le
  calc (μ.prod ν) ({x | ¬ x ∈ A} ×ˢ univ ∪ univ ×ˢ {y | ¬ y ∈ B})
      ≤ (μ.prod ν) ({x | ¬ x ∈ A} ×ˢ univ) + (μ.prod ν) (univ ×ˢ {y | ¬ y ∈ B}) := measure_union_le _ _
    _ ≤ μ {x | ¬ x ∈ A} * ν univ + μ univ * ν {y | ¬ y ∈ B} :=
        add_le_add (Measure.prod_prod_le _ _) (Measure.prod_prod_le _ _)
    _ = 0 := by rw [hA, hB, zero_mul, mul_zero, add_zero]

theorem volume_fin2_fst_eq_zero : (volume : Measure (Fin 2 → ℝ)) {r | r 0 = 0} = 0 := by
  have h := (volume_preserving_finTwoArrow ℝ).measure_preimage
    (s := ({0} : Set ℝ) ×ˢ (univ : Set ℝ)) ((measurableSet_singleton 0).prod MeasurableSet.univ).nullMeasurableSet
  have hset : (⇑(MeasurableEquiv.finTwoArrow (α := ℝ))) ⁻¹' (({0} : Set ℝ) ×ˢ univ) = {r : Fin 2 → ℝ | r 0 = 0} := by
    ext r; simp [MeasurableEquiv.finTwoArrow_apply]
  rw [hset] at h
  rw [h, Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, zero_mul]

theorem volume_fin2_line_eq_zero (c d : ℝ) (hc : c ≠ 0) :
    (volume : Measure (Fin 2 → ℝ)) {r | c * r 1 - d * r 0 = 0} = 0 := by
  have hmeas : MeasurableSet {z : ℝ × ℝ | c * z.2 - d * z.1 = 0} :=
    (measurableSet_singleton 0).preimage (by fun_prop)
  have h := (volume_preserving_finTwoArrow ℝ).measure_preimage
    (s := {z : ℝ × ℝ | c * z.2 - d * z.1 = 0}) hmeas.nullMeasurableSet
  have hset : (⇑(MeasurableEquiv.finTwoArrow (α := ℝ))) ⁻¹' {z : ℝ × ℝ | c * z.2 - d * z.1 = 0} =
      {r : Fin 2 → ℝ | c * r 1 - d * r 0 = 0} := by
    ext r; simp [MeasurableEquiv.finTwoArrow_apply]
  rw [hset] at h
  rw [h, Measure.volume_eq_prod, Measure.measure_prod_null hmeas]
  refine Filter.Eventually.of_forall fun x => ?_
  have : Prod.mk x ⁻¹' {z : ℝ × ℝ | c * z.2 - d * z.1 = 0} = {d * x / c} := by
    ext y
    simp only [mem_preimage, mem_setOf_eq, mem_singleton_iff]
    constructor
    · intro h; field_simp; linarith
    · intro h; rw [h]; field_simp; ring
  simp [this]

theorem volume_setOf_det_eq_zero :
    (volume : Measure (Fin 2 → Fin 2 → ℝ)) {e | (Matrix.of e).det = 0} = 0 := by
  have hmeasT : MeasurableSet {z : (Fin 2 → ℝ) × (Fin 2 → ℝ) | z.1 0 * z.2 1 - z.1 1 * z.2 0 = 0} :=
    (measurableSet_singleton 0).preimage (by fun_prop)
  have h := (volume_preserving_finTwoArrow (Fin 2 → ℝ)).measure_preimage
    (s := {z : (Fin 2 → ℝ) × (Fin 2 → ℝ) | z.1 0 * z.2 1 - z.1 1 * z.2 0 = 0}) hmeasT.nullMeasurableSet
  have hset : (⇑(MeasurableEquiv.finTwoArrow (α := Fin 2 → ℝ))) ⁻¹'
      {z : (Fin 2 → ℝ) × (Fin 2 → ℝ) | z.1 0 * z.2 1 - z.1 1 * z.2 0 = 0} =
      {e : Fin 2 → Fin 2 → ℝ | (Matrix.of e).det = 0} := by
    ext e; simp [MeasurableEquiv.finTwoArrow_apply, Matrix.det_fin_two]
  rw [hset] at h
  rw [h, Measure.volume_eq_prod, Measure.measure_prod_null hmeasT]
  have hae : ∀ᵐ r ∂(volume : Measure (Fin 2 → ℝ)), r 0 ≠ 0 := by
    rw [ae_iff]; simpa using volume_fin2_fst_eq_zero
  filter_upwards [hae] with r hr
  have : Prod.mk r ⁻¹' {z : (Fin 2 → ℝ) × (Fin 2 → ℝ) | z.1 0 * z.2 1 - z.1 1 * z.2 0 = 0} =
      {r' : Fin 2 → ℝ | r 0 * r' 1 - r 1 * r' 0 = 0} := by
    ext r'; simp
  rw [this]
  exact volume_fin2_line_eq_zero (r 0) (r 1) hr

theorem ae_det_ne_zero : ∀ᵐ e ∂(volume : Measure (Fin 2 → Fin 2 → ℝ)), (Matrix.of e).det ≠ 0 := by
  rw [ae_iff]; simpa using volume_setOf_det_eq_zero

theorem ae_entry_ne_zero (j : Fin 2) : ∀ᵐ e ∂(volume : Measure (Fin 2 → Fin 2 → ℝ)), e j 0 ≠ 0 := by
  rw [ae_iff]
  have hset : {e : Fin 2 → Fin 2 → ℝ | ¬ e j 0 ≠ 0} = Set.univ.pi (fun i => if i = j then {r : Fin 2 → ℝ | r 0 = 0} else univ) := by
    ext e
    simp only [mem_setOf_eq, not_not, mem_univ_pi]
    constructor
    · intro h i; by_cases hij : i = j
      · subst hij; simpa
      · simp [hij]
    · intro h; simpa using h j
  rw [hset, volume_pi, Measure.pi_pi]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simpa using volume_fin2_fst_eq_zero

theorem ae_ne_zero_real : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
  rw [ae_iff]; simp

end W4DOM

namespace W4DOM
open MeasureTheory Set Real

theorem hadamard_fin_two (e : Matrix (Fin 2) (Fin 2) ℝ) :
    |e.det| ≤ Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) * Real.sqrt (e 0 1 ^ 2 + e 1 1 ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.abs_le_sqrt
  rw [Matrix.det_fin_two]
  nlinarith [sq_nonneg (e 0 0 * e 0 1 + e 1 0 * e 1 1)]

theorem inv_row_sq_sum (e : Matrix (Fin 2) (Fin 2) ℝ) (he : e.det ≠ 0) :
    ∑ i, (e⁻¹ 1 i) ^ 2 = (e 0 0 ^ 2 + e 1 0 ^ 2) / e.det ^ 2 := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]
  simp [Fin.sum_univ_two, Matrix.smul_apply]
  field_simp
  ring

theorem aux_T1_eq (d p lam : ℝ) (hd : 0 < d) (hp : 0 < p) :
    d⁻¹ * (p / d) ^ (-lam) = d ^ (lam - 1) * p ^ (-lam) := by
  rw [Real.div_rpow hp.le hd.le, Real.rpow_neg hd.le, Real.rpow_sub_one hd.ne']
  field_simp

theorem aux_T1_le (d p q lam : ℝ) (hd : 0 < d) (hp : 0 < p) (hq : 0 ≤ q) (hdpq : d ≤ p * q)
    (hlam : 1 ≤ lam) :
    d⁻¹ * (p / d) ^ (-lam) ≤ p ^ (-1 : ℝ) * q ^ (lam - 1) := by
  rw [aux_T1_eq d p lam hd hp]
  have h1 : d ^ (lam - 1) ≤ (p * q) ^ (lam - 1) := Real.rpow_le_rpow hd.le hdpq (by linarith)
  rw [Real.mul_rpow hp.le hq] at h1
  have h2 : p ^ (lam - 1) * q ^ (lam - 1) * p ^ (-lam) = p ^ (-1 : ℝ) * q ^ (lam - 1) := by
    rw [show p ^ (-1 : ℝ) = p ^ (lam - 1) * p ^ (-lam) by rw [← Real.rpow_add hp]; ring_nf]
    ring
  calc d ^ (lam - 1) * p ^ (-lam) ≤ p ^ (lam - 1) * q ^ (lam - 1) * p ^ (-lam) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hp.le _)
    _ = _ := h2

theorem aux_T2_le (d p q lam σ₀ : ℝ) (hd : 0 < d) (hp : 0 < p) (hq : 0 ≤ q) (hdpq : d ≤ p * q)
    (hlam : 1 + σ₀ ≤ lam) :
    d⁻¹ * (p / d) ^ (-lam) * (d * (p / d) ^ 2) ^ σ₀ ≤ p ^ (σ₀ - 1) * q ^ (lam - 1 - σ₀) := by
  have hρ : 0 < p / d := div_pos hp hd
  have hE : d⁻¹ * (p / d) ^ (-lam) * (d * (p / d) ^ 2) ^ σ₀ = d ^ (lam - 1 - σ₀) * p ^ (2 * σ₀ - lam) := by
    rw [Real.mul_rpow hd.le (by positivity), show ((p / d) ^ 2) ^ σ₀ = (p / d) ^ (2 * σ₀) by
      rw [Real.rpow_mul hρ.le, Real.rpow_two]]
    rw [Real.div_rpow hp.le hd.le, Real.div_rpow hp.le hd.le]
    rw [show lam - 1 - σ₀ = (lam - 1) + (-σ₀) by ring, Real.rpow_add hd, Real.rpow_sub_one hd.ne',
      show 2 * σ₀ - lam = 2 * σ₀ + (-lam) by ring, Real.rpow_add hp, Real.rpow_neg hd.le σ₀,
      Real.rpow_neg hp.le, Real.rpow_neg hd.le]
    have : d ^ lam ≠ 0 := (Real.rpow_pos_of_pos hd _).ne'
    have : d ^ σ₀ ≠ 0 := (Real.rpow_pos_of_pos hd _).ne'
    have : d ^ (2 * σ₀) ≠ 0 := (Real.rpow_pos_of_pos hd _).ne'
    have : p ^ lam ≠ 0 := (Real.rpow_pos_of_pos hp _).ne'
    have h2 : d ^ (2 * σ₀) = d ^ σ₀ * d ^ σ₀ := by rw [← Real.rpow_add hd]; ring_nf
    field_simp
    rw [h2]
    ring
  rw [hE]
  have h1 : d ^ (lam - 1 - σ₀) ≤ (p * q) ^ (lam - 1 - σ₀) := Real.rpow_le_rpow hd.le hdpq (by linarith)
  rw [Real.mul_rpow hp.le hq] at h1
  have h3 : p ^ (lam - 1 - σ₀) * q ^ (lam - 1 - σ₀) * p ^ (2 * σ₀ - lam) = p ^ (σ₀ - 1) * q ^ (lam - 1 - σ₀) := by
    rw [show p ^ (σ₀ - 1) = p ^ (lam - 1 - σ₀) * p ^ (2 * σ₀ - lam) by rw [← Real.rpow_add hp]; ring_nf]
    ring
  calc d ^ (lam - 1 - σ₀) * p ^ (2 * σ₀ - lam) ≤ p ^ (lam - 1 - σ₀) * q ^ (lam - 1 - σ₀) * p ^ (2 * σ₀ - lam) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hp.le _)
    _ = _ := h3

theorem aux_inv_norm_le (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    (Real.sqrt (x ^ 2 + y ^ 2)) ^ (-1 : ℝ) ≤ |x| ^ (-(1/2) : ℝ) * |y| ^ (-(1/2) : ℝ) := by
  have hxy : 0 < |x| * |y| := mul_pos (abs_pos.mpr hx) (abs_pos.mpr hy)
  rw [← Real.mul_rpow (abs_nonneg x) (abs_nonneg y), Real.rpow_neg hxy.le, Real.rpow_neg_one,
    ← Real.sqrt_eq_rpow]
  have hp : 0 < Real.sqrt (x ^ 2 + y ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [inv_le_inv₀ hp (Real.sqrt_pos.mpr hxy)]
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y, abs_nonneg x, abs_nonneg y]

theorem aux_rpow_le_one_add_sq_pow (q x : ℝ) (n : ℕ) (hq : 0 ≤ q) (hx : 0 ≤ x) (hxn : x ≤ 2 * n) :
    q ^ x ≤ (1 + q ^ 2) ^ n := by
  have h1 : q ^ x = (q ^ 2) ^ (x / 2) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hq]; ring_nf
  rw [h1]
  calc (q ^ 2) ^ (x / 2) ≤ (1 + q ^ 2) ^ (x / 2) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    _ ≤ (1 + q ^ 2) ^ ((n : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by nlinarith) (by linarith)
    _ = (1 + q ^ 2) ^ n := Real.rpow_natCast _ _

theorem continuousOn_rpow_mul_inv_pow (κ : ℝ) (N : ℕ) :
    ContinuousOn (fun u : ℝ => u ^ κ * ((1 + u ^ 2) ^ N)⁻¹) (Ioi 0) := by
  intro u hu
  have hu0 : u ≠ 0 := (mem_Ioi.mp hu).ne'
  refine ContinuousAt.continuousWithinAt ?_
  refine (Real.continuousAt_rpow_const u κ (Or.inl hu0)).mul ?_
  refine (ContinuousAt.inv₀ ?_ (by positivity))
  fun_prop

theorem integrableOn_rpow_mul_inv_pow (κ : ℝ) (N : ℕ) (hκ : -1 < κ) (hN : κ + 1 < 2 * N) :
    IntegrableOn (fun u : ℝ => u ^ κ * ((1 + u ^ 2) ^ N)⁻¹) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
  constructor
  · have hI : IntegrableOn (fun u : ℝ => u ^ κ) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' hκ)
    refine Integrable.mono' hI ?_ ?_
    · exact ((continuousOn_rpow_mul_inv_pow κ N).mono Ioc_subset_Ioi_self).aestronglyMeasurable
        measurableSet_Ioc
    · refine (ae_restrict_mem measurableSet_Ioc).mono fun u hu => ?_
      have hu0 : 0 < u := hu.1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have : ((1 + u ^ 2) ^ N)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by nlinarith))
      calc u ^ κ * ((1 + u ^ 2) ^ N)⁻¹ ≤ u ^ κ * 1 :=
            mul_le_mul_of_nonneg_left this (Real.rpow_nonneg hu0.le _)
        _ = u ^ κ := mul_one _
  · have hI : IntegrableOn (fun u : ℝ => u ^ (κ - 2 * N)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine Integrable.mono' hI ?_ ?_
    · exact ((continuousOn_rpow_mul_inv_pow κ N).mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
        measurableSet_Ioi
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun u hu => ?_
      have hu1 : 1 < u := hu
      have hu0 : 0 < u := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hle : ((1 + u ^ 2) ^ N)⁻¹ ≤ u ^ (-(2 * N : ℝ)) := by
        rw [Real.rpow_neg hu0.le, show (2 * N : ℝ) = ((2 * N : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_natCast, pow_mul]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by nlinarith) N)
      calc u ^ κ * ((1 + u ^ 2) ^ N)⁻¹ ≤ u ^ κ * u ^ (-(2 * N : ℝ)) :=
            mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hu0.le _)
        _ = u ^ (κ - 2 * N) := by rw [← Real.rpow_add hu0]; ring_nf

theorem yIntegral (κ : ℝ) (N : ℕ) (hκ : -1 < κ) (hN : κ + 1 < 2 * N) (B : ℝ) (hB : 0 < B) :
    IntegrableOn (fun y : ℝ => y ^ κ * ((1 + y ^ 2 * B) ^ N)⁻¹) (Ioi 0) ∧
      ∫ y in Ioi 0, y ^ κ * ((1 + y ^ 2 * B) ^ N)⁻¹ =
        (Real.sqrt B) ^ (-(κ + 1)) * ∫ u in Ioi 0, u ^ κ * ((1 + u ^ 2) ^ N)⁻¹ := by
  set g : ℝ → ℝ := fun u => u ^ κ * ((1 + u ^ 2) ^ N)⁻¹ with hg
  set b : ℝ := Real.sqrt B with hb
  have hb0 : 0 < b := Real.sqrt_pos.mpr hB
  have hbsq : b ^ 2 = B := Real.sq_sqrt hB.le
  have hpt : ∀ y ∈ Ioi (0:ℝ), y ^ κ * ((1 + y ^ 2 * B) ^ N)⁻¹ = b ^ (-κ) * g (b * y) := by
    intro y hy
    have hy0 : 0 ≤ y := le_of_lt (mem_Ioi.mp hy)
    simp only [hg]
    rw [Real.mul_rpow hb0.le hy0, Real.rpow_neg hb0.le]
    have : b ^ κ ≠ 0 := (Real.rpow_pos_of_pos hb0 κ).ne'
    field_simp
    rw [hbsq]
  have hgI : IntegrableOn g (Ioi 0) := integrableOn_rpow_mul_inv_pow κ N hκ hN
  have hcomp : IntegrableOn (fun y => g (b * y)) (Ioi 0) := by
    have := (integrableOn_Ioi_comp_mul_left_iff g 0 hb0).mpr (by simpa using hgI)
    exact this
  constructor
  · have h' : IntegrableOn (fun y => b ^ (-κ) * g (b * y)) (Ioi 0) := hcomp.const_mul (b ^ (-κ))
    exact h'.congr_fun (fun y hy => (hpt y hy).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
    have := integral_comp_mul_left_Ioi g 0 hb0
    rw [mul_zero] at this
    rw [this, smul_eq_mul, ← mul_assoc]
    congr 1
    rw [Real.rpow_neg hb0.le, Real.rpow_neg hb0.le, Real.rpow_add hb0, Real.rpow_one]
    field_simp

end W4DOM

namespace W4DOM
open MeasureTheory Set Real

theorem one_add_add_le_mul (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 1 + a + b ≤ (1 + a) * (1 + b) := by
  nlinarith

noncomputable def Mmaj (n : ℕ) (x00 x01 x10 x11 : ℝ) : ℝ :=
  |x00| ^ (-(1/2):ℝ) * |x10| ^ (-(1/2):ℝ) * ((1 + x00 ^ 2) ^ n * (1 + x10 ^ 2) ^ n) *
    ((1 + x01 ^ 2) ^ n * (1 + x11 ^ 2) ^ n)

theorem Mmaj_nonneg (n : ℕ) (x00 x01 x10 x11 : ℝ) : 0 ≤ Mmaj n x00 x01 x10 x11 := by
  unfold Mmaj; positivity

theorem one_add_sq_pow_le (x y : ℝ) (n : ℕ) :
    (1 + (Real.sqrt (x ^ 2 + y ^ 2)) ^ 2) ^ n ≤ (1 + x ^ 2) ^ n * (1 + y ^ 2) ^ n := by
  rw [← mul_pow, Real.sq_sqrt (by positivity)]
  exact pow_le_pow_left₀ (by positivity) (by nlinarith [one_add_add_le_mul _ _ (sq_nonneg x) (sq_nonneg y)]) n

theorem torus_T1_le (x00 x01 x10 x11 d lam : ℝ) (n : ℕ)
    (h00 : x00 ≠ 0) (h10 : x10 ≠ 0) (hd : 0 < d)
    (hdet : d ≤ Real.sqrt (x00 ^ 2 + x10 ^ 2) * Real.sqrt (x01 ^ 2 + x11 ^ 2))
    (hlam : 1 ≤ lam) (hn : lam ≤ n) :
    d⁻¹ * (Real.sqrt (x00 ^ 2 + x10 ^ 2) / d) ^ (-lam) ≤ Mmaj n x00 x01 x10 x11 := by
  set p := Real.sqrt (x00 ^ 2 + x10 ^ 2) with hp
  set q := Real.sqrt (x01 ^ 2 + x11 ^ 2) with hq
  have hp0 : 0 < p := Real.sqrt_pos.mpr (by positivity)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hT1 : d⁻¹ * (p / d) ^ (-lam) ≤ p ^ (-1:ℝ) * q ^ (lam - 1) :=
    aux_T1_le d p q lam hd hp0 hq0 hdet hlam
  have hpinv : p ^ (-1:ℝ) ≤ |x00| ^ (-(1/2):ℝ) * |x10| ^ (-(1/2):ℝ) := aux_inv_norm_le x00 x10 h00 h10
  have hq1 : q ^ (lam - 1) ≤ (1 + q ^ 2) ^ n :=
    aux_rpow_le_one_add_sq_pow q (lam - 1) n hq0 (by linarith) (by linarith)
  have hq' : (1 + q ^ 2) ^ n ≤ (1 + x01 ^ 2) ^ n * (1 + x11 ^ 2) ^ n := one_add_sq_pow_le x01 x11 n
  have h1p : 1 ≤ (1 + x00 ^ 2) ^ n * (1 + x10 ^ 2) ^ n :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by nlinarith)) (one_le_pow₀ (by nlinarith))
  have hX0 : 0 ≤ |x00| ^ (-(1/2):ℝ) * |x10| ^ (-(1/2):ℝ) := by positivity
  calc d⁻¹ * (p / d) ^ (-lam) ≤ p ^ (-1:ℝ) * q ^ (lam - 1) := hT1
    _ ≤ (|x00| ^ (-(1/2):ℝ) * |x10| ^ (-(1/2):ℝ)) * ((1 + x01 ^ 2) ^ n * (1 + x11 ^ 2) ^ n) :=
        mul_le_mul hpinv (hq1.trans hq') (Real.rpow_nonneg hq0 _) hX0
    _ = (|x00| ^ (-(1/2):ℝ) * |x10| ^ (-(1/2):ℝ)) * 1 * ((1 + x01 ^ 2) ^ n * (1 + x11 ^ 2) ^ n) := by ring
    _ ≤ (|x00| ^ (-(1/2):ℝ) * |x10| ^ (-(1/2):ℝ)) * ((1 + x00 ^ 2) ^ n * (1 + x10 ^ 2) ^ n) *
          ((1 + x01 ^ 2) ^ n * (1 + x11 ^ 2) ^ n) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1p hX0) (by positivity)
    _ = Mmaj n x00 x01 x10 x11 := by rw [Mmaj]

theorem torus_T2_le (x00 x01 x10 x11 d lam σ₀ : ℝ) (n : ℕ)
    (h00 : x00 ≠ 0) (h10 : x10 ≠ 0) (hd : 0 < d)
    (hdet : d ≤ Real.sqrt (x00 ^ 2 + x10 ^ 2) * Real.sqrt (x01 ^ 2 + x11 ^ 2))
    (hσ₀ : 0 ≤ σ₀) (hlam : 1 + σ₀ ≤ lam) (hn : lam ≤ n) :
    d⁻¹ * (Real.sqrt (x00 ^ 2 + x10 ^ 2) / d) ^ (-lam) * (d * (Real.sqrt (x00 ^ 2 + x10 ^ 2) / d) ^ 2) ^ σ₀
      ≤ Mmaj n x00 x01 x10 x11 := by
  set p := Real.sqrt (x00 ^ 2 + x10 ^ 2) with hp
  set q := Real.sqrt (x01 ^ 2 + x11 ^ 2) with hq
  have hp0 : 0 < p := Real.sqrt_pos.mpr (by positivity)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hT2 : d⁻¹ * (p / d) ^ (-lam) * (d * (p / d) ^ 2) ^ σ₀ ≤ p ^ (σ₀ - 1) * q ^ (lam - 1 - σ₀) :=
    aux_T2_le d p q lam σ₀ hd hp0 hq0 hdet hlam
  have hpinv : p ^ (-1:ℝ) ≤ |x00| ^ (-(1/2):ℝ) * |x10| ^ (-(1/2):ℝ) := aux_inv_norm_le x00 x10 h00 h10
  have hX0 : 0 ≤ |x00| ^ (-(1/2):ℝ) * |x10| ^ (-(1/2):ℝ) := by positivity
  have hpσ : p ^ (σ₀ - 1) ≤ (|x00| ^ (-(1/2):ℝ) * |x10| ^ (-(1/2):ℝ)) * ((1 + x00 ^ 2) ^ n * (1 + x10 ^ 2) ^ n) := by
    rw [show σ₀ - 1 = (-1:ℝ) + σ₀ by ring, Real.rpow_add hp0]
    exact mul_le_mul hpinv
      ((aux_rpow_le_one_add_sq_pow p σ₀ n hp0.le hσ₀ (by linarith)).trans (one_add_sq_pow_le x00 x10 n))
      (Real.rpow_nonneg hp0.le _) hX0
  have hq2 : q ^ (lam - 1 - σ₀) ≤ (1 + x01 ^ 2) ^ n * (1 + x11 ^ 2) ^ n :=
    (aux_rpow_le_one_add_sq_pow q _ n hq0 (by linarith) (by linarith)).trans (one_add_sq_pow_le x01 x11 n)
  calc d⁻¹ * (p / d) ^ (-lam) * (d * (p / d) ^ 2) ^ σ₀ ≤ p ^ (σ₀ - 1) * q ^ (lam - 1 - σ₀) := hT2
    _ ≤ (|x00| ^ (-(1/2):ℝ) * |x10| ^ (-(1/2):ℝ)) * ((1 + x00 ^ 2) ^ n * (1 + x10 ^ 2) ^ n) *
          ((1 + x01 ^ 2) ^ n * (1 + x11 ^ 2) ^ n) :=
        mul_le_mul hpσ hq2 (Real.rpow_nonneg hq0 _) (by positivity)
    _ = Mmaj n x00 x01 x10 x11 := by rw [Mmaj]

theorem torus_le (x00 x01 x10 x11 d lam σ₀ I₁ I₂ ca : ℝ) (n : ℕ)
    (h00 : x00 ≠ 0) (h10 : x10 ≠ 0) (hd : 0 < d)
    (hdet : d ≤ Real.sqrt (x00 ^ 2 + x10 ^ 2) * Real.sqrt (x01 ^ 2 + x11 ^ 2))
    (hσ₀ : 0 ≤ σ₀) (hlam : 1 + σ₀ ≤ lam) (hn : lam ≤ n) (hI₁ : 0 ≤ I₁) (hI₂ : 0 ≤ I₂) (hca : 0 ≤ ca) :
    d⁻¹ * (Real.sqrt (x00 ^ 2 + x10 ^ 2) / d) ^ (-lam) *
        (I₁ + ca * (d * (Real.sqrt (x00 ^ 2 + x10 ^ 2) / d) ^ 2) ^ σ₀ * I₂)
      ≤ (I₁ + ca * I₂) * Mmaj n x00 x01 x10 x11 := by
  have hT1' := torus_T1_le x00 x01 x10 x11 d lam n h00 h10 hd hdet (by linarith) hn
  have hT2' := torus_T2_le x00 x01 x10 x11 d lam σ₀ n h00 h10 hd hdet hσ₀ hlam hn
  set T := d⁻¹ * (Real.sqrt (x00 ^ 2 + x10 ^ 2) / d) ^ (-lam) with hT
  set U := (d * (Real.sqrt (x00 ^ 2 + x10 ^ 2) / d) ^ 2) ^ σ₀ with hU
  set M := Mmaj n x00 x01 x10 x11 with hM
  have ha : T * I₁ ≤ M * I₁ := mul_le_mul_of_nonneg_right hT1' hI₁
  have hb : ca * ((T * U) * I₂) ≤ ca * (M * I₂) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hT2' hI₂) hca
  calc T * (I₁ + ca * U * I₂) = T * I₁ + ca * ((T * U) * I₂) := by ring
    _ ≤ M * I₁ + ca * (M * I₂) := add_le_add ha hb
    _ = (I₁ + ca * I₂) * M := by ring

noncomputable def Gmaj (A : ℕ) (x00 x01 x10 x11 : ℝ) : ℝ :=
  ((1 + x00 ^ 2) ^ A * (1 + x01 ^ 2) ^ A * (1 + x10 ^ 2) ^ A * (1 + x11 ^ 2) ^ A) *
    (Real.exp (-Real.pi * x00 ^ 2) * Real.exp (-Real.pi * x01 ^ 2) * Real.exp (-Real.pi * x10 ^ 2) *
      Real.exp (-Real.pi * x11 ^ 2))

theorem gauss_le (x00 x01 x10 x11 : ℝ) (A : ℕ) :
    (1 + (x00 ^ 2 + x01 ^ 2 + x10 ^ 2 + x11 ^ 2)) ^ A *
        Real.exp (-Real.pi * (x00 ^ 2 + x01 ^ 2 + x10 ^ 2 + x11 ^ 2)) ≤ Gmaj A x00 x01 x10 x11 := by
  have hexp : Real.exp (-Real.pi * (x00 ^ 2 + x01 ^ 2 + x10 ^ 2 + x11 ^ 2)) =
      Real.exp (-Real.pi * x00 ^ 2) * Real.exp (-Real.pi * x01 ^ 2) *
        Real.exp (-Real.pi * x10 ^ 2) * Real.exp (-Real.pi * x11 ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [Gmaj, hexp]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [← mul_pow, ← mul_pow, ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ A
  have h1 := one_add_add_le_mul (x00 ^ 2) (x01 ^ 2) (sq_nonneg _) (sq_nonneg _)
  have h2 := one_add_add_le_mul (x00 ^ 2 + x01 ^ 2) (x10 ^ 2) (by positivity) (sq_nonneg _)
  have h3 := one_add_add_le_mul (x00 ^ 2 + x01 ^ 2 + x10 ^ 2) (x11 ^ 2) (by positivity) (sq_nonneg _)
  calc 1 + (x00 ^ 2 + x01 ^ 2 + x10 ^ 2 + x11 ^ 2) = 1 + (x00 ^ 2 + x01 ^ 2 + x10 ^ 2) + x11 ^ 2 := by ring
    _ ≤ (1 + (x00 ^ 2 + x01 ^ 2 + x10 ^ 2)) * (1 + x11 ^ 2) := h3
    _ = (1 + (x00 ^ 2 + x01 ^ 2) + x10 ^ 2) * (1 + x11 ^ 2) := by ring
    _ ≤ ((1 + (x00 ^ 2 + x01 ^ 2)) * (1 + x10 ^ 2)) * (1 + x11 ^ 2) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = ((1 + x00 ^ 2 + x01 ^ 2) * (1 + x10 ^ 2)) * (1 + x11 ^ 2) := by ring
    _ ≤ (((1 + x00 ^ 2) * (1 + x01 ^ 2)) * (1 + x10 ^ 2)) * (1 + x11 ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity)) (by positivity)

theorem Mmaj_mul_Gmaj (n A : ℕ) (x00 x01 x10 x11 : ℝ) :
    Mmaj n x00 x01 x10 x11 * Gmaj A x00 x01 x10 x11 =
      (phi (-(1/2)) (n + A) x00 * phi 0 (n + A) x01) * (phi (-(1/2)) (n + A) x10 * phi 0 (n + A) x11) := by
  simp only [phi, Mmaj, Gmaj, Real.rpow_zero, pow_add]; ring

theorem key_bound (x00 x01 x10 x11 d lam σ₀ I₁ I₂ ca : ℝ) (n A : ℕ)
    (h00 : x00 ≠ 0) (h10 : x10 ≠ 0) (hd : 0 < d)
    (hdet : d ≤ Real.sqrt (x00 ^ 2 + x10 ^ 2) * Real.sqrt (x01 ^ 2 + x11 ^ 2))
    (hσ₀ : 0 ≤ σ₀) (hlam : 1 + σ₀ ≤ lam) (hn : lam ≤ n) (hI₁ : 0 ≤ I₁) (hI₂ : 0 ≤ I₂) (hca : 0 ≤ ca) :
    d⁻¹ * (Real.sqrt (x00 ^ 2 + x10 ^ 2) / d) ^ (-lam) *
        (I₁ + ca * (d * (Real.sqrt (x00 ^ 2 + x10 ^ 2) / d) ^ 2) ^ σ₀ * I₂) *
        ((1 + (x00 ^ 2 + x01 ^ 2 + x10 ^ 2 + x11 ^ 2)) ^ A *
          Real.exp (-Real.pi * (x00 ^ 2 + x01 ^ 2 + x10 ^ 2 + x11 ^ 2))) ≤
      (I₁ + ca * I₂) *
        ((phi (-(1/2)) (n + A) x00 * phi 0 (n + A) x01) * (phi (-(1/2)) (n + A) x10 * phi 0 (n + A) x11)) := by
  rw [← Mmaj_mul_Gmaj]
  calc _ ≤ ((I₁ + ca * I₂) * Mmaj n x00 x01 x10 x11) * Gmaj A x00 x01 x10 x11 :=
        mul_le_mul (torus_le x00 x01 x10 x11 d lam σ₀ I₁ I₂ ca n h00 h10 hd hdet hσ₀ hlam hn hI₁ hI₂ hca)
          (gauss_le x00 x01 x10 x11 A) (by positivity)
          (mul_nonneg (by positivity) (Mmaj_nonneg _ _ _ _ _))
    _ = _ := by ring

end W4DOM

namespace W4DOM
open MeasureTheory Set Real LanglandsTunnell LanglandsTunnell.Converse

theorem continuousOn_quasiChar (u : ℂ) (a : ZMod 2) :
    ContinuousOn (fun y : ℝ => ArchR.quasiChar u a y) {y | y ≠ 0} := by
  intro y hy
  apply ContinuousAt.continuousWithinAt
  unfold ArchR.quasiChar
  refine ContinuousAt.mul ?_ ?_
  · exact (Complex.continuousAt_ofReal_cpow_const |y| u (Or.inr (abs_ne_zero.mpr hy))).comp
      continuous_abs.continuousAt
  · by_cases ha : a = 0
    · simp only [ha, if_true]; exact continuousAt_const
    · simp only [ha, if_false]
      have hg : Continuous (fun σ : SignType => ((σ : ℝ) : ℂ)) := continuous_of_discreteTopology
      exact hg.continuousAt.comp (continuousAt_sign_of_ne_zero hy)

theorem norm_quasiChar (u : ℂ) (a : ZMod 2) (y : ℝ) (hy : y ≠ 0) :
    ‖ArchR.quasiChar u a y‖ = |y| ^ u.re := by
  unfold ArchR.quasiChar
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr hy)]
  split_ifs with ha
  · rw [norm_one, mul_one]
  · rcases lt_or_gt_of_ne hy with h | h
    · rw [sign_neg h]; simp
    · rw [sign_pos h]; simp

theorem norm_c_eq_one (u : ℂ) (hu : u.re = 0) (a₃ : ZMod 2) (x : ℝ) (hx : x ≠ 0) :
    ‖ArchR.quasiChar (u + 2) a₃ x * (((|x| ^ 2)⁻¹ : ℝ) : ℂ)‖ = 1 := by
  rw [norm_mul, norm_quasiChar _ _ x hx, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_pow, abs_abs,
    Complex.add_re, hu, zero_add, show (2:ℂ).re = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have : |x| ^ 2 ≠ 0 := pow_ne_zero _ (abs_ne_zero.mpr hx)
  field_simp

theorem continuous_det_of : Continuous fun e : Fin 2 → Fin 2 → ℝ => (Matrix.of e).det :=
  Continuous.matrix_det (A := fun e : Fin 2 → Fin 2 → ℝ => Matrix.of e) continuous_id

theorem continuousOn_inv_of :
    ContinuousOn (fun e : Fin 2 → Fin 2 → ℝ => (Matrix.of e)⁻¹) {e | (Matrix.of e).det ≠ 0} := by
  have h : ∀ e : Fin 2 → Fin 2 → ℝ, (Matrix.of e)⁻¹ = ((Matrix.of e).det)⁻¹ • (Matrix.of e).adjugate := by
    intro e; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp_rw [h]
  exact (continuous_det_of.continuousOn.inv₀ fun e he => he).smul
    (Continuous.matrix_adjugate (A := fun e : Fin 2 → Fin 2 → ℝ => Matrix.of e) continuous_id).continuousOn

theorem continuous_diagOne_mul (a : ℝ) : Continuous fun t : ℝ => ArchR.diagOne (a * t) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [ArchR.diagOne] <;> fun_prop

theorem det_diagOne_mul_inv (x : ℝ) (e : Matrix (Fin 2) (Fin 2) ℝ) (_he : e.det ≠ 0) :
    (ArchR.diagOne x * e⁻¹).det = x * e.det⁻¹ := by
  rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  simp [ArchR.diagOne, Matrix.det_fin_two_of]

theorem aesm_of_continuousOn_compl_zero {f : ℝ → ℂ} (hf : ContinuousOn f {t | t ≠ 0}) :
    AEStronglyMeasurable f (volume : Measure ℝ) := by
  have h := hf.aestronglyMeasurable (μ := volume) isOpen_ne.measurableSet
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ {t : ℝ | t ≠ 0} := ae_ne_zero_real
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at h

theorem continuousOn_WD {WD : Matrix (Fin 2) (Fin 2) ℝ → ℂ}
    (hWD : ContinuousOn (ArchR.asPi WD) ArchR.glSet) (a : ℝ) (ha : a ≠ 0) :
    ContinuousOn (fun q : (Fin 2 → Fin 2 → ℝ) × ℝ => WD (ArchR.diagOne (a * q.2) * (Matrix.of q.1)⁻¹))
      {q | (Matrix.of q.1).det ≠ 0 ∧ q.2 ≠ 0} := by
  have hinner : ContinuousOn
      (fun q : (Fin 2 → Fin 2 → ℝ) × ℝ => ArchR.diagOne (a * q.2) * (Matrix.of q.1)⁻¹)
      {q | (Matrix.of q.1).det ≠ 0 ∧ q.2 ≠ 0} :=
    ((continuous_diagOne_mul a).comp continuous_snd).continuousOn.mul
      (continuousOn_inv_of.comp continuous_fst.continuousOn fun q hq => hq.1)
  have h := hWD.comp hinner (fun q hq => by
    show (Matrix.of (ArchR.diagOne (a * q.2) * (Matrix.of q.1)⁻¹)).det ≠ 0
    have : Matrix.of (ArchR.diagOne (a * q.2) * (Matrix.of q.1)⁻¹) = ArchR.diagOne (a * q.2) * (Matrix.of q.1)⁻¹ := rfl
    rw [this, det_diagOne_mul_inv _ _ hq.1]
    exact mul_ne_zero (mul_ne_zero ha hq.2) (inv_ne_zero hq.1))
  exact h

theorem continuousOn_G {Gf : ℝ → Matrix (Fin 2) (Fin 2) ℝ → ℂ}
    (hG : ContinuousOn (fun p : ℝ × Matrix (Fin 2) (Fin 2) ℝ => Gf p.1 p.2) {p | p.2.det ≠ 0}) :
    ContinuousOn (fun q : (Fin 2 → Fin 2 → ℝ) × ℝ => Gf q.2 (Matrix.of q.1)) {q | (Matrix.of q.1).det ≠ 0} :=
  hG.comp (continuous_snd.prodMk continuous_fst).continuousOn (fun _ hq => hq)

theorem sum_sq_pos_of_det_ne_zero (e : Matrix (Fin 2) (Fin 2) ℝ) (he : e.det ≠ 0) :
    0 < e 0 0 ^ 2 + e 1 0 ^ 2 := by
  rcases (eq_or_ne (e 0 0) 0) with h0 | h0
  · rcases (eq_or_ne (e 1 0) 0) with h1 | h1
    · exact absurd (by rw [Matrix.det_fin_two, h0, h1]; ring) he
    · positivity
  · positivity

theorem inv_row_sq_sum_pos (e : Matrix (Fin 2) (Fin 2) ℝ) (he : e.det ≠ 0) :
    0 < ∑ i, (e⁻¹ 1 i) ^ 2 := by
  rw [inv_row_sq_sum e he]
  exact div_pos (sum_sq_pos_of_det_ne_zero e he) (by positivity)

def Uset : Set ((Fin 2 → Fin 2 → ℝ) × ℝ × ℝ) :=
  {q | (Matrix.of q.1).det ≠ 0 ∧ q.2.1 ≠ 0 ∧ 0 < q.2.2}

theorem isOpen_Uset : IsOpen Uset := by
  have h1 : IsOpen {q : (Fin 2 → Fin 2 → ℝ) × ℝ × ℝ | (Matrix.of q.1).det ≠ 0} :=
    isOpen_ne_fun (continuous_det_of.comp continuous_fst) continuous_const
  have h2 : IsOpen {q : (Fin 2 → Fin 2 → ℝ) × ℝ × ℝ | q.2.1 ≠ 0} :=
    isOpen_ne_fun (continuous_fst.comp continuous_snd) continuous_const
  have h3 : IsOpen {q : (Fin 2 → Fin 2 → ℝ) × ℝ × ℝ | 0 < q.2.2} :=
    isOpen_lt continuous_const (continuous_snd.comp continuous_snd)
  have : Uset = {q : (Fin 2 → Fin 2 → ℝ) × ℝ × ℝ | (Matrix.of q.1).det ≠ 0} ∩
      ({q : (Fin 2 → Fin 2 → ℝ) × ℝ × ℝ | q.2.1 ≠ 0} ∩ {q | 0 < q.2.2}) := by
    ext q; simp [Uset]
  rw [this]
  exact h1.inter (h2.inter h3)

theorem ae_mem_Uset :
    ∀ᵐ q ∂((volume : Measure (Fin 2 → Fin 2 → ℝ)).prod
        ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0)))), q ∈ Uset := by
  have h := ae_mem_prod (μ := (volume : Measure (Fin 2 → Fin 2 → ℝ))) ae_det_ne_zero
    (ae_mem_prod (μ := (volume : Measure ℝ)) ae_ne_zero_real
      (ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioi (a := (0:ℝ)))))
  exact h.mono fun q hq => ⟨hq.1, hq.2.1, hq.2.2⟩

theorem continuousOn_R
    (c : ℝ → ℂ) (hc : ContinuousOn c {x | x ≠ 0})
    (WD : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (hWD : ContinuousOn (ArchR.asPi WD) ArchR.glSet) (a : ℝ) (ha : a ≠ 0)
    (z : ℂ) (Gf : ℝ → Matrix (Fin 2) (Fin 2) ℝ → ℂ)
    (hG : ContinuousOn (fun p : ℝ × Matrix (Fin 2) (Fin 2) ℝ => Gf p.1 p.2) {p | p.2.det ≠ 0}) :
    ContinuousOn (fun q : (Fin 2 → Fin 2 → ℝ) × ℝ × ℝ =>
      c (Matrix.of q.1).det * (((|(Matrix.of q.1).det| ^ 2)⁻¹ : ℝ) : ℂ) *
        WD (ArchR.diagOne (a * q.2.1) * (Matrix.of q.1)⁻¹) *
        (((q.2.2 : ℝ) : ℂ) ^ z * Gf q.2.2 (Matrix.of q.1))) Uset := by
  have hA : ContinuousOn (fun q : (Fin 2 → Fin 2 → ℝ) × ℝ × ℝ => c (Matrix.of q.1).det) Uset :=
    hc.comp (continuous_det_of.comp continuous_fst).continuousOn (fun q hq => hq.1)
  have hB : ContinuousOn (fun q : (Fin 2 → Fin 2 → ℝ) × ℝ × ℝ =>
      (((|(Matrix.of q.1).det| ^ 2)⁻¹ : ℝ) : ℂ)) Uset := by
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact (((continuous_det_of.comp continuous_fst).abs.pow 2).continuousOn.inv₀
      (fun q hq => pow_ne_zero _ (abs_ne_zero.mpr hq.1)))
  have hC : ContinuousOn (fun q : (Fin 2 → Fin 2 → ℝ) × ℝ × ℝ =>
      WD (ArchR.diagOne (a * q.2.1) * (Matrix.of q.1)⁻¹)) Uset := by
    have hinner : ContinuousOn
        (fun q : (Fin 2 → Fin 2 → ℝ) × ℝ × ℝ => ArchR.diagOne (a * q.2.1) * (Matrix.of q.1)⁻¹) Uset :=
      ((continuous_diagOne_mul a).comp (continuous_fst.comp continuous_snd)).continuousOn.mul
        (continuousOn_inv_of.comp continuous_fst.continuousOn fun q hq => hq.1)
    refine hWD.comp hinner (fun q hq => ?_)
    show (Matrix.of (ArchR.diagOne (a * q.2.1) * (Matrix.of q.1)⁻¹)).det ≠ 0
    have : Matrix.of (ArchR.diagOne (a * q.2.1) * (Matrix.of q.1)⁻¹) =
        ArchR.diagOne (a * q.2.1) * (Matrix.of q.1)⁻¹ := rfl
    rw [this, det_diagOne_mul_inv _ _ hq.1]
    exact mul_ne_zero (mul_ne_zero ha hq.2.1) (inv_ne_zero hq.1)
  have hD : ContinuousOn (fun q : (Fin 2 → Fin 2 → ℝ) × ℝ × ℝ => ((q.2.2 : ℝ) : ℂ) ^ z) Uset := by
    intro q hq
    have h1 : ContinuousAt (fun q : (Fin 2 → Fin 2 → ℝ) × ℝ × ℝ => q.2.2) q :=
      (continuous_snd.comp continuous_snd).continuousAt
    have h2 : ContinuousAt (fun y : ℝ => ((y : ℝ) : ℂ) ^ z) q.2.2 :=
      Complex.continuousAt_ofReal_cpow_const q.2.2 z (Or.inr (ne_of_gt hq.2.2))
    exact (ContinuousAt.comp (f := fun q : (Fin 2 → Fin 2 → ℝ) × ℝ × ℝ => q.2.2) h2 h1).continuousWithinAt
  have hE : ContinuousOn (fun q : (Fin 2 → Fin 2 → ℝ) × ℝ × ℝ => Gf q.2.2 (Matrix.of q.1)) Uset := by
    have hf : Continuous (fun q : (Fin 2 → Fin 2 → ℝ) × ℝ × ℝ => (q.1, q.2.2)) :=
      continuous_fst.prodMk (continuous_snd.comp continuous_snd)
    exact (continuousOn_G hG).comp hf.continuousOn (fun q hq => hq.1)
  exact ((hA.mul hB).mul hC).mul (hD.mul hE)

theorem aesm_H
    (c : ℝ → ℂ) (hc : ContinuousOn c {x | x ≠ 0})
    (Wr₀ : ℝ → ℂ) (s : ℂ)
    (hw : AEStronglyMeasurable
      (fun t : ℝ => Wr₀ t * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) volume)
    (WD : Matrix (Fin 2) (Fin 2) ℝ → ℂ) (hWD : ContinuousOn (ArchR.asPi WD) ArchR.glSet) (a : ℝ) (ha : a ≠ 0)
    (z : ℂ) (Gf : ℝ → Matrix (Fin 2) (Fin 2) ℝ → ℂ)
    (hG : ContinuousOn (fun p : ℝ × Matrix (Fin 2) (Fin 2) ℝ => Gf p.1 p.2) {p | p.2.det ≠ 0}) :
    AEStronglyMeasurable
      (fun q : (Fin 2 → Fin 2 → ℝ) × ℝ × ℝ =>
        c (Matrix.of q.1).det * (((|(Matrix.of q.1).det| ^ 2)⁻¹ : ℝ) : ℂ) *
          (Wr₀ q.2.1 * WD (ArchR.diagOne (a * q.2.1) * (Matrix.of q.1)⁻¹) *
            (((|q.2.1| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.2.1 ^ 2)⁻¹ : ℝ) : ℂ)) *
          (((q.2.2 : ℝ) : ℂ) ^ z * Gf q.2.2 (Matrix.of q.1)))
      ((volume : Measure (Fin 2 → Fin 2 → ℝ)).prod
        ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0)))) := by
  have h1 : AEStronglyMeasurable (fun q : (Fin 2 → Fin 2 → ℝ) × ℝ × ℝ =>
      Wr₀ q.2.1 * (((|q.2.1| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.2.1 ^ 2)⁻¹ : ℝ) : ℂ))
      ((volume : Measure (Fin 2 → Fin 2 → ℝ)).prod
        ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0)))) :=
    (hw.comp_fst (ν := (volume : Measure ℝ).restrict (Ioi 0))).comp_snd
      (μ := (volume : Measure (Fin 2 → Fin 2 → ℝ)))
  have hRm : AEStronglyMeasurable (fun q : (Fin 2 → Fin 2 → ℝ) × ℝ × ℝ =>
      c (Matrix.of q.1).det * (((|(Matrix.of q.1).det| ^ 2)⁻¹ : ℝ) : ℂ) *
        WD (ArchR.diagOne (a * q.2.1) * (Matrix.of q.1)⁻¹) *
        (((q.2.2 : ℝ) : ℂ) ^ z * Gf q.2.2 (Matrix.of q.1)))
      ((volume : Measure (Fin 2 → Fin 2 → ℝ)).prod
        ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0)))) := by
    have h := (continuousOn_R c hc WD hWD a ha z Gf hG).aestronglyMeasurable
      (μ := (volume : Measure (Fin 2 → Fin 2 → ℝ)).prod
        ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0)))) isOpen_Uset.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem ae_mem_Uset] at h
  refine (h1.mul hRm).congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [Pi.mul_apply]
  ring

end W4DOM

namespace W4DOM
open MeasureTheory Set Real LanglandsTunnell LanglandsTunnell.Converse

theorem norm_w (Wr₀ : ℝ → ℂ) (z : ℂ) (t : ℝ) (ht : t ≠ 0) :
    ‖Wr₀ t * (((|t| : ℝ) : ℂ) ^ (z - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)‖ =
      ‖Wr₀ t‖ * |t| ^ (z.re - 1 / 2) * (t ^ 2)⁻¹ := by
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr ht), Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t))]
  congr 2
  simp

theorem psi_section (Wr₀ : ℝ → ℂ) (WD : Matrix (Fin 2) (Fin 2) ℝ → ℂ)
    (hWD : ContinuousOn (ArchR.asPi WD) ArchR.glSet) (a : ℝ) (ha : a ≠ 0) (s : ℂ) (σ₀ C₂ cc : ℝ)
    (_hC₂ : 0 ≤ C₂)
    (hI₁ : Integrable (fun t : ℝ => Wr₀ t * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)))
    (hI₂ : Integrable (fun t : ℝ => Wr₀ t * (((|t| : ℝ) : ℂ) ^ ((s - σ₀) - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)))
    (hW2b : ∀ (t : ℝ) (e : Matrix (Fin 2) (Fin 2) ℝ), t ≠ 0 → e.det ≠ 0 →
        ‖WD (ArchR.diagOne (a * t) * e⁻¹)‖ ≤
          C₂ * Real.sqrt (∑ i, (e⁻¹ 1 i) ^ 2) ^ (cc + 1) *
            ((|a * t| / (|e.det| * ∑ i, (e⁻¹ 1 i) ^ 2)) ^ (-((0:ℕ) : ℝ)) +
              (|a * t| / (|e.det| * ∑ i, (e⁻¹ 1 i) ^ 2)) ^ (-σ₀)))
    (e : Matrix (Fin 2) (Fin 2) ℝ) (he : e.det ≠ 0) :
    Integrable (fun t : ℝ => Wr₀ t * WD (ArchR.diagOne (a * t) * e⁻¹) *
        (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) ∧
      ∫ t, ‖Wr₀ t * WD (ArchR.diagOne (a * t) * e⁻¹) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) *
          (((t ^ 2)⁻¹ : ℝ) : ℂ)‖ ≤
        C₂ * Real.sqrt (∑ i, (e⁻¹ 1 i) ^ 2) ^ (cc + 1) *
          ((∫ t, ‖Wr₀ t * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)‖) +
            (|e.det| * (∑ i, (e⁻¹ 1 i) ^ 2) / |a|) ^ σ₀ *
              ∫ t, ‖Wr₀ t * (((|t| : ℝ) : ℂ) ^ ((s - σ₀) - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)‖) := by
  set B : ℝ := ∑ i, (e⁻¹ 1 i) ^ 2 with hB
  have hBpos : 0 < B := inv_row_sq_sum_pos e he
  set Me : ℝ := (|e.det| * B / |a|) ^ σ₀ with hMe
  have hMe0 : 0 ≤ Me := Real.rpow_nonneg (by positivity) _
  set w₁ : ℝ → ℂ := fun t => Wr₀ t * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) with hw₁
  set w₂ : ℝ → ℂ := fun t => Wr₀ t * (((|t| : ℝ) : ℂ) ^ ((s - σ₀) - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)
    with hw₂
  set F : ℝ → ℂ := fun t => Wr₀ t * WD (ArchR.diagOne (a * t) * e⁻¹) *
        (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) with hF

  have hkey : ∀ t : ℝ, t ≠ 0 → ‖F t‖ ≤ C₂ * Real.sqrt B ^ (cc + 1) * (‖w₁ t‖ + Me * ‖w₂ t‖) := by
    intro t ht
    have hat : 0 < |a * t| := abs_pos.mpr (mul_ne_zero ha ht)
    have hWDb := hW2b t e ht he
    rw [← hB] at hWDb
    simp only [Nat.cast_zero, neg_zero, Real.rpow_zero] at hWDb
    have hr : (|a * t| / (|e.det| * B)) ^ (-σ₀) = Me * |t| ^ (-σ₀) := by
      calc (|a * t| / (|e.det| * B)) ^ (-σ₀) = ((|a * t| / (|e.det| * B))⁻¹) ^ σ₀ := by
            rw [Real.rpow_neg (by positivity), Real.inv_rpow (by positivity)]
        _ = ((|e.det| * B / |a|) * |t|⁻¹) ^ σ₀ := by
            congr 1
            rw [inv_div, abs_mul]
            field_simp
        _ = Me * |t| ^ (-σ₀) := by
            rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (abs_nonneg t),
              Real.rpow_neg (abs_nonneg t)]
    have hn : ‖F t‖ = ‖w₁ t‖ * ‖WD (ArchR.diagOne (a * t) * e⁻¹)‖ := by
      simp only [hF, hw₁, norm_mul]; ring
    have hw12 : ‖w₁ t‖ * |t| ^ (-σ₀) = ‖w₂ t‖ := by
      simp only [hw₁, hw₂]
      rw [norm_w Wr₀ s t ht, norm_w Wr₀ (s - σ₀) t ht]
      have : ((s - (σ₀ : ℂ)).re - 1 / 2) = (s.re - 1 / 2) + (-σ₀) := by simp; ring
      rw [this, Real.rpow_add (abs_pos.mpr ht)]
      ring
    calc ‖F t‖ = ‖w₁ t‖ * ‖WD (ArchR.diagOne (a * t) * e⁻¹)‖ := hn
      _ ≤ ‖w₁ t‖ * (C₂ * Real.sqrt B ^ (cc + 1) * (1 + Me * |t| ^ (-σ₀))) := by
          rw [← hr]; exact mul_le_mul_of_nonneg_left hWDb (norm_nonneg _)
      _ = C₂ * Real.sqrt B ^ (cc + 1) * (‖w₁ t‖ + Me * (‖w₁ t‖ * |t| ^ (-σ₀))) := by ring
      _ = C₂ * Real.sqrt B ^ (cc + 1) * (‖w₁ t‖ + Me * ‖w₂ t‖) := by rw [hw12]

  have hWDt : AEStronglyMeasurable (fun t : ℝ => WD (ArchR.diagOne (a * t) * e⁻¹)) volume := by
    apply aesm_of_continuousOn_compl_zero
    have hinner : ContinuousOn (fun t : ℝ => ArchR.diagOne (a * t) * e⁻¹) {t : ℝ | t ≠ 0} :=
      ((continuous_diagOne_mul a).mul continuous_const).continuousOn
    refine hWD.comp hinner (fun t ht => ?_)
    show (Matrix.of (ArchR.diagOne (a * t) * e⁻¹)).det ≠ 0
    have : Matrix.of (ArchR.diagOne (a * t) * e⁻¹) = ArchR.diagOne (a * t) * e⁻¹ := rfl
    rw [this, det_diagOne_mul_inv _ _ he]
    exact mul_ne_zero (mul_ne_zero ha ht) (inv_ne_zero he)
  have hFm : AEStronglyMeasurable F volume :=
    (hI₁.aestronglyMeasurable.mul hWDt).congr (Filter.Eventually.of_forall fun t => by
      simp only [hF, Pi.mul_apply]; ring)

  set g : ℝ → ℝ := fun t => C₂ * Real.sqrt B ^ (cc + 1) * (‖w₁ t‖ + Me * ‖w₂ t‖) with hg
  have hgI : Integrable g := (hI₁.norm.add (hI₂.norm.const_mul Me)).const_mul _
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), ‖F t‖ ≤ g t := by
    filter_upwards [ae_ne_zero_real] with t ht
    exact hkey t ht
  have hFint : Integrable F := Integrable.mono' hgI hFm hae
  refine ⟨hFint, ?_⟩
  calc ∫ t, ‖F t‖ ≤ ∫ t, g t := integral_mono_ae hFint.norm hgI hae
    _ = C₂ * Real.sqrt B ^ (cc + 1) * ((∫ t, ‖w₁ t‖) + Me * ∫ t, ‖w₂ t‖) := by
        simp only [hg]
        rw [integral_const_mul, integral_add hI₁.norm (hI₂.norm.const_mul Me), integral_const_mul]

theorem theta_section (Gf : ℝ → Matrix (Fin 2) (Fin 2) ℝ → ℂ) (z : ℂ) (N A : ℕ) (C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hκ : -1 < z.re) (hN : z.re + 1 < 2 * N)
    (hG : ContinuousOn (fun p : ℝ × Matrix (Fin 2) (Fin 2) ℝ => Gf p.1 p.2) {p | p.2.det ≠ 0})
    (hGb : ∀ (e : Matrix (Fin 2) (Fin 2) ℝ) (y : ℝ), e.det ≠ 0 →
        ‖Gf y e‖ ≤ C₁ * |e.det|⁻¹ * Real.exp (-(Real.pi * ∑ i, ∑ j, e i j ^ 2)) *
          (1 + ∑ i, ∑ j, e i j ^ 2) ^ A * ((1 + y ^ 2 * ∑ i, (e⁻¹ 1 i) ^ 2) ^ N)⁻¹)
    (e : Matrix (Fin 2) (Fin 2) ℝ) (he : e.det ≠ 0) :
    Integrable (fun y : ℝ => ((y : ℝ) : ℂ) ^ z * Gf y e) ((volume : Measure ℝ).restrict (Ioi 0)) ∧
      ∫ y in Ioi 0, ‖((y : ℝ) : ℂ) ^ z * Gf y e‖ ≤
        C₁ * |e.det|⁻¹ * Real.exp (-(Real.pi * ∑ i, ∑ j, e i j ^ 2)) * (1 + ∑ i, ∑ j, e i j ^ 2) ^ A *
          ((Real.sqrt (∑ i, (e⁻¹ 1 i) ^ 2)) ^ (-(z.re + 1)) *
            ∫ u in Ioi 0, u ^ z.re * ((1 + u ^ 2) ^ N)⁻¹) := by
  set B : ℝ := ∑ i, (e⁻¹ 1 i) ^ 2 with hB
  have hBpos : 0 < B := inv_row_sq_sum_pos e he
  set K : ℝ := C₁ * |e.det|⁻¹ * Real.exp (-(Real.pi * ∑ i, ∑ j, e i j ^ 2)) *
    (1 + ∑ i, ∑ j, e i j ^ 2) ^ A with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨hyI, hyv⟩ := yIntegral z.re N hκ hN B hBpos
  set F : ℝ → ℂ := fun y => ((y : ℝ) : ℂ) ^ z * Gf y e with hF
  have hopen : IsOpen {p : ℝ × Matrix (Fin 2) (Fin 2) ℝ | p.2.det ≠ 0} :=
    isOpen_ne_fun (Continuous.matrix_det (A := fun p : ℝ × Matrix (Fin 2) (Fin 2) ℝ => p.2) continuous_snd)
      continuous_const
  have hFm : AEStronglyMeasurable F ((volume : Measure ℝ).restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro y hy
    have hy0 : y ≠ 0 := (mem_Ioi.mp hy).ne'
    refine ContinuousWithinAt.mul ?_ ?_
    · exact (Complex.continuousAt_ofReal_cpow_const y z (Or.inr hy0)).continuousWithinAt
    · have h1 : ContinuousAt (fun p : ℝ × Matrix (Fin 2) (Fin 2) ℝ => Gf p.1 p.2) (y, e) :=
        hG.continuousAt (hopen.mem_nhds he)
      have h2 : ContinuousAt (fun y' : ℝ => ((y', e) : ℝ × Matrix (Fin 2) (Fin 2) ℝ)) y :=
        (continuous_id.prodMk continuous_const).continuousAt
      exact (ContinuousAt.comp (f := fun y' : ℝ => ((y', e) : ℝ × Matrix (Fin 2) (Fin 2) ℝ)) h1 h2).continuousWithinAt
  have hbound : ∀ᵐ y ∂((volume : Measure ℝ).restrict (Ioi 0)),
      ‖F y‖ ≤ K * (y ^ z.re * ((1 + y ^ 2 * B) ^ N)⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hy
    have hb := hGb e y he
    rw [← hB, ← hK] at hb
    simp only [hF]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    calc y ^ z.re * ‖Gf y e‖ ≤ y ^ z.re * (K * ((1 + y ^ 2 * B) ^ N)⁻¹) :=
          mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hy0.le _)
      _ = K * (y ^ z.re * ((1 + y ^ 2 * B) ^ N)⁻¹) := by ring
  have hgI : Integrable (fun y : ℝ => K * (y ^ z.re * ((1 + y ^ 2 * B) ^ N)⁻¹))
      ((volume : Measure ℝ).restrict (Ioi 0)) := hyI.const_mul K
  have hFint : Integrable F ((volume : Measure ℝ).restrict (Ioi 0)) := Integrable.mono' hgI hFm hbound
  refine ⟨hFint, ?_⟩
  calc ∫ y in Ioi 0, ‖F y‖ ≤ ∫ y in Ioi 0, K * (y ^ z.re * ((1 + y ^ 2 * B) ^ N)⁻¹) :=
        integral_mono_ae hFint.norm hgI hbound
    _ = K * ((Real.sqrt B) ^ (-(z.re + 1)) * ∫ u in Ioi 0, u ^ z.re * ((1 + u ^ 2) ^ N)⁻¹) := by
        rw [integral_const_mul, hyv]

end W4DOM

namespace W4DOM
open MeasureTheory Set Real LanglandsTunnell LanglandsTunnell.Converse

theorem final_bound (e : Matrix (Fin 2) (Fin 2) ℝ) (he : e.det ≠ 0) (h00 : e 0 0 ≠ 0) (h10 : e 1 0 ≠ 0)
    (C₁ C₂ J I₁ I₂ a σ₀ κ' cc lam : ℝ) (n A : ℕ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hJ : 0 ≤ J) (hI₁ : 0 ≤ I₁) (hI₂ : 0 ≤ I₂) (ha : a ≠ 0)
    (hσ₀ : 0 ≤ σ₀) (hlamdef : lam = κ' - cc) (hlam : 1 + σ₀ ≤ lam) (hn : lam ≤ n) :
    1 * ((C₂ * Real.sqrt (∑ i, (e⁻¹ 1 i) ^ 2) ^ (cc + 1) *
          ((I₁) + (|e.det| * (∑ i, (e⁻¹ 1 i) ^ 2) / |a|) ^ σ₀ * I₂)) *
        (C₁ * |e.det|⁻¹ * Real.exp (-(Real.pi * ∑ i, ∑ j, e i j ^ 2)) * (1 + ∑ i, ∑ j, e i j ^ 2) ^ A *
          ((Real.sqrt (∑ i, (e⁻¹ 1 i) ^ 2)) ^ (-(κ' + 1)) * J))) ≤
      (C₁ * C₂ * J * (I₁ + (|a| ^ σ₀)⁻¹ * I₂)) *
        ((phi (-(1/2)) (n + A) (e 0 0) * phi 0 (n + A) (e 0 1)) *
          (phi (-(1/2)) (n + A) (e 1 0) * phi 0 (n + A) (e 1 1))) := by
  have hP2 : 0 < e 0 0 ^ 2 + e 1 0 ^ 2 := sum_sq_pos_of_det_ne_zero e he
  set p : ℝ := Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) with hp
  set d : ℝ := |e.det| with hd
  have hp0 : 0 < p := Real.sqrt_pos.mpr hP2
  have hd0 : 0 < d := abs_pos.mpr he
  have hρ : 0 < p / d := div_pos hp0 hd0
  have hB : ∑ i, (e⁻¹ 1 i) ^ 2 = (p / d) ^ 2 := by
    rw [inv_row_sq_sum e he, div_pow, hp, Real.sq_sqrt hP2.le, hd, sq_abs]
  have hS : ∑ i, ∑ j, e i j ^ 2 = e 0 0 ^ 2 + e 0 1 ^ 2 + e 1 0 ^ 2 + e 1 1 ^ 2 := by
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]; ring
  rw [hB, Real.sqrt_sq hρ.le, hS]
  have e1 : (p / d) ^ (cc + 1) * (p / d) ^ (-(κ' + 1)) = (p / d) ^ (-lam) := by
    rw [← Real.rpow_add hρ, hlamdef]; ring_nf
  have e2 : (d * (p / d) ^ 2 / |a|) ^ σ₀ = (|a| ^ σ₀)⁻¹ * (d * (p / d) ^ 2) ^ σ₀ := by
    rw [Real.div_rpow (by positivity) (abs_nonneg a)]; ring
  have hdet : d ≤ Real.sqrt (e 0 0 ^ 2 + e 1 0 ^ 2) * Real.sqrt (e 0 1 ^ 2 + e 1 1 ^ 2) := hadamard_fin_two e
  have key := key_bound (e 0 0) (e 0 1) (e 1 0) (e 1 1) d lam σ₀ I₁ I₂ ((|a| ^ σ₀)⁻¹) n A h00 h10 hd0 hdet
    hσ₀ hlam hn hI₁ hI₂ (by positivity)
  rw [← hp, neg_mul] at key
  set S' : ℝ := e 0 0 ^ 2 + e 0 1 ^ 2 + e 1 0 ^ 2 + e 1 1 ^ 2 with hS'
  set Φ : ℝ := (phi (-(1/2)) (n + A) (e 0 0) * phi 0 (n + A) (e 0 1)) *
          (phi (-(1/2)) (n + A) (e 1 0) * phi 0 (n + A) (e 1 1)) with hΦ
  have hCCJ : 0 ≤ C₁ * C₂ * J := by positivity
  calc 1 * ((C₂ * (p / d) ^ (cc + 1) * (I₁ + (d * (p / d) ^ 2 / |a|) ^ σ₀ * I₂)) *
        (C₁ * d⁻¹ * Real.exp (-(Real.pi * S')) * (1 + S') ^ A * ((p / d) ^ (-(κ' + 1)) * J)))
      = C₁ * C₂ * J * (((p / d) ^ (cc + 1) * (p / d) ^ (-(κ' + 1))) *
          (d⁻¹ * (I₁ + (d * (p / d) ^ 2 / |a|) ^ σ₀ * I₂)) * ((1 + S') ^ A * Real.exp (-(Real.pi * S')))) := by
        ring
    _ = C₁ * C₂ * J * (d⁻¹ * (p / d) ^ (-lam) * (I₁ + (|a| ^ σ₀)⁻¹ * (d * (p / d) ^ 2) ^ σ₀ * I₂) *
          ((1 + S') ^ A * Real.exp (-(Real.pi * S')))) := by
        rw [e1, e2]; ring
    _ ≤ C₁ * C₂ * J * ((I₁ + (|a| ^ σ₀)⁻¹ * I₂) * Φ) := mul_le_mul_of_nonneg_left key hCCJ
    _ = (C₁ * C₂ * J * (I₁ + (|a| ^ σ₀)⁻¹ * I₂)) * Φ := by ring

theorem integrable_swap3 {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (ρ : Measure γ) [SFinite μ] [SFinite ν] [SFinite ρ]
    (H : α × β × γ → ℂ)
    (hH : Integrable (fun q : γ × β × α => H (q.2.2, q.2.1, q.1)) (ρ.prod (ν.prod μ))) :
    Integrable H (μ.prod (ν.prod ρ)) := by
  let ψ₁ : α × β × γ ≃ᵐ (β × γ) × α := MeasurableEquiv.prodComm
  let ψ₂ : (β × γ) × α ≃ᵐ β × γ × α := MeasurableEquiv.prodAssoc
  let ψ₃ : β × γ × α ≃ᵐ (γ × α) × β := MeasurableEquiv.prodComm
  let ψ₄ : (γ × α) × β ≃ᵐ γ × α × β := MeasurableEquiv.prodAssoc
  let ψ₅ : γ × α × β ≃ᵐ γ × β × α := MeasurableEquiv.prodCongr (MeasurableEquiv.refl γ) MeasurableEquiv.prodComm
  let ψ : α × β × γ ≃ᵐ γ × β × α := (((ψ₁.trans ψ₂).trans ψ₃).trans ψ₄).trans ψ₅
  have hψ : MeasurePreserving ψ (μ.prod (ν.prod ρ)) (ρ.prod (ν.prod μ)) := by
    have h₁ : MeasurePreserving ψ₁ (μ.prod (ν.prod ρ)) ((ν.prod ρ).prod μ) := Measure.measurePreserving_swap
    have h₂ : MeasurePreserving ψ₂ ((ν.prod ρ).prod μ) (ν.prod (ρ.prod μ)) := measurePreserving_prodAssoc ν ρ μ
    have h₃ : MeasurePreserving ψ₃ (ν.prod (ρ.prod μ)) ((ρ.prod μ).prod ν) := Measure.measurePreserving_swap
    have h₄ : MeasurePreserving ψ₄ ((ρ.prod μ).prod ν) (ρ.prod (μ.prod ν)) := measurePreserving_prodAssoc ρ μ ν
    have h₅ : MeasurePreserving ψ₅ (ρ.prod (μ.prod ν)) (ρ.prod (ν.prod μ)) :=
      (MeasurePreserving.id ρ).prod Measure.measurePreserving_swap
    exact (((h₁.trans h₂).trans h₃).trans h₄).trans h₅
  have h := (hψ.integrable_comp_emb ψ.measurableEmbedding).mpr hH
  exact h.congr (Filter.Eventually.of_forall fun p => rfl)

end W4DOM

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (_hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : IsAdmissibleTwist ℚ ω ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p →
        IsUnramifiedCharAt ω p ∧ eulerCoeff ℚ ω p = inducedE3 ℚ (inducedCoeff K μ) p) ∧
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        ∀ v : InfinitePlace ℚ, v.IsReal →
          IsArchCompAt ℚ ω v
            ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
            ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (ha : a ≠ 0) (ha1 : a = -1) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (P : RealArchParam)
    (_hP₁ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (kw : ZMod 2 → InfinitePlace ℚ → ℤ)
    (Wr : ZMod 2 → InfinitePlace ℚ → ℂ → ℂ)
    (WA : ZMod 2 → GL (Fin 2) ℝ → ℂ)
    (hkw1 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ →
          (kw par w : ℂ) = signShift (a₁ + par) + signShift (a₂ + par))
    (hkw2 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → kw par w = (n : ℤ) + 1)
    (hWr1 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par = a₁ →
          ∀ t : ℝ, Wr par w (-t) = (-1 : ℂ) ^ a₁.val * Wr par w t)
    (hWr2 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr par w t = 0)
    (hWr3 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par = a₁ + 1 →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s
                = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ)) * (P.twist 0 a₁).archFactor s)
    (hWr4 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
        (b = par ∨ b = par + P.centralSign) →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s
                = (P.twist 0 b).archFactor s)
    (hWAN : ∀ par : ZMod 2, ∀ (x : ℝ) (h : GL (Fin 2) ℝ),
        WA par (unipotentGL2 x * h) = Complex.exp (-(2 * Real.pi * Complex.I * (a : ℂ) * x)) * WA par h)
    (hWAZ : ∀ par : ZMod 2, ∀ (z : ℝˣ) (h : GL (Fin 2) ℝ),
        WA par (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h)
          = ((((|(z : ℝ)| : ℝ) : ℂ) ^ (P.centralExponent + 1)) *
              (((z : ℝ) : ℂ) / ((|(z : ℝ)| : ℝ) : ℂ)) ^ (P.centralSign.val : ℤ)) * WA par h)
    (hWAK : ∀ par : ZMod 2, ∀ (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) (h : GL (Fin 2) ℝ),
        WA par (h * κ) = (archWeightCharℝ (kw par default) ⟨κ, hκ⟩ : ℂ) * WA par h)
    (hWAt : ∀ par : ZMod 2, ∀ t : ℝˣ, WA par (diagOne t) = Wr par default (t : ℝ))
    (hWAc : ∀ par : ZMod 2, Continuous (WA par))
    (w₀R : GL (Fin 2) ℝ) (hw₀R : (w₀R : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; 1, 0])
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal)
    (P₂ : RealArchParam)
    (hP₂ : ((∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
          w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) ∧
          P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)) ∨
        (∃ (wC : InfinitePlace K) (hC : wC.IsComplex), (∀ w : InfinitePlace K, w = wC ∨ w = w₀) ∧
          ((∃ hk : kC wC hC ≠ 0, P₂ = RealArchParam.discrete (uC wC hC) (kC wC hC).natAbs (Int.natAbs_pos.mpr hk)) ∨
           (kC wC hC = 0 ∧ P₂ = RealArchParam.principal (uC wC hC) 0 (uC wC hC) 1)))))
    (D : ArchDatumR P₂) (k₀ : ℤ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ k₀ r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : LanglandsTunnell.Converse.ArchCasimir.IsCasimirEigen D)
    (hDnz : ∃ g : GL (Fin 2) ℝ, D.W (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3) (par₀ : ZMod 2) :
    ∃ σu : ℝ, ∀ s : ℂ, σu < s.re →
      MeasureTheory.Integrable
        (fun p : ℝ × ℝ × (Fin 2 → Fin 2 → ℝ) =>
          ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of p.2.2).det *
              (((|(Matrix.of p.2.2).det| ^ 2)⁻¹ : ℝ) : ℂ) *
            (Wr par₀ default p.2.1 * D.W (ArchR.diagOne ((a : ℝ) * p.2.1) * (Matrix.of p.2.2)⁻¹) *
                (((|p.2.1| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((p.2.1 ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((p.1 : ℝ) : ℂ) ^ (P.centralExponent + P₂.centralExponent + 2 * s) *
              godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal p.1)) S (Matrix.of p.2.2) 1))
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
            (MeasureTheory.volume : MeasureTheory.Measure (Fin 2 → Fin 2 → ℝ)))) := by
  classical

  obtain ⟨hGcont, hGdecay⟩ :=
    LanglandsTunnell.CubicInduction.godementInner3_mulShift_polyGauss3_continuousOn_and_decay a ha psiInf hpsiInf S hS
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hW2 := LanglandsTunnell.Converse.ArchDatumR.norm_W_diagOne_mul_inv_le_of_iwasawa D (a : ℝ) ha'
  obtain ⟨σ₃, hW3⟩ :=
    LanglandsTunnell.RankinSelberg.exists_forall_integrable_Wr_mul_abs_cpow_mul_inv_sq P Wr WA hWr1 hWr2 hWr3 hWr4
      hWAt hWAc par₀
  obtain ⟨C₂, σ₀, hC₂, hσ₀, hW2b⟩ := hW2 0
  have hure : (uR w₀ h₀).re = 0 :=
    LanglandsTunnell.CubicInduction.re_eq_zero_of_isArchCompAt_of_isUnitaryChar K μ _hμ.2.2 w₀ (uR w₀ h₀) _
      (huR w₀ h₀)

  refine ⟨max (σ₃ + σ₀) (max ((1 + σ₀ - P.centralExponent.re) / 2)
      ((-1 - P.centralExponent.re - P₂.centralExponent.re) / 2)) + 1, fun s hs => ?_⟩
  have hmax1 := le_max_left (σ₃ + σ₀) (max ((1 + σ₀ - P.centralExponent.re) / 2)
      ((-1 - P.centralExponent.re - P₂.centralExponent.re) / 2))
  have hmax2 := (le_max_left _ _).trans (le_max_right (σ₃ + σ₀) (max ((1 + σ₀ - P.centralExponent.re) / 2)
      ((-1 - P.centralExponent.re - P₂.centralExponent.re) / 2)))
  have hmax3 := (le_max_right _ _).trans (le_max_right (σ₃ + σ₀) (max ((1 + σ₀ - P.centralExponent.re) / 2)
      ((-1 - P.centralExponent.re - P₂.centralExponent.re) / 2)))
  set z : ℂ := P.centralExponent + P₂.centralExponent + 2 * s with hz
  have hzre : z.re = P.centralExponent.re + P₂.centralExponent.re + 2 * s.re := by
    simp [hz, Complex.add_re, Complex.mul_re]
  have hκ : -1 < z.re := by rw [hzre]; linarith
  set lam : ℝ := P.centralExponent.re + 2 * s.re with hlam
  have hlam1 : 1 + σ₀ ≤ lam := by rw [hlam]; linarith
  have hlamdef : lam = z.re - P₂.centralExponent.re := by rw [hzre, hlam]; ring
  obtain ⟨N, hN⟩ : ∃ N : ℕ, z.re + 1 < 2 * N := by
    refine ⟨⌈z.re⌉₊ + 1, ?_⟩
    have := Nat.le_ceil z.re
    push_cast
    linarith
  obtain ⟨C₁, A, hC₁, hW1b⟩ := hGdecay N
  obtain ⟨n, hn⟩ : ∃ n : ℕ, lam ≤ n := ⟨⌈lam⌉₊, Nat.le_ceil _⟩
  have hσs : σ₃ < s.re := by linarith
  have hσs' : σ₃ < (s - (σ₀ : ℂ)).re := by simp; linarith
  have hI₁ := hW3 s hσs
  have hI₂ := hW3 (s - σ₀) hσs'

  have hΨ := fun (e : Matrix (Fin 2) (Fin 2) ℝ) (he : e.det ≠ 0) =>
    W4DOM.psi_section (fun t : ℝ => Wr par₀ default t) D.W D.smooth.continuousOn (a : ℝ) ha' s σ₀ C₂
      P₂.centralExponent.re hC₂ hI₁ hI₂ hW2b e he
  have hΘ := fun (e : Matrix (Fin 2) (Fin 2) ℝ) (he : e.det ≠ 0) =>
    W4DOM.theta_section (fun (y : ℝ) (e' : Matrix (Fin 2) (Fin 2) ℝ) =>
        godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S e' 1)
      z N A C₁ hC₁ hκ hN hGcont hW1b e he

  have hmeas := W4DOM.aesm_H (fun x : ℝ => ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) x)
    (W4DOM.continuousOn_quasiChar _ _) (fun t : ℝ => Wr par₀ default t) s hI₁.aestronglyMeasurable D.W
    D.smooth.continuousOn (a : ℝ) ha' z
    (fun (y : ℝ) (e' : Matrix (Fin 2) (Fin 2) ℝ) =>
      godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S e' 1) hGcont

  apply W4DOM.integrable_swap3
  rw [MeasureTheory.integrable_prod_iff hmeas]
  refine ⟨?_, ?_⟩
  ·
    filter_upwards [W4DOM.ae_det_ne_zero] with e he
    have h := ((hΨ (Matrix.of e) he).1.mul_prod (hΘ (Matrix.of e) he).1).const_mul
      (ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ))
    refine h.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only
    ring
  ·
    set I₁ : ℝ := ∫ t : ℝ, ‖Wr par₀ default t * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)‖ with hI₁d
    set I₂ : ℝ := ∫ t : ℝ, ‖Wr par₀ default t * (((|t| : ℝ) : ℂ) ^ ((s - σ₀) - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)‖
      with hI₂d
    set J : ℝ := ∫ u in Set.Ioi 0, u ^ z.re * ((1 + u ^ 2) ^ N)⁻¹ with hJd
    have hI₁0 : 0 ≤ I₁ := integral_nonneg fun _ => norm_nonneg _
    have hI₂0 : 0 ≤ I₂ := integral_nonneg fun _ => norm_nonneg _
    have hJ0 : 0 ≤ J := setIntegral_nonneg measurableSet_Ioi fun u hu =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt hu) _) (inv_nonneg.mpr (pow_nonneg (by positivity) _))
    set Kc : ℝ := C₁ * C₂ * J * (I₁ + (|(a:ℝ)| ^ σ₀)⁻¹ * I₂) with hKc
    set sgn : Fin 2 → Fin 2 → ℝ := fun _ j => if j = 0 then -(1/2) else 0 with hsgn
    have hg : Integrable (fun e : Fin 2 → Fin 2 → ℝ => Kc *
        ((W4DOM.phi (-(1/2)) (n + A) (e 0 0) * W4DOM.phi 0 (n + A) (e 0 1)) *
          (W4DOM.phi (-(1/2)) (n + A) (e 1 0) * W4DOM.phi 0 (n + A) (e 1 1))))
        (volume : Measure (Fin 2 → Fin 2 → ℝ)) := by
      have h := (W4DOM.integrable_prod_phi sgn (fun i j => by
        simp only [hsgn]; split_ifs <;> norm_num) (n + A)).const_mul Kc
      refine h.congr (Filter.Eventually.of_forall fun e => ?_)
      simp [Fin.prod_univ_two, hsgn]
    refine MeasureTheory.Integrable.mono' hg hmeas.norm.integral_prod_right' ?_
    filter_upwards [W4DOM.ae_det_ne_zero, W4DOM.ae_entry_ne_zero 0, W4DOM.ae_entry_ne_zero 1] with e he h00 h10
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    obtain ⟨hΨi, hΨb⟩ := hΨ (Matrix.of e) he
    obtain ⟨hΘi, hΘb⟩ := hΘ (Matrix.of e) he
    have hc1 : ‖ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det *
        (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ)‖ = 1 :=
      W4DOM.norm_c_eq_one (uR w₀ h₀) hure (aR w₀ h₀) _ he
    have hsplit : (∫ q : ℝ × ℝ, ‖ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det *
          (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
        (Wr par₀ default q.1 * D.W (ArchR.diagOne ((a : ℝ) * q.1) * (Matrix.of e)⁻¹) *
          (((|q.1| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.1 ^ 2)⁻¹ : ℝ) : ℂ)) *
        (((q.2 : ℝ) : ℂ) ^ z *
          godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal q.2)) S (Matrix.of e) 1)‖
        ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) =
        1 * ((∫ t : ℝ, ‖Wr par₀ default t * D.W (ArchR.diagOne ((a : ℝ) * t) * (Matrix.of e)⁻¹) *
          (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)‖) *
          ∫ y in Set.Ioi 0, ‖((y : ℝ) : ℂ) ^ z *
            godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S (Matrix.of e) 1‖) := by
      rw [← hc1, ← integral_prod_mul, ← integral_const_mul]
      congr 1
      funext q
      simp only [norm_mul]
      ring
    rw [hsplit]
    refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul hΨb hΘb (integral_nonneg fun _ => norm_nonneg _)
      (le_trans (integral_nonneg fun _ => norm_nonneg _) hΨb)) zero_le_one) ?_
    exact W4DOM.final_bound (Matrix.of e) he h00 h10 C₁ C₂ J I₁ I₂ (a : ℝ) σ₀ z.re P₂.centralExponent.re lam n A
      hC₁ hC₂ hJ0 hI₁0 hI₂0 ha' hσ₀ hlamdef hlam1 hn

end S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_unfoldedTorusPairIntegrand_jacquetVector3
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_unfoldedTorusPairIntegrand_jacquetVector3 (solution)
