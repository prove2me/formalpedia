-- Prove2me | solution 1 for OAI.Problem358.one_third_exponent_is_sharp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T05:41:07.353869+00:00
-- url     : https://prove2.me/submissions/2f970b5c-7e94-43b7-8b76-8091aa2dad54

import Mathlib
import Definitions.Def_Brenier

set_option linter.all false

namespace OAI
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Problem358
namespace BrSharp

variable {n : ℕ}

lemma vol_box (a b : Fin n → ℝ) :
    volume {x : E n | ∀ i, x i ∈ Ioo (a i) (b i)} = ∏ i, ENNReal.ofReal (b i - a i) := by
  have h := (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    (s := pi univ fun i => Ioo (a i) (b i))
    ((measurableSet_pi countable_univ).2 (Or.inl fun i _ => measurableSet_Ioo)).nullMeasurableSet
  rw [← Real.volume_pi_Ioo, ← h]
  congr 1; ext x; simp

lemma vol_boxc (a b : Fin n → ℝ) :
    volume {x : E n | ∀ i, x i ∈ Icc (a i) (b i)} = ∏ i, ENNReal.ofReal (b i - a i) := by
  have h := (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    (s := Icc a b) measurableSet_Icc.nullMeasurableSet
  rw [← Real.volume_Icc_pi, ← h]
  congr 1; ext x; simp [Pi.le_def, forall_and]

lemma cube_eq : cube n = {x : E n | ∀ i, x i ∈ Icc ((fun _ => (-1:ℝ)) i) ((fun _ => (1:ℝ)) i)} := by
  ext x; simp [cube, abs_le]

lemma vol_cube : volume (cube n) = 2 ^ n := by
  rw [cube_eq, vol_boxc]; norm_num

lemma meas_cube : MeasurableSet (cube n) := by
  rw [cube_eq]
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun i => measurableSet_Icc.preimage (by fun_prop)

lemma unif_apply (S : Set (E n)) :
    uniformMeasure (cube n) S = (2 ^ n)⁻¹ * volume (S ∩ cube n) := by
  rw [uniformMeasure, vol_cube, Measure.smul_apply, Measure.restrict_apply' meas_cube, smul_eq_mul]

instance : IsProbabilityMeasure (uniformMeasure (cube n)) := by
  constructor; rw [unif_apply, univ_inter, vol_cube]
  exact ENNReal.inv_mul_cancel (by simp) (by simp)

def ell (c : E n → ℝ) (y x : E n) : ℝ := inner ℝ x y - c y

lemma intg_bdd {α : Type*} [MeasurableSpace α] (π : Measure α) [IsFiniteMeasure π] (f : α → ℝ)
    (hf : Measurable f) (C : ℝ) (h : ∀ᵐ p ∂π, |f p| ≤ C) : Integrable f π :=
  Integrable.of_bound hf.aestronglyMeasurable C (by simpa [Real.norm_eq_abs] using h)

theorem generic (ρ : Measure (E n)) [IsProbabilityMeasure ρ] (K : Set (E n)) (R : ℝ)
    (T : E n → E n) (A : Finset (E n)) (c : E n → ℝ) (N : Set (E n))
    (hK : ρ Kᶜ = 0) (hR : ∀ x ∈ K, ‖x‖ ≤ R) (hAR : ∀ y ∈ A, ‖y‖ ≤ R)
    (hT : Measurable T) (hc : Measurable c)
    (hTA : ∀ x, T x ∈ A) (hmax : ∀ x, ∀ y ∈ A, ell c y x ≤ ell c (T x) x)
    (hN : ρ N = 0) (huniq : ∀ x ∉ N, ∀ y ∈ A, ell c y x = ell c (T x) x → y = T x) :
    IsUniqueQuadraticOptimalMap ρ (ρ.map T) T := by
  set Cc : ℝ := ∑ a ∈ A, |c a|
  have hCc : ∀ y ∈ A, |c y| ≤ Cc := fun y hy =>
    Finset.single_le_sum (f := fun a => |c a|) (fun _ _ => abs_nonneg _) hy
  have hR0 : ∀ x, 0 ≤ R := fun x => (norm_nonneg _).trans (hAR _ (hTA x))
  have hR0' : 0 ≤ R := hR0 0
  set g : E n → ℝ := fun x => ‖x - T x‖ ^ 2
  set h : E n → ℝ := fun y => ‖y‖ ^ 2 - 2 * c y
  set D : E n × E n → ℝ := fun p => ell c (T p.1) p.1 - ell c p.2 p.1
  have hgm : Measurable g := by fun_prop
  have hhm : Measurable h := by fun_prop
  have hDm : Measurable D := by
    simp only [D, ell]
    have : Measurable fun p : E n × E n => T p.1 := hT.comp measurable_fst
    fun_prop
  have hρK : ∀ᵐ x ∂ρ, x ∈ K ∧ x ∉ N := by
    have h1 : ∀ᵐ x ∂ρ, x ∈ K := by
      rw [ae_iff]; exact hK
    have h2 : ∀ᵐ x ∂ρ, x ∉ N := by
      rw [ae_iff]; simpa using hN
    filter_upwards [h1, h2] with x a b using ⟨a, b⟩
  have hgi : Integrable g ρ := by
    refine intg_bdd ρ g hgm ((2 * R) ^ 2) ?_
    filter_upwards [hρK] with x hx
    have h1 := hR x hx.1; have h2 := hAR _ (hTA x)
    have : ‖x - T x‖ ≤ 2 * R := (norm_sub_le _ _).trans (by linarith)
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hcostG : quadraticPlanCost (graphPlan ρ T) = ENNReal.ofReal (∫ x, g x ∂ρ) := by
    rw [quadraticPlanCost, graphPlan, lintegral_map (by fun_prop) (by fun_prop)]
    rw [ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall fun x => by positivity)]
  -- main analysis of a coupling
  have key : ∀ π : Measure (E n × E n), IsCoupling ρ (ρ.map T) π →
      (∀ᵐ p ∂π, p.1 ∈ K ∧ p.1 ∉ N ∧ p.2 ∈ A) ∧ Integrable D π ∧ 0 ≤ ∫ p, D p ∂π ∧
      quadraticPlanCost π = ENNReal.ofReal (∫ x, g x ∂ρ + 2 * ∫ p, D p ∂π) := by
    intro π ⟨hπ1, hπ2, hπ3⟩
    have hae1 : ∀ᵐ p ∂π, p.1 ∈ K ∧ p.1 ∉ N := by
      have := hπ2 ▸ hρK
      exact ae_of_ae_map measurable_fst.aemeasurable this
    have hae2 : ∀ᵐ p ∂π, p.2 ∈ A := by
      have : ∀ᵐ y ∂(ρ.map T), y ∈ A := by
        have hm : MeasurableSet ((A : Set (E n))ᶜ) := A.finite_toSet.measurableSet.compl
        rw [ae_iff]; change (ρ.map T) ((A : Set (E n))ᶜ) = 0
        rw [Measure.map_apply hT hm]; convert measure_empty (μ := ρ); ext x; simp [hTA]
      rw [← hπ3] at this
      exact ae_of_ae_map measurable_snd.aemeasurable this
    have hae : ∀ᵐ p ∂π, p.1 ∈ K ∧ p.1 ∉ N ∧ p.2 ∈ A := by
      filter_upwards [hae1, hae2] with p a b using ⟨a.1, a.2, b⟩
    have hDi : Integrable D π := by
      refine intg_bdd π D hDm (2 * (R * R + Cc)) ?_
      filter_upwards [hae] with p hp
      have hx := hR _ hp.1
      have hy := hAR _ hp.2.2
      have hTx := hAR _ (hTA p.1)
      have b1 : |inner ℝ p.1 (T p.1)| ≤ R * R :=
        (abs_real_inner_le_norm _ _).trans (mul_le_mul hx hTx (norm_nonneg _) hR0')
      have b2 : |inner ℝ p.1 p.2| ≤ R * R :=
        (abs_real_inner_le_norm _ _).trans (mul_le_mul hx hy (norm_nonneg _) hR0')
      have b3 := hCc _ hp.2.2
      have b4 := hCc _ (hTA p.1)
      simp only [D, ell]
      rw [abs_le] at *
      constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2]
    have hD0 : 0 ≤ ∫ p, D p ∂π := by
      apply integral_nonneg_of_ae
      filter_upwards [hae] with p hp
      simp only [D, Pi.zero_apply, sub_nonneg]
      exact hmax _ _ hp.2.2
    have hgfi : Integrable (fun p : E n × E n => g p.1) π := by
      rw [← hπ2] at hgi
      exact hgi.comp_measurable measurable_fst
    have hhi : Integrable h (ρ.map T) := by
      refine intg_bdd _ h hhm (R ^ 2 + 2 * Cc) ?_
      rw [ae_map_iff hT.aemeasurable (measurableSet_le (by fun_prop) (by fun_prop))]
      refine Filter.Eventually.of_forall fun x => ?_
      have := hAR _ (hTA x); have := hCc _ (hTA x)
      have : ‖T x‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (by assumption) 2
      have : 0 ≤ ‖T x‖ ^ 2 := by positivity
      simp only [h]; rw [abs_le] at *; constructor <;> linarith
    have hhsi : Integrable (fun p : E n × E n => h p.2) π := by
      rw [← hπ3] at hhi; exact hhi.comp_measurable measurable_snd
    have hhTi : Integrable (fun x => h (T x)) ρ := hhi.comp_measurable hT
    have hhTfi : Integrable (fun p : E n × E n => h (T p.1)) π := by
      rw [← hπ2] at hhTi; exact hhTi.comp_measurable measurable_fst
    have hid : ∀ p : E n × E n, ‖p.1 - p.2‖ ^ 2 = g p.1 + 2 * D p + h p.2 - h (T p.1) := by
      intro p
      simp only [g, h, D, ell]
      rw [@norm_sub_sq_real, @norm_sub_sq_real]
      ring
    have hFi : Integrable (fun p : E n × E n => ‖p.1 - p.2‖ ^ 2) π := by
      simp_rw [hid]
      exact ((hgfi.add (hDi.const_mul 2)).add hhsi).sub hhTfi
    refine ⟨hae, hDi, hD0, ?_⟩
    rw [quadraticPlanCost, ← ofReal_integral_eq_lintegral_ofReal hFi
      (Filter.Eventually.of_forall fun p => by positivity)]
    congr 1
    simp_rw [hid]
    have i2 : Integrable (fun p : E n × E n => g p.1 + 2 * D p) π := hgfi.add (hDi.const_mul 2)
    have i1 : Integrable (fun p : E n × E n => g p.1 + 2 * D p + h p.2) π := i2.add hhsi
    rw [integral_sub i1 hhTfi, integral_add i2 hhsi, integral_add hgfi (hDi.const_mul 2),
      integral_const_mul]
    have e1 : ∫ p, g p.1 ∂π = ∫ x, g x ∂ρ := by
      rw [← hπ2, integral_map measurable_fst.aemeasurable hgm.aestronglyMeasurable]
    have e2 : ∫ p, h p.2 ∂π = ∫ x, h (T x) ∂ρ := by
      rw [← integral_map hT.aemeasurable hhm.aestronglyMeasurable, ← hπ3,
        integral_map measurable_snd.aemeasurable hhm.aestronglyMeasurable]
    have e3 : ∫ p, h (T p.1) ∂π = ∫ x, h (T x) ∂ρ := by
      rw [← hπ2]
      exact (integral_map measurable_fst.aemeasurable (hhm.comp hT).aestronglyMeasurable).symm
    rw [e1, e2, e3]; ring
  refine ⟨⟨hT, rfl, fun π hπ => ?_⟩, fun π hπ hle => ?_⟩
  · obtain ⟨-, -, hD0, hc⟩ := key π hπ
    rw [hc, hcostG]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · obtain ⟨hae, hDi, hD0, hcost⟩ := key π hπ
    rw [hcost, hcostG, ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun x => by positivity)] at hle
    have hD : ∫ p, D p ∂π = 0 := by linarith
    have hDae : D =ᵐ[π] 0 := by
      rw [integral_eq_zero_iff_of_nonneg_ae _ hDi] at hD
      · exact hD
      · filter_upwards [hae] with p hp
        simp only [D, Pi.zero_apply, sub_nonneg]
        exact hmax _ _ hp.2.2
    have hgr : ∀ᵐ p ∂π, p = (p.1, T p.1) := by
      filter_upwards [hae, hDae] with p hp hp0
      simp only [D, Pi.zero_apply, sub_eq_zero] at hp0
      have := huniq p.1 hp.2.1 p.2 hp.2.2 hp0.symm
      ext <;> simp [this]
    rw [graphPlan, ← hπ.2.1, Measure.map_map (by fun_prop) measurable_fst]
    conv_lhs => rw [← Measure.map_id (μ := π)]
    exact Measure.map_congr hgr

lemma hyper_null (L : E n →L[ℝ] ℝ) (v : E n) (hv : L v ≠ 0) (a : ℝ) :
    volume {x : E n | L x = a} = 0 := by
  set p : E n := (a / L v) • v
  have hp : L p = a := by simp [p, map_smul, div_mul_cancel₀ _ hv]
  set S : AffineSubspace ℝ (E n) := AffineSubspace.mk' p (LinearMap.ker (L : E n →ₗ[ℝ] ℝ))
  have hS : (S : Set (E n)) = {x : E n | L x = a} := by
    ext x
    simp only [SetLike.mem_coe, S, AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe, map_sub, hp, mem_setOf_eq, sub_eq_zero]
  have hne : S ≠ ⊤ := by
    intro h
    have : p + v ∈ S := by rw [h]; exact AffineSubspace.mem_top _ _ _
    simp only [S, AffineSubspace.mem_mk', vsub_eq_sub, add_sub_cancel_left, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe] at this
    exact hv this
  rw [← hS]
  exact Measure.addHaar_affineSubspace volume S hne

lemma unif_null {S : Set (E n)} (h : volume S = 0) : uniformMeasure (cube n) S = 0 := by
  rw [unif_apply, measure_mono_null inter_subset_left h, mul_zero]

def ee (i : Fin n) : E n := EuclideanSpace.single i (1:ℝ)

@[simp] lemma ee_apply (i j : Fin n) : ee i j = if j = i then 1 else 0 := by
  simp [ee, EuclideanSpace.single_apply]

def Tm (i0 i1 : Fin n) (b s : ℝ) (x : E n) : E n :=
  if |x i0| < b * x i1 + s then b • ee i1 else if x i0 < 0 then -ee i0 else ee i0

open Classical in
def At (i0 i1 : Fin n) (b : ℝ) : Finset (E n) := {b • ee i1, -ee i0, ee i0}

open Classical in
def cc (i0 i1 : Fin n) (b s : ℝ) (y : E n) : ℝ := if y = b • ee i1 then -s else 0

def NN (i0 i1 : Fin n) (b s : ℝ) : Set (E n) :=
  {x | x i0 = 0} ∪ {x | x i0 - b * x i1 = s} ∪ {x | -x i0 - b * x i1 = s}

section
variable {i0 i1 : Fin n} (h01 : i0 ≠ i1) {b s : ℝ}
include h01

lemma ne1 : b • ee i1 ≠ -ee (n := n) i0 := by
  intro h; have := congrArg (fun x : E n => x i0) h; simp [h01] at this
lemma ne2 : b • ee i1 ≠ ee (n := n) i0 := by
  intro h; have := congrArg (fun x : E n => x i0) h; simp [h01] at this
lemma ne3 : -ee (n := n) i0 ≠ ee i0 := by
  intro h; have := congrArg (fun x : E n => x i0) h; simp at this; linarith

lemma ell_a (x : E n) : ell (cc i0 i1 b s) (b • ee i1) x = b * x i1 + s := by
  simp [ell, cc, ee, EuclideanSpace.inner_single_right, inner_smul_right]
lemma ell_b (x : E n) : ell (cc i0 i1 b s) (-ee i0) x = - x i0 := by
  rw [ell, cc, if_neg (ne1 h01).symm]; simp [ee, EuclideanSpace.inner_single_right]
lemma ell_c (x : E n) : ell (cc i0 i1 b s) (ee i0) x = x i0 := by
  rw [ell, cc, if_neg (ne2 h01).symm]; simp [ee, EuclideanSpace.inner_single_right]

lemma Tm_mem (x : E n) : Tm i0 i1 b s x ∈ At i0 i1 b := by
  unfold Tm At; split_ifs <;> simp

lemma Tm_meas : Measurable (Tm i0 i1 b s) := by
  unfold Tm
  refine Measurable.ite ?_ measurable_const (Measurable.ite ?_ measurable_const measurable_const)
  · exact measurableSet_lt (by fun_prop) (by fun_prop)
  · exact measurableSet_lt (by fun_prop) measurable_const

lemma Tm_max (x : E n) : ∀ y ∈ At i0 i1 b, ell (cc i0 i1 b s) y x ≤ ell (cc i0 i1 b s) (Tm i0 i1 b s x) x := by
  intro y hy
  simp only [At, Finset.mem_insert, Finset.mem_singleton] at hy
  unfold Tm
  rcases hy with rfl | rfl | rfl <;> split_ifs with H1 H2 <;>
    simp only [ell_a h01, ell_b h01, ell_c h01] <;>
    cases abs_cases (x i0) <;> linarith

lemma Tm_uniq : ∀ x ∉ NN i0 i1 b s, ∀ y ∈ At i0 i1 b,
    ell (cc i0 i1 b s) y x = ell (cc i0 i1 b s) (Tm i0 i1 b s x) x → y = Tm i0 i1 b s x := by
  intro x hx y hy he
  simp only [NN, mem_union, mem_setOf_eq, not_or] at hx
  obtain ⟨⟨h1, h2⟩, h3⟩ := hx
  simp only [At, Finset.mem_insert, Finset.mem_singleton] at hy
  unfold Tm at he ⊢
  rcases hy with rfl | rfl | rfl <;> split_ifs at he ⊢ with H1 H2 <;>
    simp only [ell_a h01, ell_b h01, ell_c h01] at he <;>
    first | rfl | (exfalso; apply h1; linarith) | (exfalso; apply h2; linarith) |
      (exfalso; apply h3; linarith)

lemma NN_null : uniformMeasure (cube n) (NN i0 i1 b s) = 0 := by
  apply unif_null
  have hv : ∀ (L : E n →L[ℝ] ℝ), L (ee i0) ≠ 0 → ∀ a, volume {x : E n | L x = a} = 0 :=
    fun L hL a => hyper_null L _ hL a
  refine measure_union_null (measure_union_null ?_ ?_) ?_
  · have := hv (EuclideanSpace.proj i0) (by simp) 0
    simpa using this
  · have := hv (EuclideanSpace.proj i0 - b • EuclideanSpace.proj i1) (by simp [h01.symm]) s
    simpa using this
  · have := hv (-EuclideanSpace.proj i0 - b • EuclideanSpace.proj i1) (by simp [h01.symm]) s
    simpa using this
end

lemma norm_le_of_cube {x : E n} (hx : x ∈ cube n) : ‖x‖ ≤ n + 1 := by
  have h1 : ‖x‖ ^ 2 ≤ (n + 1 : ℝ) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ i, x i ^ 2 ≤ ∑ _i : Fin n, (1:ℝ) := by
          apply Finset.sum_le_sum; intro i _
          have := hx i; rw [abs_le] at this; nlinarith
      _ = n := by simp
      _ ≤ (n + 1) ^ 2 := by nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1

theorem opt {i0 i1 : Fin n} (h01 : i0 ≠ i1) {b : ℝ} (s : ℝ) (hb : |b| ≤ 1) :
    IsUniqueQuadraticOptimalMap (uniformMeasure (cube n))
      ((uniformMeasure (cube n)).map (Tm i0 i1 b s)) (Tm i0 i1 b s) := by
  refine generic _ (cube n) (n + 1) _ (At i0 i1 b) (cc i0 i1 b s) (NN i0 i1 b s) ?_
    (fun x hx => norm_le_of_cube hx) ?_ (Tm_meas h01) ?_ (Tm_mem h01) (Tm_max h01) (NN_null h01)
    (Tm_uniq h01)
  · rw [unif_apply, compl_inter_self, measure_empty, mul_zero]
  · intro y hy
    have h1 : (1:ℝ) ≤ n + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    simp only [At, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · rw [norm_smul, ee, EuclideanSpace.norm_single]; simp; linarith
    · rw [norm_neg, ee, EuclideanSpace.norm_single]; simpa using h1
    · rw [ee, EuclideanSpace.norm_single]; simpa using h1
  · unfold cc
    exact Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const
      measurable_const

lemma prod2 {i0 i1 : Fin n} (h01 : i0 ≠ i1) (α β : ℝ) :
    ∏ i, (if i = i0 then α else if i = i1 then β else 2) = α * β * 2 ^ (n - 2) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i0), if_pos rfl,
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨h01.symm, Finset.mem_univ i1⟩),
    if_neg h01.symm, if_pos rfl]
  rw [Finset.prod_congr rfl (g := fun _ => (2:ℝ)), Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨h01.symm, Finset.mem_univ i1⟩),
    Finset.card_erase_of_mem (Finset.mem_univ i0), Finset.card_univ, Fintype.card_fin]
  · rw [Nat.sub_sub]; ring
  · intro i hi
    simp only [Finset.mem_erase] at hi
    rw [if_neg hi.2.1, if_neg hi.1]

lemma prod1 (i0 : Fin n) (α : ℝ) :
    ∏ i, (if i = i0 then α else 2) = α * 2 ^ (n - 1) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i0), if_pos rfl]
  rw [Finset.prod_congr rfl (g := fun _ => (2:ℝ)), Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_univ i0), Finset.card_univ, Fintype.card_fin]
  intro i hi
  simp only [Finset.mem_erase] at hi
  rw [if_neg hi.1]

lemma unif_box (a b : Fin n → ℝ) (h : ∀ i, -1 ≤ a i ∧ a i ≤ b i ∧ b i ≤ 1) :
    uniformMeasure (cube n) {x : E n | ∀ i, x i ∈ Ioo (a i) (b i)} =
      ENNReal.ofReal ((2 ^ n)⁻¹ * ∏ i, (b i - a i)) := by
  rw [unif_apply]
  have hsub : {x : E n | ∀ i, x i ∈ Ioo (a i) (b i)} ∩ cube n = {x : E n | ∀ i, x i ∈ Ioo (a i) (b i)} := by
    apply inter_eq_left.2
    intro x hx i
    have := hx i; have := h i
    simp only [mem_Ioo] at *
    rw [abs_le]; constructor <;> linarith
  rw [hsub, vol_box, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => by linarith [h i])]
  congr 1
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
  simp

lemma unif_le_boxc (S : Set (E n)) (a b : Fin n → ℝ) (h : ∀ i, a i ≤ b i)
    (hS : S ∩ cube n ⊆ {x : E n | ∀ i, x i ∈ Icc (a i) (b i)}) :
    uniformMeasure (cube n) S ≤ ENNReal.ofReal ((2 ^ n)⁻¹ * ∏ i, (b i - a i)) := by
  rw [unif_apply]
  refine (mul_le_mul_right (measure_mono hS) _).trans ?_
  rw [vol_boxc, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => by linarith [h i])]
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
  simp

lemma meas_box (a b : Fin n → ℝ) : MeasurableSet {x : E n | ∀ i, x i ∈ Ioo (a i) (b i)} := by
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun i => measurableSet_Ioo.preimage (by fun_prop)

lemma unif_box_pos (a b : Fin n → ℝ) (h : ∀ i, -1 ≤ a i ∧ a i < b i ∧ b i ≤ 1) :
    0 < uniformMeasure (cube n) {x : E n | ∀ i, x i ∈ Ioo (a i) (b i)} := by
  rw [unif_box a b (fun i => ⟨(h i).1, (h i).2.1.le, (h i).2.2⟩), ENNReal.ofReal_pos]
  have : 0 < ∏ i, (b i - a i) := Finset.prod_pos fun i _ => by linarith [h i]
  positivity

section
variable {i0 i1 : Fin n} (h01 : i0 ≠ i1) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1 / 4)
include h01 hs0 hs1

lemma w1_pos {b : ℝ} (hb : |b| ≤ s) :
    0 < uniformMeasure (cube n) (Tm i0 i1 b s ⁻¹' {b • ee i1}) := by
  set a : Fin n → ℝ := fun i => if i = i0 then -(s/2) else if i = i1 then -(1/2) else -1
  set c : Fin n → ℝ := fun i => if i = i0 then s/2 else if i = i1 then 1/2 else 1
  refine (unif_box_pos a c ?_).trans_le (measure_mono ?_)
  · intro i; simp only [a, c]; split_ifs <;> refine ⟨?_, ?_, ?_⟩ <;> linarith
  · intro x hx
    have h0 := hx i0; have h1 := hx i1
    simp only [a, c, mem_Ioo, if_pos rfl, if_neg h01.symm, ite_true, if_true] at h0 h1
    simp only [mem_preimage, mem_singleton_iff, Tm]
    rw [if_pos]
    have : |b * x i1| ≤ s * (1/2) := by
      rw [abs_mul]; exact mul_le_mul hb (by rw [abs_le]; constructor <;> linarith) (abs_nonneg _) hs0.le
    rw [abs_lt]; rw [abs_le] at this; constructor <;> linarith

lemma w2_pos {b : ℝ} (hb : |b| ≤ s) :
    0 < uniformMeasure (cube n) (Tm i0 i1 b s ⁻¹' {-ee i0}) := by
  set a : Fin n → ℝ := fun i => if i = i0 then -1 else -1
  set c : Fin n → ℝ := fun i => if i = i0 then -(2 * s) else 1
  refine (unif_box_pos a c ?_).trans_le (measure_mono ?_)
  · intro i; simp only [a, c]; split_ifs <;> refine ⟨?_, ?_, ?_⟩ <;> linarith
  · intro x hx
    have h0 := hx i0; have h1 := hx i1
    simp only [a, c, mem_Ioo, if_pos rfl, if_neg h01.symm, ite_true, if_true] at h0 h1
    simp only [mem_preimage, mem_singleton_iff, Tm]
    have : |b * x i1| ≤ s := by
      have hx1 : |x i1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have := mul_le_mul hb hx1 (abs_nonneg _) hs0.le
      rw [abs_mul]; linarith
    rw [if_neg, if_pos (by linarith)]
    rw [abs_of_neg (by linarith)]; rw [abs_le] at this; intro h; linarith

lemma w3_pos {b : ℝ} (hb : |b| ≤ s) :
    0 < uniformMeasure (cube n) (Tm i0 i1 b s ⁻¹' {ee i0}) := by
  set a : Fin n → ℝ := fun i => if i = i0 then 2 * s else -1
  set c : Fin n → ℝ := fun i => if i = i0 then 1 else 1
  refine (unif_box_pos a c ?_).trans_le (measure_mono ?_)
  · intro i; simp only [a, c]; split_ifs <;> refine ⟨?_, ?_, ?_⟩ <;> linarith
  · intro x hx
    have h0 := hx i0; have h1 := hx i1
    simp only [a, c, mem_Ioo, if_pos rfl, if_neg h01.symm, ite_true, if_true] at h0 h1
    simp only [mem_preimage, mem_singleton_iff, Tm]
    have : |b * x i1| ≤ s := by
      have hx1 : |x i1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have := mul_le_mul hb hx1 (abs_nonneg _) hs0.le
      rw [abs_mul]; linarith
    rw [if_neg, if_neg (by linarith)]
    rw [abs_of_pos (by linarith)]; rw [abs_le] at this; intro h; linarith
end

lemma map_three (ρ : Measure (E n)) (T : E n → E n) (hT : Measurable T) (y : Fin 3 → E n)
    (hy : Function.Injective y) (hval : ∀ x, ∃ i, T x = y i) :
    ρ.map T = ∑ i, ρ (T ⁻¹' {y i}) • Measure.dirac (y i) := by
  ext S hS
  rw [Measure.map_apply hT hS, Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hS, smul_eq_mul]
  have hU : T ⁻¹' S = ⋃ i, (T ⁻¹' S ∩ T ⁻¹' {y i}) := by
    ext x; simp only [mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · intro hx; obtain ⟨i, hi⟩ := hval x; exact ⟨i, hx, hi⟩
    · rintro ⟨i, hx, -⟩; exact hx
  rw [hU, measure_iUnion, tsum_fintype]
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : y i ∈ S
    · rw [indicator_of_mem h, Pi.one_apply, mul_one]
      congr 1; apply inter_eq_right.2; intro x hx
      simp only [mem_preimage, mem_singleton_iff] at hx ⊢; rw [hx]; exact h
    · rw [indicator_of_notMem h, mul_zero]
      convert measure_empty (μ := ρ)
      ext x; simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false,
        iff_false, not_and]
      intro h1 h2; rw [h2] at h1; exact h h1
  · intro i j hij
    refine Disjoint.mono inter_subset_right inter_subset_right ?_
    rw [Set.disjoint_left]
    intro x hi hj
    simp only [mem_preimage, mem_singleton_iff] at hi hj
    exact hij (hy (hi.symm.trans hj))
  · intro i; exact (hT hS).inter (hT (measurableSet_singleton _))

lemma three_atoms {i0 i1 : Fin n} (h01 : i0 ≠ i1) {b s : ℝ} (hb : |b| ≤ 1)
    (hw : ∀ y ∈ At i0 i1 b, 0 < uniformMeasure (cube n) (Tm i0 i1 b s ⁻¹' {y})) :
    HasExactlyThreeAtoms ((uniformMeasure (cube n)).map (Tm i0 i1 b s)) (cube n) := by
  set y : Fin 3 → E n := ![b • ee i1, -ee i0, ee i0]
  have hy : Function.Injective y := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [y] at hij ⊢
    all_goals first
      | exact absurd hij (ne1 h01) | exact absurd hij.symm (ne1 h01)
      | exact absurd hij (ne2 h01) | exact absurd hij.symm (ne2 h01)
      | exact absurd hij (ne3 h01) | exact absurd hij.symm (ne3 h01)
  have hyA : ∀ i, y i ∈ At i0 i1 b := by
    intro i; fin_cases i <;> simp [y, At]
  have hval : ∀ x, ∃ i, Tm i0 i1 b s x = y i := by
    intro x
    have := Tm_mem h01 (b := b) (s := s) x
    simp only [At, Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  have hdec := map_three (uniformMeasure (cube n)) _ (Tm_meas h01) y hy hval
  refine ⟨y, hy, ?_, fun i => uniformMeasure (cube n) (Tm i0 i1 b s ⁻¹' {y i}),
    fun i => hw _ (hyA i), ?_, hdec⟩
  · intro i
    fin_cases i <;> intro j <;> by_cases hj0 : j = i0 <;> by_cases hj1 : j = i1 <;>
      simp [y, ee_apply, hj0, hj1, abs_mul, hb, h01, h01.symm]
  · have := congrArg (fun m : Measure (E n) => m univ) hdec
    simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one] at this
    rw [← this, Measure.map_apply (Tm_meas h01) MeasurableSet.univ, preimage_univ, measure_univ]

lemma two_le {i0 i1 : Fin n} (h01 : i0 ≠ i1) : 2 ≤ n := by
  have := i0.isLt; have := i1.isLt; have : i0.val ≠ i1.val := fun h => h01 (Fin.ext h); omega

lemma Tm_norm {i0 i1 : Fin n} (h01 : i0 ≠ i1) {b s : ℝ} (hb : |b| ≤ 1) (x : E n) :
    ‖Tm i0 i1 b s x‖ ≤ 1 := by
  unfold Tm; split_ifs
  · rw [norm_smul, ee, EuclideanSpace.norm_single]; simpa using hb
  · rw [norm_neg, ee, EuclideanSpace.norm_single]; simp
  · rw [ee, EuclideanSpace.norm_single]; simp

lemma Tm_diff_intg {i0 i1 : Fin n} (h01 : i0 ≠ i1) {b b' s s' : ℝ} (hb : |b| ≤ 1) (hb' : |b'| ≤ 1)
    (ρ : Measure (E n)) [IsFiniteMeasure ρ] :
    Integrable (fun x => ‖Tm i0 i1 b s x - Tm i0 i1 b' s' x‖ ^ 2) ρ := by
  refine intg_bdd ρ _ (by have := Tm_meas h01 (b := b) (s := s); have := Tm_meas h01 (b := b') (s := s'); fun_prop) 4
    (Filter.Eventually.of_forall fun x => ?_)
  have h1 := Tm_norm h01 (s := s) hb x; have h2 := Tm_norm h01 (s := s') hb' x
  have : ‖Tm i0 i1 b s x - Tm i0 i1 b' s' x‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  rw [abs_of_nonneg (by positivity)]; nlinarith [norm_nonneg (Tm i0 i1 b s x - Tm i0 i1 b' s' x)]

section
variable {i0 i1 : Fin n} (h01 : i0 ≠ i1) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1 / 4)
include h01 hs0 hs1

lemma l2_lower : s / 16 ≤ ∫ x, ‖Tm i0 i1 s s x - Tm i0 i1 (-s) s x‖ ^ 2 ∂(uniformMeasure (cube n)) := by
  set a : Fin n → ℝ := fun i => if i = i0 then s/2 else if i = i1 then 1/2 else -1
  set c : Fin n → ℝ := fun i => if i = i0 then s else if i = i1 then 1 else 1
  set A := {x : E n | ∀ i, x i ∈ Ioo (a i) (c i)}
  have hAm : MeasurableSet A := meas_box a c
  have hval : uniformMeasure (cube n) A = ENNReal.ofReal (s / 16) := by
    rw [unif_box a c (by intro i; simp only [a, c]; split_ifs <;> refine ⟨?_, ?_, ?_⟩ <;> linarith)]
    congr 1
    have : (fun i => c i - a i) = fun i => if i = i0 then s/2 else if i = i1 then 1/2 else 2 := by
      funext i; simp only [a, c]; split_ifs <;> ring
    rw [this, prod2 h01]
    obtain ⟨k, hk⟩ : ∃ k, n = k + 2 := ⟨n - 2, by have := two_le h01; omega⟩
    rw [hk, Nat.add_sub_cancel, pow_add]; field_simp; ring
  have hb1 : |s| ≤ 1 := by rw [abs_of_pos hs0]; linarith
  have hb2 : |-s| ≤ 1 := by rw [abs_neg, abs_of_pos hs0]; linarith
  have key : ∀ x, A.indicator 1 x ≤ ‖Tm i0 i1 s s x - Tm i0 i1 (-s) s x‖ ^ 2 := by
    intro x
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx, Pi.one_apply]
      have h0 := hx i0; have h1 := hx i1
      simp only [a, c, mem_Ioo, if_pos rfl, if_neg h01.symm, ite_true, if_true] at h0 h1
      have e1 : Tm i0 i1 s s x = s • ee i1 := by
        unfold Tm; rw [if_pos]; rw [abs_of_pos (by linarith)]; nlinarith
      have e2 : Tm i0 i1 (-s) s x = ee i0 := by
        unfold Tm; rw [if_neg, if_neg (by linarith)]
        rw [abs_of_pos (by linarith)]; nlinarith
      rw [e1, e2]
      have := PiLp.norm_apply_le (s • ee i1 - ee (n := n) i0) i0
      simp [h01] at this
      nlinarith
    · rw [indicator_of_notMem hx]; positivity
  have := integral_mono ((integrable_const (1:ℝ)).indicator hAm) (Tm_diff_intg h01 hb1 hb2 (uniformMeasure (cube n))) key
  rw [integral_indicator_const (1:ℝ) hAm, measureReal_def, hval, ENNReal.toReal_ofReal (by positivity), smul_eq_mul, mul_one] at this
  exact this

lemma mu_ne : (uniformMeasure (cube n)).map (Tm i0 i1 s s) ≠ (uniformMeasure (cube n)).map (Tm i0 i1 (-s) s) := by
  intro h
  have := congrArg (fun m : Measure (E n) => m {s • ee i1}) h
  simp only [Measure.map_apply (Tm_meas h01) (measurableSet_singleton _)] at this
  have hpos := w1_pos h01 hs0 hs1 (b := s) (by rw [abs_of_pos hs0])
  have hz : Tm i0 i1 (-s) s ⁻¹' {s • ee i1} = ∅ := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
    intro hx
    have := Tm_mem h01 (b := -s) (s := s) x
    rw [hx] at this
    simp only [At, Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h
    · have := congrArg (fun x : E n => x i1) h; simp at this; linarith
    · exact ne1 h01 h
    · exact ne2 h01 h
  rw [this, hz, measure_empty] at hpos
  exact lt_irrefl _ hpos
end

def Rf (i1 : Fin n) : E n ≃ₗᵢ[ℝ] E n :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun i : Fin n => if i = i1 then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

lemma Rf_apply (i1 : Fin n) (x : E n) (j : Fin n) : Rf i1 x j = if j = i1 then -x j else x j := by
  simp only [Rf, LinearIsometryEquiv.piLpCongrRight_apply, PiLp.toLp_apply]
  split_ifs <;> simp

lemma Rf_cube (i1 : Fin n) : Rf i1 ⁻¹' cube n = cube n := by
  ext x; simp only [cube, mem_preimage, mem_setOf_eq, Rf_apply]
  refine forall_congr' fun j => ?_
  split_ifs <;> simp

lemma Rf_map (i1 : Fin n) : (uniformMeasure (cube n)).map (Rf i1) = uniformMeasure (cube n) := by
  ext S hS
  rw [Measure.map_apply (Rf i1).continuous.measurable hS, unif_apply, unif_apply]
  congr 1
  rw [← Rf_cube i1, ← preimage_inter, (Rf i1).measurePreserving.measure_preimage
    (hS.inter meas_cube).nullMeasurableSet, Rf_cube]

section
variable {i0 i1 : Fin n} (h01 : i0 ≠ i1) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1 / 4)
include h01 hs0 hs1

lemma coupling_exists : ∃ π : Measure (E n × E n),
    IsCoupling ((uniformMeasure (cube n)).map (Tm i0 i1 s s))
      ((uniformMeasure (cube n)).map (Tm i0 i1 (-s) s)) π ∧
    quadraticPlanCost π ≤ ENNReal.ofReal (8 * s ^ 3) := by
  have hT1 := Tm_meas h01 (b := s) (s := s)
  have hT2 := Tm_meas h01 (b := -s) (s := s)
  have hR := (Rf (n := n) i1).continuous.measurable
  set F : E n → E n × E n := fun x => (Tm i0 i1 s s x, Tm i0 i1 (-s) s (Rf i1 x))
  have hF : Measurable F := Measurable.prodMk hT1 (hT2.comp hR)
  refine ⟨(uniformMeasure (cube n)).map F, ⟨Measure.isProbabilityMeasure_map hF.aemeasurable, ?_, ?_⟩, ?_⟩
  · rw [Measure.map_map measurable_fst hF]; rfl
  · rw [Measure.map_map measurable_snd hF]
    change Measure.map (Tm i0 i1 (-s) s ∘ Rf i1) _ = _
    rw [← Measure.map_map hT2 hR, Rf_map]
  · set C : Set (E n) := {x | |x i0| < s * x i1 + s}
    have hCm : MeasurableSet C := measurableSet_lt (by fun_prop) (by fun_prop)
    rw [quadraticPlanCost, lintegral_map (by fun_prop) hF]
    have hpt : ∀ x, ENNReal.ofReal (‖(F x).1 - (F x).2‖ ^ 2) ≤
        C.indicator (fun _ => ENNReal.ofReal (4 * s ^ 2)) x := by
      intro x
      simp only [F]
      have hR0 : Rf i1 x i0 = x i0 := by rw [Rf_apply, if_neg h01]
      have hR1 : Rf i1 x i1 = -x i1 := by rw [Rf_apply, if_pos rfl]
      unfold Tm; rw [hR0, hR1, neg_mul_neg]
      by_cases hC : |x i0| < s * x i1 + s
      · rw [indicator_of_mem (show x ∈ C from hC), if_pos hC, if_pos hC]
        apply ENNReal.ofReal_le_ofReal
        rw [show s • ee (n := n) i1 - (-s) • ee i1 = (2 * s) • ee i1 by module, norm_smul, ee,
          EuclideanSpace.norm_single]
        simp [abs_of_pos hs0]; nlinarith
      · rw [indicator_of_notMem (show x ∉ C from hC), if_neg hC, if_neg hC]
        split_ifs <;> simp
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_indicator_const hCm]
    have hCb : uniformMeasure (cube n) C ≤ ENNReal.ofReal (2 * s) := by
      have := unif_le_boxc C (fun i => if i = i0 then -(2 * s) else -1)
        (fun i => if i = i0 then 2 * s else 1) (by intro i; split_ifs <;> linarith) (by
          intro x ⟨hxC, hxc⟩ i
          simp only [C, mem_setOf_eq] at hxC
          have h1 := hxc i1; have h0 := hxc i
          rw [abs_le] at h1 h0
          split_ifs with h
          · subst h; rw [abs_lt] at hxC; constructor <;> nlinarith
          · exact h0)
      have e : (fun i => (if i = i0 then 2 * s else 1) - (if i = i0 then -(2 * s) else -1)) =
          fun i => if i = i0 then 4 * s else 2 := by
        funext i; split_ifs <;> ring
      rw [e, prod1] at this
      obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := two_le h01; omega⟩
      convert this using 2
      rw [hk, Nat.add_sub_cancel, pow_succ]; field_simp; ring
    calc ENNReal.ofReal (4 * s ^ 2) * uniformMeasure (cube n) C
        ≤ ENNReal.ofReal (4 * s ^ 2) * ENNReal.ofReal (2 * s) := mul_le_mul_right hCb _
      _ = ENNReal.ofReal (8 * s ^ 3) := by
        rw [← ENNReal.ofReal_mul (by positivity)]; ring_nf

lemma coupling_lower (π : Measure (E n × E n))
    (hπ : IsCoupling ((uniformMeasure (cube n)).map (Tm i0 i1 s s))
      ((uniformMeasure (cube n)).map (Tm i0 i1 (-s) s)) π) :
    ENNReal.ofReal (4 * s ^ 2) * uniformMeasure (cube n) (Tm i0 i1 s s ⁻¹' {s • ee i1}) ≤
      quadraticPlanCost π := by
  obtain ⟨_, hπ2, hπ3⟩ := hπ
  have hT1 := Tm_meas h01 (b := s) (s := s)
  have hT2 := Tm_meas h01 (b := -s) (s := s)
  have hae2 : ∀ᵐ p ∂π, p.2 ∈ At i0 i1 (-s) := by
    have : ∀ᵐ y ∂((uniformMeasure (cube n)).map (Tm i0 i1 (-s) s)), y ∈ At i0 i1 (-s) := by
      have hm : MeasurableSet ((At i0 i1 (-s) : Set (E n))ᶜ) :=
        (At i0 i1 (-s)).finite_toSet.measurableSet.compl
      rw [ae_iff]; change (Measure.map _ _) ((At i0 i1 (-s) : Set (E n))ᶜ) = 0
      rw [Measure.map_apply hT2 hm]; convert measure_empty (μ := uniformMeasure (cube n))
      ext x; simp [Tm_mem h01]
    rw [← hπ3] at this
    exact ae_of_ae_map measurable_snd.aemeasurable this
  set P : Set (E n × E n) := Prod.fst ⁻¹' {s • ee i1}
  have hPm : MeasurableSet P := measurable_fst (measurableSet_singleton _)
  have hpt : ∀ᵐ p ∂π, P.indicator (fun _ => ENNReal.ofReal (4 * s ^ 2)) p ≤
      ENNReal.ofReal (‖p.1 - p.2‖ ^ 2) := by
    filter_upwards [hae2] with p hp
    by_cases hP : p ∈ P
    · rw [indicator_of_mem hP]
      simp only [P, mem_preimage, mem_singleton_iff] at hP
      rw [hP]
      apply ENNReal.ofReal_le_ofReal
      have h2s : 2 * s ≤ ‖s • ee i1 - p.2‖ := by
        simp only [At, Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with h | h | h <;> rw [h]
        · rw [show s • ee (n := n) i1 - (-s) • ee i1 = (2 * s) • ee i1 by module, norm_smul, ee,
            EuclideanSpace.norm_single]
          simp [abs_of_pos hs0]
        · have := PiLp.norm_apply_le (s • ee i1 - -ee (n := n) i0) i0
          simp [h01] at this; rw [sub_neg_eq_add]; linarith
        · have := PiLp.norm_apply_le (s • ee i1 - ee (n := n) i0) i0
          simp [h01] at this; linarith
      nlinarith
    · rw [indicator_of_notMem hP]; exact bot_le
  refine le_trans ?_ (lintegral_mono_ae hpt)
  rw [lintegral_indicator_const hPm]
  apply le_of_eq; congr 1
  rw [← Measure.map_apply hT1 (measurableSet_singleton _), ← hπ2,
    Measure.map_apply measurable_fst (measurableSet_singleton _)]
end

lemma Tm_in_cube {i0 i1 : Fin n} (h01 : i0 ≠ i1) {b s : ℝ} (hb : |b| ≤ 1) (x : E n) :
    Tm i0 i1 b s x ∈ cube n := by
  intro j
  unfold Tm
  split_ifs <;> by_cases hj0 : j = i0 <;> by_cases hj1 : j = i1 <;>
    simp [ee_apply, hj0, hj1, abs_mul, hb, h01, h01.symm]

lemma Tm_supp {i0 i1 : Fin n} (h01 : i0 ≠ i1) {b s : ℝ} (hb : |b| ≤ 1) :
    IsSupported ((uniformMeasure (cube n)).map (Tm i0 i1 b s)) (cube n) := by
  rw [IsSupported, Measure.map_apply (Tm_meas h01) meas_cube.compl]
  convert measure_empty (μ := uniformMeasure (cube n))
  ext x; simp [Tm_in_cube h01 hb x]

lemma Tm_atoms {i0 i1 : Fin n} (h01 : i0 ≠ i1) {b s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1 / 4)
    (hb : |b| ≤ s) :
    HasExactlyThreeAtoms ((uniformMeasure (cube n)).map (Tm i0 i1 b s)) (cube n) := by
  refine three_atoms h01 (hb.trans (by linarith)) ?_
  intro y hy
  simp only [At, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl
  · exact w1_pos h01 hs0 hs1 hb
  · exact w2_pos h01 hs0 hs1 hb
  · exact w3_pos h01 hs0 hs1 hb

lemma w2_bounds {i0 i1 : Fin n} (h01 : i0 ≠ i1) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1 / 4) :
    0 < wasserstein2 ((uniformMeasure (cube n)).map (Tm i0 i1 s s))
      ((uniformMeasure (cube n)).map (Tm i0 i1 (-s) s)) ∧
    wasserstein2 ((uniformMeasure (cube n)).map (Tm i0 i1 s s))
      ((uniformMeasure (cube n)).map (Tm i0 i1 (-s) s)) ≤ Real.sqrt (8 * s ^ 3) := by
  obtain ⟨π0, hc, hcost⟩ := coupling_exists h01 hs0 hs1
  unfold wasserstein2
  set I := sInf {cost : ℝ≥0∞ | ∃ plan : Measure (E n × E n),
    IsCoupling ((uniformMeasure (cube n)).map (Tm i0 i1 s s))
      ((uniformMeasure (cube n)).map (Tm i0 i1 (-s) s)) plan ∧ quadraticPlanCost plan = cost}
  have hle : I ≤ ENNReal.ofReal (8 * s ^ 3) := by
    refine le_trans (sInf_le ?_) hcost
    exact ⟨π0, hc, rfl⟩
  have hge : ENNReal.ofReal (4 * s ^ 2) *
      uniformMeasure (cube n) (Tm i0 i1 s s ⁻¹' {s • ee i1}) ≤ I := by
    apply le_sInf; rintro _ ⟨π, hπ, rfl⟩; exact coupling_lower h01 hs0 hs1 π hπ
  have hw := w1_pos h01 hs0 hs1 (b := s) (by rw [abs_of_pos hs0])
  have hpos : 0 < I := lt_of_lt_of_le
    (ENNReal.mul_pos (ENNReal.ofReal_pos.2 (by positivity)).ne' hw.ne') hge
  have hne : I ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  constructor
  · exact Real.sqrt_pos.2 (ENNReal.toReal_pos hpos.ne' hne)
  · exact Real.sqrt_le_sqrt (ENNReal.toReal_le_of_le_ofReal (by positivity) hle)

theorem main_sharp :
    ∀ (dimension : ℕ), 2 ≤ dimension → ∀ exponent : ℝ, (1 / 3 : ℝ) < exponent →
      ∀ constant : ℝ, 0 < constant →
        ∃ (first second : Measure (E dimension)) (firstMap secondMap : E dimension → E dimension),
          IsProbabilityMeasure first ∧ IsProbabilityMeasure second ∧
          IsSupported first (cube dimension) ∧ IsSupported second (cube dimension) ∧
          HasExactlyThreeAtoms first (cube dimension) ∧
          HasExactlyThreeAtoms second (cube dimension) ∧
          first ≠ second ∧
          IsUniqueQuadraticOptimalMap (uniformMeasure (cube dimension)) first firstMap ∧
          IsUniqueQuadraticOptimalMap (uniformMeasure (cube dimension)) second secondMap ∧
          0 < wasserstein2 first second ∧
          constant * Real.rpow (wasserstein2 first second) exponent <
            mapL2Dist (uniformMeasure (cube dimension)) firstMap secondMap := by
  intro n hn p hp C hC
  set i0 : Fin n := ⟨0, by omega⟩
  set i1 : Fin n := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  -- choice of s
  set q : ℝ := (3 * p - 1) / 2
  have hq : 0 < q := by simp only [q]; linarith
  have hp0 : 0 ≤ p := by linarith
  set K : ℝ := 1 / (4 * C * (8:ℝ) ^ (p / 2))
  have hK : 0 < K := by positivity
  set s : ℝ := min (1 / 4) ((K / 2) ^ q⁻¹)
  have hs0 : 0 < s := lt_min (by norm_num) (by positivity)
  have hs1 : s ≤ 1 / 4 := min_le_left _ _
  have hsq : s ^ q < K := by
    calc s ^ q ≤ ((K / 2) ^ q⁻¹) ^ q :=
          Real.rpow_le_rpow hs0.le (min_le_right _ _) hq.le
      _ = K / 2 := Real.rpow_inv_rpow (by positivity) hq.ne'
      _ < K := by linarith
  have hb1 : |s| ≤ s := le_of_eq (abs_of_pos hs0)
  have hb2 : |-s| ≤ s := le_of_eq (by rw [abs_neg, abs_of_pos hs0])
  have hb1' : |s| ≤ 1 := by rw [abs_of_pos hs0]; linarith
  have hb2' : |-s| ≤ 1 := by rw [abs_neg, abs_of_pos hs0]; linarith
  obtain ⟨hW0, hW⟩ := w2_bounds h01 hs0 hs1
  refine ⟨_, _, Tm i0 i1 s s, Tm i0 i1 (-s) s,
    Measure.isProbabilityMeasure_map (Tm_meas h01).aemeasurable,
    Measure.isProbabilityMeasure_map (Tm_meas h01).aemeasurable,
    Tm_supp h01 hb1', Tm_supp h01 hb2', Tm_atoms h01 hs0 hs1 hb1, Tm_atoms h01 hs0 hs1 hb2,
    mu_ne h01 hs0 hs1, opt h01 s hb1', opt h01 s hb2', hW0, ?_⟩
  set W := wasserstein2 ((uniformMeasure (cube n)).map (Tm i0 i1 s s))
      ((uniformMeasure (cube n)).map (Tm i0 i1 (-s) s))
  have hL : Real.sqrt (s / 16) ≤ mapL2Dist (uniformMeasure (cube n)) (Tm i0 i1 s s) (Tm i0 i1 (-s) s) :=
    Real.sqrt_le_sqrt (l2_lower h01 hs0 hs1)
  refine lt_of_lt_of_le ?_ hL
  have h1 : Real.rpow W p ≤ (Real.sqrt (8 * s ^ 3)) ^ p :=
    Real.rpow_le_rpow hW0.le hW hp0
  have h2 : (Real.sqrt (8 * s ^ 3)) ^ p = (8:ℝ) ^ (p / 2) * (s ^ q * s ^ (1/2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity), Real.mul_rpow (by norm_num) (by positivity),
      ← Real.rpow_add hs0, show q + 1/2 = 3 * (p/2) by simp only [q]; ring, Real.rpow_mul hs0.le]
    norm_cast
    rw [← Real.rpow_natCast]; norm_num; ring_nf
  have h3 : Real.sqrt (s / 16) = s ^ (1/2 : ℝ) / 4 := by
    rw [Real.sqrt_div' _ (by norm_num), show (16:ℝ) = 4 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num), Real.sqrt_eq_rpow]
  rw [h3]
  have hs12 : 0 < s ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hs0 _
  have h8 : 0 < (8:ℝ) ^ (p / 2) := by positivity
  calc C * Real.rpow W p ≤ C * ((8:ℝ) ^ (p / 2) * (s ^ q * s ^ (1/2 : ℝ))) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hC.le
    _ = (C * (8:ℝ) ^ (p / 2) * s ^ q) * s ^ (1/2 : ℝ) := by ring
    _ < (1/4) * s ^ (1/2 : ℝ) := by
        apply mul_lt_mul_of_pos_right _ hs12
        have : C * (8:ℝ) ^ (p / 2) * s ^ q < C * (8:ℝ) ^ (p / 2) * K :=
          mul_lt_mul_of_pos_left hsq (by positivity)
        have e : C * (8:ℝ) ^ (p / 2) * K = 1/4 := by
          simp only [K]; field_simp
        linarith
    _ = s ^ (1/2 : ℝ) / 4 := by ring

end BrSharp
end Problem358
end
end OAI

open MeasureTheory OAI.Problem358 in
theorem solution :
    ∀ (dimension : ℕ), 2 ≤ dimension → ∀ exponent : ℝ, (1 / 3 : ℝ) < exponent →
      ∀ constant : ℝ, 0 < constant →
        ∃ (first second : Measure (E dimension)) (firstMap secondMap : E dimension → E dimension),
          IsProbabilityMeasure first ∧ IsProbabilityMeasure second ∧
          IsSupported first (cube dimension) ∧ IsSupported second (cube dimension) ∧
          HasExactlyThreeAtoms first (cube dimension) ∧
          HasExactlyThreeAtoms second (cube dimension) ∧
          first ≠ second ∧
          IsUniqueQuadraticOptimalMap (uniformMeasure (cube dimension)) first firstMap ∧
          IsUniqueQuadraticOptimalMap (uniformMeasure (cube dimension)) second secondMap ∧
          0 < wasserstein2 first second ∧
          constant * Real.rpow (wasserstein2 first second) exponent <
            mapL2Dist (uniformMeasure (cube dimension)) firstMap secondMap :=
  OAI.Problem358.BrSharp.main_sharp
