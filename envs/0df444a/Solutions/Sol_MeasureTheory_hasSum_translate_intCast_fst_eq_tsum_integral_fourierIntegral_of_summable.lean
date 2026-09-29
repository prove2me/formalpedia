-- Prove2me | solution 1 for MeasureTheory.hasSum_translate_intCast_fst_eq_tsum_integral_fourierIntegral_of_summable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/d5ce228d-bd41-53e2-8d9c-f9997d2ee8c6

import Mathlib
import Theorems.Thm_Real_tsum_comp_add_intCast_eq_tsum_integral_mul_cexp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_hasSum_translate_intCast_fst_eq_tsum_integral_fourierIntegral_of_summable

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

p2m_open "MeasureTheory P2MW.S_MeasureTheory_hasSum_translate_intCast_fst_eq_tsum_integral_fourierIntegral_of_summable.MeasureTheory Filter Topology Complex TopologicalSpace"
open scoped BigOperators ENNReal FourierTransform InnerProductSpace

noncomputable section

section CubeLemma
open Set
namespace CubeDecomp

variable {d : Type*} [Fintype d]

def cube (k : d → ℤ) : Set (d → ℝ) := Set.pi Set.univ (fun i => Set.Ico (k i : ℝ) (k i + 1))

theorem mem_cube_iff (k : d → ℤ) (w : d → ℝ) : w ∈ cube k ↔ ∀ i, ⌊w i⌋ = k i := by
  simp only [cube, Set.mem_univ_pi, Set.mem_Ico, Int.floor_eq_iff]

theorem mem_cube_floor (w : d → ℝ) : w ∈ cube (fun i => ⌊w i⌋) :=
  (mem_cube_iff _ w).2 fun _ => rfl

theorem measurableSet_cube (k : d → ℤ) : MeasurableSet (cube k) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

theorem pairwise_disjoint_cube : Pairwise (Function.onFun Disjoint (cube (d := d))) := by
  intro k k' hkk'
  rw [Function.onFun, Set.disjoint_left]
  intro w hw hw'
  apply hkk'
  funext i
  rw [← (mem_cube_iff k w).1 hw i, (mem_cube_iff k' w).1 hw' i]

theorem iUnion_cube : (⋃ k : d → ℤ, cube k) = Set.univ :=
  Set.eq_univ_of_forall fun w => Set.mem_iUnion.2 ⟨_, mem_cube_floor w⟩

theorem volume_cube (k : d → ℤ) : volume (cube k) = 1 := by
  rw [cube, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ico]

theorem eqOn_cube (M : (d → ℤ) → ℝ) (k : d → ℤ) :
    Set.EqOn (fun w : d → ℝ => M (fun i => ⌊w i⌋)) (fun _ => M k) (cube k) := by
  intro w hw
  have : (fun i => ⌊w i⌋) = k := funext ((mem_cube_iff k w).1 hw)
  simp only [this]

theorem integrableOn_cube (M : (d → ℤ) → ℝ) (k : d → ℤ) :
    IntegrableOn (fun w : d → ℝ => M (fun i => ⌊w i⌋)) (cube k) := by
  refine IntegrableOn.congr_fun ?_ (eqOn_cube M k).symm (measurableSet_cube k)
  refine integrableOn_const ?_
  rw [volume_cube]; exact ENNReal.one_ne_top

theorem setIntegral_cube (M : (d → ℤ) → ℝ) (k : d → ℤ) :
    ∫ w in cube k, M (fun i => ⌊w i⌋) = M k := by
  rw [setIntegral_congr_fun (measurableSet_cube k) (eqOn_cube M k), setIntegral_const]
  simp [measureReal_def, volume_cube]

theorem setIntegral_norm_cube (M : (d → ℤ) → ℝ) (k : d → ℤ) :
    ∫ w in cube k, ‖M (fun i => ⌊w i⌋)‖ = ‖M k‖ := by
  have h : Set.EqOn (fun w : d → ℝ => ‖M (fun i => ⌊w i⌋)‖) (fun _ => ‖M k‖) (cube k) := fun w hw => by
    simp only [eqOn_cube M k hw]
  rw [setIntegral_congr_fun (measurableSet_cube k) h, setIntegral_const]
  simp [measureReal_def, volume_cube]

end CubeDecomp

namespace MeasureTheory p2m_export "MeasureTheory" "Measure setIntegral_congr_fun MeasurePreserving hasSum_integral_iUnion continuousAt_of_dominated setIntegral_const IntegrableOn Measure.prod volume_pi Measure.pi_pi integrableOn_const continuous_of_dominated IntegrableOn.congr_fun Measure.prod.instIsAddHaarMeasure measureReal_def MeasurePreserving.integral_comp' norm_integral_le_integral_norm integrableOn_univ Integrable integrable_comp integral_prod_symm integral_const_mul setIntegral_univ integrableOn_iUnion_of_summable_integral_norm" end MeasureTheory
p2m_open_scoped "MeasureTheory" in
open CubeDecomp in
theorem MeasureTheory.integrable_comp_intFloor_and_integral_eq_tsum
    {d : Type*} [Fintype d] (M : (d → ℤ) → ℝ) (hM : Summable M) :
    Integrable (fun w : d → ℝ => M (fun i => ⌊w i⌋)) ∧
      ∫ w : d → ℝ, M (fun i => ⌊w i⌋) = ∑' k : d → ℤ, M k := by
  have hIU : IntegrableOn (fun w : d → ℝ => M (fun i => ⌊w i⌋)) (⋃ k : d → ℤ, cube k) := by
    refine integrableOn_iUnion_of_summable_integral_norm (integrableOn_cube M) ?_
    simp only [setIntegral_norm_cube]
    exact hM.norm
  have hI : Integrable (fun w : d → ℝ => M (fun i => ⌊w i⌋)) := by
    rw [iUnion_cube] at hIU
    exact integrableOn_univ.1 hIU
  refine ⟨hI, ?_⟩
  have hsum := hasSum_integral_iUnion measurableSet_cube pairwise_disjoint_cube hIU
  simp only [setIntegral_cube] at hsum
  rw [iUnion_cube, setIntegral_univ] at hsum
  exact hsum.tsum_eq.symm

end CubeLemma

namespace PoissonSummableSol

variable {a b : ℕ}

def ιZ (κ : Fin a → ℤ) : Fin a → ℝ := fun i => (κ i : ℝ)

scoped instance instHaarProd : (volume : Measure ((Fin a → ℝ) × (Fin b → ℝ))).IsAddHaarMeasure :=
  MeasureTheory.Measure.prod.instIsAddHaarMeasure _ _

scoped instance instHaarProd' :
    ((volume : Measure (Fin a → ℝ)).prod (volume : Measure (Fin b → ℝ))).IsAddHaarMeasure :=
  MeasureTheory.Measure.prod.instIsAddHaarMeasure _ _

lemma norm_cexp_neg_mul_I (t : ℝ) :
    ‖Complex.exp (-(2 * Real.pi * Complex.I * (t : ℂ)))‖ = 1 := by
  have : -(2 * Real.pi * Complex.I * (t : ℂ)) = ((-(2 * Real.pi * t) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma norm_cexp_mul_I (t : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))‖ = 1 := by
  have : (2 * Real.pi * Complex.I * (t : ℂ)) = (((2 * Real.pi * t) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

def LocDom (f : (Fin a → ℝ) × (Fin b → ℝ) → ℂ) : Prop :=
  ∀ y : (Fin a → ℝ) × (Fin b → ℝ), ∃ V ∈ nhds y, ∃ M : (Fin a → ℤ) → ℝ, Summable M ∧
      ∀ y' ∈ V, ∀ k : Fin a → ℤ, ‖f (y' + (fun i => (k i : ℝ), 0))‖ ≤ M k

def fhatF (f : (Fin a → ℝ) × (Fin b → ℝ) → ℂ) (κ : Fin a → ℤ) (η : Fin b → ℝ) : ℂ :=
  ∫ p : (Fin a → ℝ) × (Fin b → ℝ),
    Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, (κ i : ℝ) * p.1 i + ∑ j, η j * p.2 j : ℝ) : ℂ))) * f p

def pF (f : (Fin a → ℝ) × (Fin b → ℝ) → ℂ) (κ : Fin a → ℤ) (z : Fin b → ℝ) : ℂ :=
  ∫ w : Fin a → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, (κ i : ℝ) * w i : ℝ) : ℂ))) * f (w, z)

def slice (f : (Fin a → ℝ) × (Fin b → ℝ) → ℂ) (hfc : Continuous f) (z : Fin b → ℝ) : C(Fin a → ℝ, ℂ) :=
  ⟨fun w => f (w, z), hfc.comp (continuous_id.prodMk continuous_const)⟩

lemma continuous_fhatF (f : (Fin a → ℝ) × (Fin b → ℝ) → ℂ) (hfi : Integrable f) (κ : Fin a → ℤ) :
    Continuous (fhatF f κ) := by
  unfold fhatF
  refine continuous_of_dominated (bound := fun p => ‖f p‖) ?_ ?_ hfi.norm ?_
  · intro η
    exact (Continuous.aestronglyMeasurable (by fun_prop)).mul hfi.aestronglyMeasurable
  · intro η
    refine Filter.Eventually.of_forall fun p => ?_
    rw [norm_mul, norm_cexp_neg_mul_I, one_mul]
  · refine Filter.Eventually.of_forall fun p => ?_
    fun_prop

lemma hnorm_slice (f : (Fin a → ℝ) × (Fin b → ℝ) → ℂ) (hfc : Continuous f) (hloc : LocDom f)
    (z : Fin b → ℝ) (K : Compacts (Fin a → ℝ)) :
    Summable fun n : Fin a → ℤ => ‖((slice f hfc z).comp (ContinuousMap.addRight (fun i => (n i : ℝ)))).restrict K‖ := by
  classical
  choose V hV M hMs hM using fun x : Fin a → ℝ => hloc (x, z)
  have hU : ∀ x : Fin a → ℝ, {x' : Fin a → ℝ | (x', z) ∈ V x} ∈ nhds x := fun x =>
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hV x)
  obtain ⟨t, -, hcover⟩ := K.isCompact.elim_nhds_subcover (fun x => {x' : Fin a → ℝ | (x', z) ∈ V x})
    (fun x _ => hU x)
  have hMnn : ∀ x k, 0 ≤ M x k := fun x k =>
    le_trans (norm_nonneg _) (hM x (x, z) (mem_of_mem_nhds (hV x)) k)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (summable_sum fun x _ => hMs x : Summable fun n => ∑ x ∈ t, M x n)
  apply (ContinuousMap.norm_le _ (Finset.sum_nonneg fun x _ => hMnn x n)).2
  rintro ⟨x', hx'⟩
  have hx'' := hcover hx'
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hx''
  obtain ⟨x, hxt, hx'U⟩ := hx''
  have h1 : ‖f ((x', z) + (fun i => (n i : ℝ), 0))‖ ≤ M x n := hM x (x', z) hx'U n
  have h2 : ((slice f hfc z).comp (ContinuousMap.addRight (fun i => (n i : ℝ)))).restrict K ⟨x', hx'⟩ =
      f ((x', z) + (fun i => (n i : ℝ), 0)) := by
    simp only [ContinuousMap.restrict_apply, ContinuousMap.comp_apply, ContinuousMap.coe_addRight, slice,
      ContinuousMap.coe_mk]
    congr 1; ext <;> simp
  rw [h2]
  exact h1.trans (Finset.single_le_sum (fun x _ => hMnn x n) hxt)

lemma continuous_pF (f : (Fin a → ℝ) × (Fin b → ℝ) → ℂ) (hfc : Continuous f) (hloc : LocDom f) (κ : Fin a → ℤ) :
    Continuous (pF f κ) := by
  classical
  refine continuous_iff_continuousAt.2 fun z₀ => ?_

  have hprod : ∀ u : Fin a → ℝ, ∃ A ∈ nhds u, ∃ B ∈ nhds z₀, ∃ M : (Fin a → ℤ) → ℝ, Summable M ∧
      ∀ u' ∈ A, ∀ z ∈ B, ∀ k : Fin a → ℤ, ‖f ((u', z) + (fun i => (k i : ℝ), 0))‖ ≤ M k := by
    intro u
    obtain ⟨V, hV, M, hMs, hM⟩ := hloc (u, z₀)
    obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 hV
    exact ⟨A, hA, B, hB, M, hMs, fun u' hu' z hz k => hM (u', z) (hAB (Set.mk_mem_prod hu' hz)) k⟩
  choose A hA B hB M hMs hM using hprod

  have hCc : IsCompact (Set.pi Set.univ (fun _ : Fin a => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨t, -, hcover⟩ := hCc.elim_nhds_subcover A (fun u _ => hA u)
  have hMnn : ∀ u k, 0 ≤ M u k := fun u k =>
    le_trans (norm_nonneg _) (hM u u (mem_of_mem_nhds (hA u)) z₀ (mem_of_mem_nhds (hB u)) k)
  have hMts : Summable (fun k : Fin a → ℤ => ∑ u ∈ t, M u k) := summable_sum fun u _ => hMs u
  have hBt : (⋂ u ∈ t, B u) ∈ nhds z₀ := (Filter.biInter_finset_mem t).2 fun u _ => hB u

  have hdom : ∀ z ∈ ⋂ u ∈ t, B u, ∀ w : Fin a → ℝ, ‖f (w, z)‖ ≤ ∑ u ∈ t, M u (fun i => ⌊w i⌋) := by
    intro z hz w
    have hvC : (fun i => w i - (⌊w i⌋ : ℝ)) ∈ Set.pi Set.univ (fun _ : Fin a => Set.Icc (0 : ℝ) 1) := by
      simp only [Set.mem_univ_pi, Set.mem_Icc]
      intro i
      exact ⟨sub_nonneg.2 (Int.floor_le _), by linarith [Int.lt_floor_add_one (w i)]⟩
    have hcov := hcover hvC
    simp only [Set.mem_iUnion, exists_prop] at hcov
    obtain ⟨u, hut, hvu⟩ := hcov
    have hzB : z ∈ B u := (Set.mem_iInter₂.1 hz) u hut
    have h1 := hM u _ hvu z hzB (fun i => ⌊w i⌋)
    have hvk : ((fun i => w i - (⌊w i⌋ : ℝ)), z) + ((fun i => ((⌊w i⌋ : ℤ) : ℝ)), (0 : Fin b → ℝ)) = (w, z) := by
      ext i <;> simp
    rw [hvk] at h1
    exact h1.trans (Finset.single_le_sum (fun u _ => hMnn u _) hut)

  unfold pF
  refine continuousAt_of_dominated (bound := fun w : Fin a → ℝ => ∑ u ∈ t, M u (fun i => ⌊w i⌋)) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun z => Continuous.aestronglyMeasurable (by fun_prop)
  · refine Filter.eventually_of_mem hBt fun z hz => Filter.Eventually.of_forall fun w => ?_
    rw [norm_mul, norm_cexp_neg_mul_I, one_mul]
    exact hdom z hz w
  · exact (MeasureTheory.integrable_comp_intFloor_and_integral_eq_tsum (fun k => ∑ u ∈ t, M u k) hMts).1
  · exact Filter.Eventually.of_forall fun w =>
      (show Continuous (fun z : Fin b → ℝ =>
        Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, (κ i : ℝ) * w i : ℝ) : ℂ))) * f (w, z)) by fun_prop).continuousAt

lemma integrable_pF (f : (Fin a → ℝ) × (Fin b → ℝ) → ℂ) (hfi : Integrable f) (κ : Fin a → ℤ) :
    Integrable (pF f κ) := by
  set G : (Fin a → ℝ) × (Fin b → ℝ) → ℂ := fun p =>
    Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, (κ i : ℝ) * p.1 i : ℝ) : ℂ))) * f p with hG
  have hGint : Integrable G (volume.prod volume) := by
    have hf : Integrable (fun p : (Fin a → ℝ) × (Fin b → ℝ) => f p) (volume.prod volume) := hfi
    refine hf.bdd_mul (c := 1) ?_ ?_
    · exact (Continuous.aestronglyMeasurable (by fun_prop))
    · exact Filter.Eventually.of_forall fun p => (norm_cexp_neg_mul_I _).le
  have := hGint.integral_prod_right
  exact this

lemma integral_cexp_mul_pF (f : (Fin a → ℝ) × (Fin b → ℝ) → ℂ) (hfi : Integrable f) (κ : Fin a → ℤ) (η : Fin b → ℝ) :
    ∫ z : Fin b → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, η j * z j : ℝ) : ℂ))) * pF f κ z =
      fhatF f κ η := by
  set G : (Fin a → ℝ) × (Fin b → ℝ) → ℂ := fun p =>
    Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, (κ i : ℝ) * p.1 i + ∑ j, η j * p.2 j : ℝ) : ℂ))) * f p with hG
  have hGint : Integrable G (volume.prod volume) := by
    have hf : Integrable (fun p : (Fin a → ℝ) × (Fin b → ℝ) => f p) (volume.prod volume) := hfi
    refine hf.bdd_mul (c := 1) ?_ ?_
    · exact (Continuous.aestronglyMeasurable (by fun_prop))
    · exact Filter.Eventually.of_forall fun p => (norm_cexp_neg_mul_I _).le
  have hfub := integral_prod_symm G hGint
  have hlhs : fhatF f κ η = ∫ p, G p ∂(volume.prod volume) := rfl
  rw [hlhs, hfub]
  congr 1
  funext z
  rw [pF, ← integral_const_mul]
  congr 1
  funext w
  simp only [hG]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

lemma inner_eq_sum (v w : EuclideanSpace ℝ (Fin b)) :
    ⟪v, w⟫_ℝ = ∑ j, (WithLp.ofLp v) j * (WithLp.ofLp w) j := by
  rw [PiLp.inner_apply]
  simp [mul_comm]

lemma pF_eq_integral (f : (Fin a → ℝ) × (Fin b → ℝ) → ℂ) (hfc : Continuous f) (hfi : Integrable f)
    (hloc : LocDom f) (κ : Fin a → ℤ) (hint : Integrable (fhatF f κ)) (z : Fin b → ℝ) :
    pF f κ z = ∫ η : Fin b → ℝ, fhatF f κ η *
      Complex.exp (2 * Real.pi * Complex.I * ((∑ j, η j * z j : ℝ) : ℂ)) := by
  have hcont : Continuous (fhatF f κ) := continuous_fhatF f hfi κ
  set Pκ : EuclideanSpace ℝ (Fin b) → ℂ := fun v => pF f κ (WithLp.ofLp v) with hPκ
  have hPcont : Continuous Pκ := (continuous_pF f hfc hloc κ).comp (PiLp.continuous_ofLp 2 _)
  have hPint : Integrable Pκ :=
    ((PiLp.volume_preserving_ofLp (Fin b)).integrable_comp
      (continuous_pF f hfc hloc κ).aestronglyMeasurable).mpr (integrable_pF f hfi κ)
  have hFT : 𝓕 Pκ = fun ξ => fhatF f κ (WithLp.ofLp ξ) := by
    funext ξ
    rw [Real.fourier_eq']
    have hcv := MeasurePreserving.integral_comp'
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin b))
      (fun z : Fin b → ℝ => Complex.exp (↑(-2 * Real.pi * (∑ j, z j * (WithLp.ofLp ξ) j)) * Complex.I) * pF f κ z)
    simp only [MeasurableEquiv.toLp_symm_apply] at hcv
    have hlhs : (∫ v : EuclideanSpace ℝ (Fin b), Complex.exp (↑(-2 * Real.pi * ⟪v, ξ⟫_ℝ) * Complex.I) • Pκ v) =
        ∫ v : EuclideanSpace ℝ (Fin b),
          Complex.exp (↑(-2 * Real.pi * (∑ j, (WithLp.ofLp v) j * (WithLp.ofLp ξ) j)) * Complex.I) *
            pF f κ (WithLp.ofLp v) := by
      congr 1; funext v; rw [inner_eq_sum, smul_eq_mul]
    rw [hlhs, hcv, ← integral_cexp_mul_pF f hfi κ (WithLp.ofLp ξ)]
    congr 1; funext z
    congr 2
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hFTint : Integrable (𝓕 Pκ) := by
    rw [hFT]
    exact ((PiLp.volume_preserving_ofLp (Fin b)).integrable_comp hcont.aestronglyMeasurable).mpr hint
  have hinv := Continuous.fourierInv_fourier_eq hPcont hPint hFTint
  have heval := congr_fun hinv (WithLp.toLp 2 z)
  have hrhs : Pκ (WithLp.toLp 2 z) = pF f κ z := rfl
  rw [hrhs] at heval
  rw [← heval, hFT, Real.fourierInv_eq']
  have hcv := MeasurePreserving.integral_comp'
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin b))
    (fun η : Fin b → ℝ => Complex.exp (↑(2 * Real.pi * (∑ j, η j * z j)) * Complex.I) * fhatF f κ η)
  simp only [MeasurableEquiv.toLp_symm_apply] at hcv
  have hlhs : (∫ v : EuclideanSpace ℝ (Fin b),
      Complex.exp (↑(2 * Real.pi * ⟪v, (WithLp.toLp 2 z : EuclideanSpace ℝ (Fin b))⟫_ℝ) * Complex.I) •
        fhatF f κ (WithLp.ofLp v)) =
      ∫ v : EuclideanSpace ℝ (Fin b),
        Complex.exp (↑(2 * Real.pi * (∑ j, (WithLp.ofLp v) j * z j)) * Complex.I) * fhatF f κ (WithLp.ofLp v) := by
    congr 1; funext v; rw [inner_eq_sum, smul_eq_mul]
  rw [hlhs, hcv]
  congr 1; funext η
  rw [mul_comm]
  congr 2
  push_cast
  ring

theorem main (f : (Fin a → ℝ) × (Fin b → ℝ) → ℂ) (hfc : Continuous f) (hfi : Integrable f) (hloc : LocDom f)
    (fhat : (Fin a → ℤ) → (Fin b → ℝ) → ℂ)
    (hfhat : ∀ (κ : Fin a → ℤ) (η : Fin b → ℝ), fhat κ η =
      ∫ p : (Fin a → ℝ) × (Fin b → ℝ),
        Complex.exp (-(2 * Real.pi * Complex.I *
          ((∑ i, (κ i : ℝ) * p.1 i + ∑ j, η j * p.2 j : ℝ) : ℂ))) * f p)
    (hint : ∀ κ : Fin a → ℤ, Integrable (fhat κ))
    (hsum : Summable (fun κ : Fin a → ℤ => ∫ η, ‖fhat κ η‖)) :
    (∀ κ : Fin a → ℤ, Continuous (fhat κ)) ∧
    ∀ y : (Fin a → ℝ) × (Fin b → ℝ),
      Summable (fun k : Fin a → ℤ => ‖f (y + (fun i => (k i : ℝ), 0))‖) ∧
      HasSum (fun k : Fin a → ℤ => f (y + (fun i => (k i : ℝ), 0)))
        (∑' κ : Fin a → ℤ, ∫ η : Fin b → ℝ, fhat κ η *
          Complex.exp (2 * Real.pi * Complex.I *
            ((∑ i, (κ i : ℝ) * y.1 i + ∑ j, η j * y.2 j : ℝ) : ℂ))) := by
  have hfh : fhat = fhatF f := by
    funext κ η; rw [hfhat]; rfl
  subst hfh
  refine ⟨fun κ => continuous_fhatF f hfi κ, fun y => ?_⟩

  have hK : Summable fun n : Fin a → ℤ => ‖f (y + (fun i => (n i : ℝ), 0))‖ := by
    have h := hnorm_slice f hfc hloc y.2 ⟨{y.1}, isCompact_singleton⟩
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) h
    have : f (y + (fun i => (n i : ℝ), 0)) =
        ((slice f hfc y.2).comp (ContinuousMap.addRight (fun i => (n i : ℝ)))).restrict
          (⟨{y.1}, isCompact_singleton⟩ : Compacts (Fin a → ℝ)) ⟨y.1, Set.mem_singleton _⟩ := by
      simp [slice, ContinuousMap.restrict_apply, ContinuousMap.comp_apply, ContinuousMap.coe_addRight]
      congr 1; ext <;> simp
    rw [this]
    exact ContinuousMap.norm_coe_le_norm _ _
  refine ⟨hK, ?_⟩

  have hid : ∀ κ : Fin a → ℤ, pF f κ y.2 = ∫ η : Fin b → ℝ, fhatF f κ η *
      Complex.exp (2 * Real.pi * Complex.I * ((∑ j, η j * y.2 j : ℝ) : ℂ)) :=
    fun κ => pF_eq_integral f hfc hfi hloc κ (hint κ) y.2
  have hcoef : Summable fun n : Fin a → ℤ =>
      ∫ w : Fin a → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, (n i : ℝ) * w i : ℝ) : ℂ))) *
        (slice f hfc y.2) w := by
    have : (fun n : Fin a → ℤ => ∫ w : Fin a → ℝ,
        Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, (n i : ℝ) * w i : ℝ) : ℂ))) * (slice f hfc y.2) w) =
        fun n => pF f n y.2 := rfl
    rw [this]
    refine Summable.of_norm_bounded hsum (fun κ => ?_)
    rw [hid κ]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext η
    rw [norm_mul, norm_cexp_mul_I, mul_one]

  have hP := Real.tsum_comp_add_intCast_eq_tsum_integral_mul_cexp (slice f hfc y.2)
    (hnorm_slice f hfc hloc y.2) hcoef y.1
  have hlhs : (fun n : Fin a → ℤ => (slice f hfc y.2) (y.1 + fun i => (n i : ℝ))) =
      fun k => f (y + (fun i => (k i : ℝ), 0)) := by
    funext k
    show f (y.1 + (fun i => (k i : ℝ)), y.2) = f (y + (fun i => (k i : ℝ), 0))
    congr 1; ext <;> simp
  have hterm : ∀ κ : Fin a → ℤ,
      (∫ w : Fin a → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, (κ i : ℝ) * w i : ℝ) : ℂ))) *
          (slice f hfc y.2) w) *
        Complex.exp (2 * Real.pi * Complex.I * ((∑ i, (κ i : ℝ) * y.1 i : ℝ) : ℂ)) =
        ∫ η : Fin b → ℝ, fhatF f κ η *
          Complex.exp (2 * Real.pi * Complex.I * ((∑ i, (κ i : ℝ) * y.1 i + ∑ j, η j * y.2 j : ℝ) : ℂ)) := by
    intro κ
    have : (∫ w : Fin a → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, (κ i : ℝ) * w i : ℝ) : ℂ))) *
          (slice f hfc y.2) w) = pF f κ y.2 := rfl
    rw [this, hid κ, mul_comm, ← integral_const_mul]
    congr 1; funext η
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hlhs] at hP
  simp only [hterm] at hP
  rw [← hP]
  exact hK.of_norm.hasSum

end PoissonSummableSol
p2m_reactivate "P2MW.S_MeasureTheory_hasSum_translate_intCast_fst_eq_tsum_integral_fourierIntegral_of_summable.PoissonSummableSol"

end
p2m_reactivate "P2MW.S_MeasureTheory_hasSum_translate_intCast_fst_eq_tsum_integral_fourierIntegral_of_summable.PoissonSummableSol"

theorem solution
    (a b : ℕ) (f : (Fin a → ℝ) × (Fin b → ℝ) → ℂ) (hfc : Continuous f) (hfi : MeasureTheory.Integrable f)
    (hloc : ∀ y : (Fin a → ℝ) × (Fin b → ℝ), ∃ V ∈ nhds y, ∃ M : (Fin a → ℤ) → ℝ, Summable M ∧
      ∀ y' ∈ V, ∀ k : Fin a → ℤ, ‖f (y' + (fun i => (k i : ℝ), 0))‖ ≤ M k)
    (fhat : (Fin a → ℤ) → (Fin b → ℝ) → ℂ)
    (hfhat : ∀ (κ : Fin a → ℤ) (η : Fin b → ℝ), fhat κ η =
      ∫ p : (Fin a → ℝ) × (Fin b → ℝ),
        Complex.exp (-(2 * Real.pi * Complex.I *
          ((∑ i, (κ i : ℝ) * p.1 i + ∑ j, η j * p.2 j : ℝ) : ℂ))) * f p)
    (hint : ∀ κ : Fin a → ℤ, MeasureTheory.Integrable (fhat κ))
    (hsum : Summable (fun κ : Fin a → ℤ => ∫ η, ‖fhat κ η‖)) :
    (∀ κ : Fin a → ℤ, Continuous (fhat κ)) ∧
    ∀ y : (Fin a → ℝ) × (Fin b → ℝ),
      Summable (fun k : Fin a → ℤ => ‖f (y + (fun i => (k i : ℝ), 0))‖) ∧
      HasSum (fun k : Fin a → ℤ => f (y + (fun i => (k i : ℝ), 0)))
        (∑' κ : Fin a → ℤ, ∫ η : Fin b → ℝ, fhat κ η *
          Complex.exp (2 * Real.pi * Complex.I *
            ((∑ i, (κ i : ℝ) * y.1 i + ∑ j, η j * y.2 j : ℝ) : ℂ))) :=
  PoissonSummableSol.main f hfc hfi hloc fhat hfhat hint hsum

end S_MeasureTheory_hasSum_translate_intCast_fst_eq_tsum_integral_fourierIntegral_of_summable
end P2MW
export P2MW.S_MeasureTheory_hasSum_translate_intCast_fst_eq_tsum_integral_fourierIntegral_of_summable (solution)
