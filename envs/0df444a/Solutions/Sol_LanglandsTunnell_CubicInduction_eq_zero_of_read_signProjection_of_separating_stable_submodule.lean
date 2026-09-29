-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.eq_zero_of_read_signProjection_of_separating_stable_submodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ca55aed2-4e4c-571b-bb09-c079320c0ec5

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Theorems.Thm_LanglandsTunnell_CubicInduction_hasDerivAt_archFlow_eq_eval_inducedPicture_act_of_upperTriangular_equivariant
import Theorems.Thm_LanglandsTunnell_CubicInduction_upperTriangular_equivariant_and_signIsotypic_signProjection
import Theorems.Thm_LanglandsTunnell_CubicInduction_inducedPicture_quantisedMinor_annihilates_lowest_of_matched
import Theorems.Thm_LanglandsTunnell_CubicInduction_inducedPicture_act_det_mul
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_whittaker3_archDeriv_archDeriv_diag_eq_mul_and_whittaker3_archDeriv_corner_eq_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_joint_expansion_coeff_eq_zero_of_forall_whittaker3_diag_mul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_read_signProjection_of_separating_stable_submodule
p2m_attr_erase "instance" "WhittakerBlock.sigmaCompactSpace_adelicGL3 M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply"

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm Topology Filter
open LanglandsTunnell.CubicInduction

namespace WsB
namespace T2

abbrev E33 : Type := Fin 3 → Fin 3 → ℝ
abbrev G3 : Type := AdelicGL 3 (𝓞 ℚ) ℚ
abbrev R9 : Type := MvPolynomial (Fin 3 × Fin 3) ℂ
abbrev R3 : Type := MvPolynomial (Fin 3) ℂ

private def _root_.WsB.T2.ofRealHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v : InfinitePlace ℚ =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.toRingHom

p2m_export "WsB.T2" "ofRealHom"
def realM (e : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) := e.map ofRealHom

theorem archRealMat3_eq (e : E33) : WhittakerBlock.archRealMat3 e = archMatrixInclN (Fin 3) ℚ (realM e) := rfl

theorem realM_mul (e f : Matrix (Fin 3) (Fin 3) ℝ) : realM (e * f) = realM e * realM f := Matrix.map_mul

theorem isUnit_archRealMat3 (e : E33) (h : (Matrix.of e).det ≠ 0) : IsUnit (WhittakerBlock.archRealMat3 e) := by
  rw [archRealMat3_eq]
  have h0 : IsUnit (Matrix.of e) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h)
  exact (h0.map (RingHom.mapMatrix ofRealHom)).map (archMatrixInclHomN (Fin 3) ℚ)

theorem val_lift (e : E33) (h : (Matrix.of e).det ≠ 0) :
    ((WhittakerBlock.archRealLift3 e : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      WhittakerBlock.archRealMat3 e := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_pos (isUnit_archRealMat3 e h)]
  exact IsUnit.unit_spec _

theorem lift_mul (e f : Matrix (Fin 3) (Fin 3) ℝ) (he : e.det ≠ 0) (hf : f.det ≠ 0) :
    WhittakerBlock.archRealLift3 (e * f) = WhittakerBlock.archRealLift3 e * WhittakerBlock.archRealLift3 f := by
  have hef : (Matrix.of (e * f)).det ≠ 0 := by
    change (e * f).det ≠ 0
    rw [Matrix.det_mul]; exact mul_ne_zero he hf
  refine Units.ext ?_
  rw [Units.val_mul, val_lift _ hef, val_lift _ he, val_lift _ hf, archRealMat3_eq, archRealMat3_eq,
    archRealMat3_eq, ← archMatrixInclN_mul, ← realM_mul]

theorem lift_mul' {m m' : E33} (hm : (Matrix.of m).det ≠ 0) (hm' : (Matrix.of m').det ≠ 0) :
    WhittakerBlock.archRealLift3 m * WhittakerBlock.archRealLift3 m' =
      WhittakerBlock.archRealLift3 (fun a b => (Matrix.of m * Matrix.of m') a b) :=
  (lift_mul (Matrix.of m) (Matrix.of m') hm hm').symm

theorem lift_mul_comm_of_archComponent3_eq_one (f : E33) (h : (Matrix.of f).det ≠ 0)
    (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ) (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1) :
    WhittakerBlock.archRealLift3 f * k₁ = k₁ * WhittakerBlock.archRealLift3 f := by
  have hK : ∀ l j : Fin 3, AdelicLevel.adeleArch (𝓞 ℚ) ℚ ((k₁ : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) l j) =
      (1 : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) l j := fun l j =>
    congrArg (fun u : GL (Fin 3) (InfiniteAdeleRing ℚ) => (u : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) l j) hk₁
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, val_lift f h, archRealMat3_eq]
  ext i j
  refine Prod.ext ?_ ?_
  · change AdelicLevel.adeleArch (𝓞 ℚ) ℚ ((archMatrixInclN (Fin 3) ℚ (realM (Matrix.of f)) * (k₁ : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) i j) =
      AdelicLevel.adeleArch (𝓞 ℚ) ℚ (((k₁ : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) * archMatrixInclN (Fin 3) ℚ (realM (Matrix.of f))) i j)
    simp only [Matrix.mul_apply, map_sum, map_mul, adeleArch_archMatrixInclN, hK]
    rw [← Matrix.mul_apply, ← Matrix.mul_apply, Matrix.mul_one, Matrix.one_mul]
  · change AdelicLevel.adeleFin (𝓞 ℚ) ℚ ((archMatrixInclN (Fin 3) ℚ (realM (Matrix.of f)) * (k₁ : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) i j) =
      AdelicLevel.adeleFin (𝓞 ℚ) ℚ (((k₁ : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) * archMatrixInclN (Fin 3) ℚ (realM (Matrix.of f))) i j)
    simp only [Matrix.mul_apply, map_sum, map_mul, adeleFin_archMatrixInclN]
    simp [Matrix.one_apply]

def invLocus : Set E33 := {m | (Matrix.of m).det ≠ 0}

theorem isOpen_invLocus : IsOpen invLocus := by
  have hc : Continuous fun e : E33 => (Matrix.of e).det :=
    (continuous_id : Continuous fun e : E33 => (Matrix.of e : Matrix (Fin 3) (Fin 3) ℝ)).matrix_det
  exact isOpen_ne_fun hc continuous_const

def dirE (i j : Fin 3) (s : ℝ) : E33 :=
  fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0

def idE : E33 := fun a b => if a = b then 1 else 0
def stdE (i j : Fin 3) : E33 := fun a b => if a = i ∧ b = j then 1 else 0

theorem dirE_eq (i j : Fin 3) (s : ℝ) : dirE i j s = idE + s • stdE i j := by
  funext a b
  simp only [dirE, idE, stdE, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

theorem of_idE : Matrix.of idE = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext a b; rw [Matrix.of_apply, idE, Matrix.one_apply]

theorem of_dirE (i j : Fin 3) (s : ℝ) : Matrix.of (dirE i j s) = 1 + s • Matrix.single i j (1 : ℝ) := by
  ext a b
  simp only [dirE, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  congr 1
  by_cases h : a = i ∧ b = j
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
  · rw [if_neg h, if_neg fun h' => h ⟨h'.1.symm, h'.2.symm⟩]

theorem continuous_dirE (i j : Fin 3) : Continuous (dirE i j) := by
  have : dirE i j = fun s => idE + s • stdE i j := funext (dirE_eq i j)
  rw [this]
  exact continuous_const.add (continuous_id.smul continuous_const)

theorem eventually_dirE_mem_invLocus (i j : Fin 3) : ∀ᶠ s in 𝓝 (0 : ℝ), dirE i j s ∈ invLocus := by
  have hc : Continuous fun s : ℝ => (Matrix.of (dirE i j s)).det :=
    ((continuous_dirE i j : Continuous fun s => (Matrix.of (dirE i j s) : Matrix (Fin 3) (Fin 3) ℝ))).matrix_det
  have h0 : (Matrix.of (dirE i j 0)).det ≠ 0 := by
    rw [dirE_eq, zero_smul, add_zero, of_idE, Matrix.det_one]
    exact one_ne_zero
  exact hc.continuousAt.eventually_ne h0

def colDir (i j : Fin 3) (m : E33) : E33 := fun a b => if b = j then m a i else 0

theorem of_mul_of_dirE (i j : Fin 3) (t : ℝ) (m : E33) :
    (fun a b => (Matrix.of m * Matrix.of (dirE i j t)) a b) = m + t • colDir i j m := by
  funext a b
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, colDir]
  rw [of_dirE, mul_add, mul_one, Matrix.add_apply, Matrix.of_apply, Matrix.mul_smul, Matrix.smul_apply,
    smul_eq_mul]
  congr 1
  by_cases hb : b = j
  · subst hb
    rw [Matrix.mul_single_apply_same, mul_one, if_pos rfl, Matrix.of_apply]
  · rw [Matrix.mul_single_apply_of_ne (hbj := hb), if_neg hb]

theorem eventually_add_smul_mem_invLocus {o : E33} (ho : o ∈ invLocus) (W : E33) :
    ∀ᶠ s in 𝓝 (0 : ℝ), o + s • W ∈ invLocus := by
  have hc : Continuous fun s : ℝ => o + s • W := continuous_const.add (continuous_id.smul continuous_const)
  have : (fun s : ℝ => o + s • W) 0 ∈ invLocus := by simpa using ho
  exact hc.continuousAt.eventually_mem (isOpen_invLocus.mem_nhds this)

def sg (s : Fin 2) : ℝ := (-1 : ℝ) ^ (s : ℕ)

theorem sg_mul_self (s : Fin 2) : sg s * sg s = 1 := by
  unfold sg; fin_cases s <;> simp

theorem sg_ne_zero (s : Fin 2) : sg s ≠ 0 := by
  unfold sg; exact pow_ne_zero _ (by norm_num)

theorem sg_add (s t : Fin 2) : sg (s + t) = sg s * sg t := by
  unfold sg; fin_cases s <;> fin_cases t <;> simp <;> decide

def msig (σ : Fin 3 → Fin 2) : E33 := fun a b => if a = b then (-1 : ℝ) ^ (σ a : ℕ) else 0

theorem msig_apply (σ : Fin 3 → Fin 2) (a b : Fin 3) : msig σ a b = if a = b then sg (σ a) else 0 := rfl

theorem det_msig (σ : Fin 3 → Fin 2) : (Matrix.of (msig σ)).det ≠ 0 := by
  rw [Matrix.det_fin_three]
  simp [msig_apply, sg_ne_zero]

theorem msig_mul_msig (σ τ : Fin 3 → Fin 2) :
    (fun a b => (Matrix.of (msig σ) * Matrix.of (msig τ)) a b) = msig (σ + τ) := by
  funext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply, msig_apply, Pi.add_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  split_ifs with h
  · subst h; rw [sg_add]
  · simp

section WhittakerLinearity

open MeasureTheory

theorem continuous_upperUnipotent3 {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous fun p : A × A × A => upperUnipotent3 p.1 p.2.1 p.2.2 := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun p : A × A × A =>
      (Matrix.of ![![1, p.1, p.2.2], ![0, 1, p.2.1], ![0, 0, 1]] : Matrix (Fin 3) (Fin 3) A)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun p : A × A × A =>
      (Matrix.of ![![1, -p.1, p.1 * p.2.1 - p.2.2], ![0, 1, -p.2.1], ![0, 0, 1]] : Matrix (Fin 3) (Fin 3) A)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem isProbabilityMeasure_productionPins_ν :
    @IsProbabilityMeasure _ (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS
      (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν :=
  isProbabilityMeasure_productionPinsOf_ν ℚ _ _ _ _ (AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne'
    (AdelicBox.adelicAddHaar_adelicBox_lt_top ℚ).ne

theorem borelSpace_productionPins_nS :
    @BorelSpace (AdeleRing (𝓞 ℚ) ℚ) _
      (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS := by
  rw [productionPinsOf_nS]
  exact AdelicHaar.borelSpace_adeleBorel _ _

theorem ae_mem_adelicBox_productionPins_ν :
    ∀ᵐ a ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν,
      a ∈ AdelicBox.adelicBox ℚ := by
  rw [productionPinsOf_ν]
  unfold ProbabilityTheory.cond
  exact MeasureTheory.Measure.ae_smul_measure (ae_restrict_mem (AdelicBox.measurableSet_adelicBox ℚ)) _

theorem continuous_integral_of_continuous {β : Type*} [TopologicalSpace β] {α : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [OpensMeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (C : Set α)
    (hC : IsCompact C) (hae : ∀ᵐ a ∂μ, a ∈ C) (H : β → α → ℂ) (hH : Continuous fun q : β × α => H q.1 q.2) :
    Continuous fun b => ∫ a, H b a ∂μ := by
  have hslice : ∀ b : β, Continuous fun a => H b a := fun b => hH.comp (Continuous.prodMk_right b)
  have hint : ∀ b : β, Integrable (fun a => H b a) μ := by
    intro b
    obtain ⟨Mb, hMb⟩ := hC.exists_bound_of_continuousOn (hslice b).continuousOn
    exact Integrable.of_bound (hslice b).aestronglyMeasurable Mb (hae.mono fun a ha => hMb a ha)
  refine continuous_iff_continuousAt.mpr fun b₀ => ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hH₀ : Continuous fun q : β × α => H b₀ q.2 :=
    hH.comp ((continuous_const : Continuous fun _ : β × α => b₀).prodMk continuous_snd)
  have hdist : Continuous fun q : β × α => ‖H q.1 q.2 - H b₀ q.2‖ := (hH.sub hH₀).norm
  have htube : ∀ᶠ b in nhds b₀, ∀ a ∈ C, ‖H b a - H b₀ a‖ < ε / 2 := by
    refine hC.eventually_forall_of_forall_eventually fun a _ => ?_
    refine hdist.continuousAt.eventually_lt continuous_const.continuousAt ?_
    show ‖H b₀ a - H b₀ a‖ < ε / 2
    rw [sub_self, norm_zero]
    exact half_pos hε
  refine htube.mono fun b hb => ?_
  rw [dist_eq_norm, ← integral_sub (hint b) (hint b₀)]
  have hbound : ∀ᵐ a ∂μ, ‖H b a - H b₀ a‖ ≤ ε / 2 := hae.mono fun a ha => (hb a ha).le
  calc ‖∫ a, H b a - H b₀ a ∂μ‖ ≤ ε / 2 * μ.real Set.univ := norm_integral_le_of_norm_le_const hbound
    _ = ε / 2 := by simp
    _ < ε := half_lt_self hε

theorem integrable_of_continuous_of_ae_mem_compact {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (C : Set α) (hC : IsCompact C)
    (hae : ∀ᵐ a ∂μ, a ∈ C) (K : α → ℂ) (hK : Continuous K) : Integrable K μ := by
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hK.continuousOn
  exact Integrable.of_bound hK.aestronglyMeasurable M (hae.mono fun a ha => hM a ha)

theorem integral3_sum_of_continuous {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (C : Set α) (hC : IsCompact C)
    (hae : ∀ᵐ a ∂μ, a ∈ C) {ι : Type*} [Fintype ι] (c : ι → ℂ) (G : ι → α → α → α → ℂ)
    (hG : ∀ i, Continuous fun p : α × α × α => G i p.1 p.2.1 p.2.2) :
    (∫ x, ∫ y, ∫ z, ∑ i, c i * G i x y z ∂μ ∂μ ∂μ) = ∑ i, c i * ∫ x, ∫ y, ∫ z, G i x y z ∂μ ∂μ ∂μ := by
  have key : ∀ K : ι → α → ℂ, (∀ i, Continuous (K i)) →
      (∫ a, ∑ i, c i * K i a ∂μ) = ∑ i, c i * ∫ a, K i a ∂μ := by
    intro K hK
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]
    · intro i _
      exact (integrable_of_continuous_of_ae_mem_compact μ C hC hae (K i) (hK i)).const_mul (c i)
  have hz : ∀ i x y, Continuous fun z => G i x y z := fun i x y =>
    (hG i).comp ((Continuous.prodMk_right x).comp (Continuous.prodMk_right y))
  have hI : ∀ i, Continuous fun p : α × α => ∫ z, G i p.1 p.2 z ∂μ := fun i =>
    continuous_integral_of_continuous μ C hC hae (fun (p : α × α) z => G i p.1 p.2 z)
      ((hG i).comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd)))
  have hJ : ∀ i, Continuous fun x => ∫ y, ∫ z, G i x y z ∂μ ∂μ := fun i =>
    continuous_integral_of_continuous μ C hC hae (fun x y => ∫ z, G i x y z ∂μ) (hI i)
  have h1 : ∀ x y, (∫ z, ∑ i, c i * G i x y z ∂μ) = ∑ i, c i * ∫ z, G i x y z ∂μ := fun x y =>
    key (fun i z => G i x y z) fun i => hz i x y
  have h2 : ∀ x, (∫ y, ∑ i, c i * ∫ z, G i x y z ∂μ ∂μ) = ∑ i, c i * ∫ y, ∫ z, G i x y z ∂μ ∂μ := fun x =>
    key (fun i y => ∫ z, G i x y z ∂μ) fun i => (hI i).comp (Continuous.prodMk_right x)
  simp_rw [h1, h2]
  exact key (fun i x => ∫ y, ∫ z, G i x y z ∂μ ∂μ) hJ

theorem whittaker3_sum_mul_of_continuous {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (F : ι → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : ∀ i, Continuous (F i)) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ (fun x => ∑ i, c i * F i x) g =
      ∑ i, c i *
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ (F i) g := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) :=
    (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).nS
  haveI := borelSpace_productionPins_nS
  haveI := isProbabilityMeasure_productionPins_ν
  obtain ⟨C, hC, hBC⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  have hae : ∀ᵐ a ∂(productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)).ν, a ∈ C :=
    ae_mem_adelicBox_productionPins_ν.mono fun a ha => hBC ha
  have hG : ∀ i, Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      F i (upperUnipotent3 p.1 p.2.1 p.2.2 * g) * NumberField.StandardAddChar.psiQ (-(p.1 + p.2.1)) := fun i =>
    ((hF i).comp ((continuous_upperUnipotent3 (A := AdeleRing (𝓞 ℚ) ℚ)).mul continuous_const)).mul
      (NumberField.StandardAddChar.continuous_psiQ.comp ((continuous_fst.add continuous_snd.fst).neg))
  unfold whittaker3
  simp_rw [Finset.sum_mul, mul_assoc]
  exact integral3_sum_of_continuous _ C hC hae c
    (fun i x y z => F i (upperUnipotent3 x y z * g) * NumberField.StandardAddChar.psiQ (-(x + y))) hG

end WhittakerLinearity

def Rt (k : G3) (φ : G3 → ℂ) : G3 → ℂ := fun g => φ (g * k)

theorem archDeriv_Rt (k₁ : G3) (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1) (c d : Fin 3) (φ : G3 → ℂ) :
    WhittakerBlock.archDeriv c d (Rt k₁ φ) = Rt k₁ (WhittakerBlock.archDeriv c d φ) := by
  funext g
  show deriv (fun s : ℝ => φ (g * WhittakerBlock.archRealLift3 (dirE c d s) * k₁)) 0 =
    deriv (fun s : ℝ => φ (g * k₁ * WhittakerBlock.archRealLift3 (dirE c d s))) 0
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [eventually_dirE_mem_invLocus c d] with s hs
  rw [mul_assoc, lift_mul_comm_of_archComponent3_eq_one _ hs k₁ hk₁, ← mul_assoc]

theorem foldr_Rt (k₁ : G3) (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1) (φ : G3 → ℂ) (wd : List (Fin 3 × Fin 3)) :
    List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) (Rt k₁ φ) wd =
      Rt k₁ (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) φ wd) := by
  induction wd with
  | nil => rfl
  | cons ij wd ih => simp only [List.foldr_cons, ih, archDeriv_Rt k₁ hk₁]

theorem isArchSmooth3_Rt (k₁ : G3) (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1) (φ : G3 → ℂ)
    (h : WhittakerBlock.IsArchSmooth3 φ) : WhittakerBlock.IsArchSmooth3 (Rt k₁ φ) := by
  intro g
  have := h (g * k₁)
  refine this.congr (fun e he => ?_)
  show φ (g * WhittakerBlock.archRealLift3 e * k₁) = φ (g * k₁ * WhittakerBlock.archRealLift3 e)
  rw [mul_assoc, lift_mul_comm_of_archComponent3_eq_one _ he k₁ hk₁, ← mul_assoc]

theorem continuous_Rt (k : G3) (φ : G3 → ℂ) (h : Continuous φ) : Continuous (Rt k φ) :=
  h.comp (continuous_mul_right k)

theorem whittaker3_Rt (k : G3) (φ : G3 → ℂ) (g : G3) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ (Rt k φ) g =
      whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ φ (g * k) := by
  simp only [whittaker3, Rt, mul_assoc]

theorem eq_C_of_isHomogeneous_zero (p : R3) (hp : p.IsHomogeneous 0) : p = MvPolynomial.C (p.coeff 0) :=
  MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp ((MvPolynomial.totalDegree_zero_iff_isHomogeneous _).mpr hp)

theorem exists_linear_of_isHomogeneous_one (p : R3) (hp : p.IsHomogeneous 1) :
    ∃ c : Fin 3 → ℂ, p = ∑ a : Fin 3, MvPolynomial.X a * MvPolynomial.C (c a) := by
  refine ⟨fun a => (MvPolynomial.pderiv a p).coeff 0, ?_⟩
  have hE := hp.sum_X_mul_pderiv
  have hc : ∀ a : Fin 3, MvPolynomial.pderiv a p = MvPolynomial.C ((MvPolynomial.pderiv a p).coeff 0) :=
    fun a => eq_C_of_isHomogeneous_zero _ (by simpa using (hp.pderiv (i := a)))
  calc p = (1 : ℕ) • p := by simp
    _ = ∑ a : Fin 3, MvPolynomial.X a * MvPolynomial.pderiv a p := hE.symm
    _ = _ := Finset.sum_congr rfl (fun a _ => by rw [← hc a])

def unitInf (e : Matrix (Fin 3) (Fin 3) ℝ) (h : e.det ≠ 0) : GL (Fin 3) (InfiniteAdeleRing ℚ) :=
  Matrix.GeneralLinearGroup.map ofRealHom (e.nonsingInvUnit (isUnit_iff_ne_zero.mpr h))

theorem lift_eq_archInclN (e : E33) (h : (Matrix.of e).det ≠ 0) :
    WhittakerBlock.archRealLift3 e = archInclN (Fin 3) ℚ (unitInf (Matrix.of e) h) := by
  refine Units.ext ?_
  rw [val_lift e h]
  rfl

theorem componentAt3_lift (f : E33) (h : (Matrix.of f).det ≠ 0) (q : HeightOneSpectrum (𝓞 ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ q (WhittakerBlock.archRealLift3 f) = 1 := by
  rw [lift_eq_archInclN f h]
  exact componentAtN_archInclN (Fin 3) ℚ q _

theorem colOrth_iff (o : E33) :
    (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) ↔ (Matrix.of o).transpose * Matrix.of o = 1 := by
  constructor
  · intro h; ext i j; rw [Matrix.mul_apply, Matrix.one_apply]; simpa [Matrix.transpose_apply] using h i j
  · intro h i j
    have := congrFun (congrFun h i) j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using this

theorem archComponent3_lift_mem_orth3 (f : E33) (h : (Matrix.of f).det ≠ 0)
    (horth : (Matrix.of f).transpose * Matrix.of f = 1) :
    archComponent3 (𝓞 ℚ) ℚ (WhittakerBlock.archRealLift3 f) ∈ orth3 := by
  rw [lift_eq_archInclN f h]
  change archComponentN (Fin 3) (𝓞 ℚ) ℚ (archInclN (Fin 3) ℚ (unitInf (Matrix.of f) h)) ∈ orth3
  rw [archComponentN_archInclN]
  change (realM (Matrix.of f)).transpose * realM (Matrix.of f) = 1
  rw [realM, ← Matrix.transpose_map, ← Matrix.map_mul, horth, Matrix.map_one ofRealHom (map_zero _) (map_one _)]

theorem det_ne_zero_of_colOrth (o : E33)
    (ho : ∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) : (Matrix.of o).det ≠ 0 := by
  have h1 := congrArg Matrix.det ((colOrth_iff o).mp ho)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
  intro h0; rw [h0, mul_zero] at h1; exact zero_ne_one h1

theorem colOrth_mul (o r : E33)
    (ho : ∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0)
    (hr : ∀ i j : Fin 3, ∑ a : Fin 3, r a i * r a j = if i = j then 1 else 0) :
    ∀ i j : Fin 3, ∑ a : Fin 3, (fun a b => (Matrix.of o * Matrix.of r) a b) a i *
      (fun a b => (Matrix.of o * Matrix.of r) a b) a j = if i = j then 1 else 0 := by
  rw [colOrth_iff] at ho hr ⊢
  show (Matrix.of o * Matrix.of r).transpose * (Matrix.of o * Matrix.of r) = 1
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.of o).transpose, ho, Matrix.one_mul, hr]

theorem msig_colOrth (τ : Fin 3 → Fin 2) :
    ∀ i j : Fin 3, ∑ a : Fin 3, msig τ a i * msig τ a j = if i = j then 1 else 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [msig_apply, Fin.sum_univ_three, sg_mul_self]

def chi (ε τ : Fin 3 → Fin 2) : ℂ := (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ))

def piF (ε : Fin 3 → Fin 2) (F : G3 → ℂ) : G3 → ℂ :=
  fun g => (1 / 8 : ℂ) * ∑ τ : Fin 3 → Fin 2, chi ε τ * F (WhittakerBlock.archRealLift3 (msig τ) * g)

def pt (o : E33) : Fin 3 × Fin 3 → ℂ := fun ij => ((o ij.1 ij.2 : ℝ) : ℂ)

def ColOrth (o : E33) : Prop := ∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0

def Reads (ε : Fin 3 → Fin 2) (k₁ : G3) (F : G3 → ℂ) (P : R9) : Prop :=
  ∀ o : E33, ColOrth o → piF ε F (WhittakerBlock.archRealLift3 o * k₁) = MvPolynomial.eval (pt o) P

def act (ν : Fin 3 → ℂ) (c d : Fin 3) (p : R9) : R9 :=
  (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
      (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
  ∑ i : Fin 3, ∑ j : Fin 3,
    (∑ m : Fin 3,
      (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
        else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
        else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
      MvPolynomial.pderiv (i, j) p

theorem piF_add (ε : Fin 3 → Fin 2) (F G : G3 → ℂ) (g : G3) : piF ε (F + G) g = piF ε F g + piF ε G g := by
  simp only [piF, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem piF_sub (ε : Fin 3 → Fin 2) (F G : G3 → ℂ) (g : G3) : piF ε (F - G) g = piF ε F g - piF ε G g := by
  simp only [piF, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem piF_smul (ε : Fin 3 → Fin 2) (c : ℂ) (F : G3 → ℂ) (g : G3) : piF ε (c • F) g = c * piF ε F g := by
  simp only [piF, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun τ _ => by ring)

theorem reads_archDeriv (ν : Fin 3 → ℂ) (M : Submodule ℂ (G3 → ℂ))
    (h5 : ∀ w ∈ M, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M)
    (Λ : ↥M →ₗ[ℂ] (G3 → ℂ))
    (hΛc : ∀ (v : G3 → ℂ) (hv : v ∈ M) (c d : Fin 3) (g : G3),
        HasDerivAt
          (fun s : ℝ => Λ ⟨v, hv⟩ (g * WhittakerBlock.archRealLift3 fun a b =>
            (if a = b then (1 : ℝ) else 0) + if a = c ∧ b = d then s else 0))
          (Λ ⟨WhittakerBlock.archDeriv c d v, h5 v hv c d⟩ g) 0)
    (ε : Fin 3 → Fin 2) (k₁ : G3) (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1)
    (u : G3 → ℂ) (hu : u ∈ M)
    (heq : ∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : G3, Λ ⟨u, hu⟩ (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * Λ ⟨u, hu⟩ g)
    (P : R9) (hP : Reads ε k₁ (Λ ⟨u, hu⟩) P) (c d : Fin 3) :
    Reads ε k₁ (Λ ⟨WhittakerBlock.archDeriv c d u, h5 u hu c d⟩) (act ν c d P) := by
  intro o ho

  have hpi := (LanglandsTunnell.CubicInduction.upperTriangular_equivariant_and_signIsotypic_signProjection
    ν ε (Λ ⟨u, hu⟩) heq).1

  have hind := LanglandsTunnell.CubicInduction.hasDerivAt_archFlow_eq_eval_inducedPicture_act_of_upperTriangular_equivariant
    ν (piF ε (Λ ⟨u, hu⟩)) hpi k₁ hk₁ P (fun o' ho' => hP o' ho') o ho c d

  have hcurve : HasDerivAt
      (fun s : ℝ => piF ε (Λ ⟨u, hu⟩) (WhittakerBlock.archRealLift3 o * k₁ *
        WhittakerBlock.archRealLift3 fun a b => (if a = b then (1 : ℝ) else 0) + if a = c ∧ b = d then s else 0))
      (piF ε (Λ ⟨WhittakerBlock.archDeriv c d u, h5 u hu c d⟩) (WhittakerBlock.archRealLift3 o * k₁)) 0 := by
    unfold piF
    have hτ : ∀ τ : Fin 3 → Fin 2, HasDerivAt
        (fun s : ℝ => chi ε τ * Λ ⟨u, hu⟩ (WhittakerBlock.archRealLift3 (msig τ) *
          (WhittakerBlock.archRealLift3 o * k₁ *
            WhittakerBlock.archRealLift3 fun a b => (if a = b then (1 : ℝ) else 0) + if a = c ∧ b = d then s else 0)))
        (chi ε τ * Λ ⟨WhittakerBlock.archDeriv c d u, h5 u hu c d⟩
          (WhittakerBlock.archRealLift3 (msig τ) * (WhittakerBlock.archRealLift3 o * k₁))) 0 := by
      intro τ
      have h := (hΛc u hu c d (WhittakerBlock.archRealLift3 (msig τ) * (WhittakerBlock.archRealLift3 o * k₁))).const_mul (chi ε τ)
      simp only [mul_assoc] at h ⊢
      exact h
    have hs := HasDerivAt.sum (u := Finset.univ) (fun τ (_ : τ ∈ Finset.univ) => hτ τ)
    have hs' := hs.const_mul (1 / 8 : ℂ)
    convert hs' using 2
    all_goals first | (ext s; simp only [Finset.sum_apply]) | simp only [Finset.sum_apply] | rfl
  have := hcurve.unique hind
  rw [this]
  rfl

def detC (o : E33) : ℂ := (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det

theorem detC_eq (o : E33) : detC o = (((Matrix.of o).det : ℝ) : ℂ) := by
  unfold detC
  have : (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)) = (Complex.ofRealHom : ℝ →+* ℂ).mapMatrix (Matrix.of o) := rfl
  rw [this, ← RingHom.map_det]; rfl

theorem detC_mul (o r : E33) : detC (fun a b => (Matrix.of o * Matrix.of r) a b) = detC o * detC r := by
  rw [detC_eq, detC_eq, detC_eq]
  change ((((Matrix.of o * Matrix.of r)).det : ℝ) : ℂ) = _
  rw [Matrix.det_mul]; push_cast; rfl

theorem detC_ne_zero (o : E33) (ho : ColOrth o) : detC o ≠ 0 := by
  rw [detC_eq]; exact_mod_cast det_ne_zero_of_colOrth o ho

def detX : R9 := (Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : R9)).det

theorem eval_detX (o : E33) : MvPolynomial.eval (pt o) detX = detC o := by
  unfold detX detC
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [pt]

open MvPolynomial in
theorem act_add (ν : Fin 3 → ℂ) (c d : Fin 3) (P Q : R9) : act ν c d (P + Q) = act ν c d P + act ν c d Q := by
  simp only [act, mul_add, map_add, Finset.sum_add_distrib]
  ring

open MvPolynomial in
theorem act_C_mul (ν : Fin 3 → ℂ) (c d : Fin 3) (r : ℂ) (P : R9) : act ν c d (C r * P) = C r * act ν c d P := by
  simp only [act, Derivation.leibniz, MvPolynomial.pderiv_C, smul_zero, add_zero, smul_eq_mul, mul_add,
    Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_)); ring

theorem act_detX_mul (ν : Fin 3 → ℂ) (c d : Fin 3) (P : R9) : act ν c d (detX * P) = detX * act ν c d P :=
  LanglandsTunnell.CubicInduction.inducedPicture_act_det_mul ν c d P

theorem act_detX_pow_mul (ν : Fin 3 → ℂ) (c d : Fin 3) (n : ℕ) (P : R9) :
    act ν c d (detX ^ n * P) = detX ^ n * act ν c d P := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_comm (detX ^ n) detX, mul_assoc, act_detX_mul, ih, ← mul_assoc]

def dl (ν : Fin 3 → ℂ) (c' : ℂ) (f : R9) : R9 :=
  act ν 0 1 (act ν 1 2 f) - act ν 0 2 (act ν 1 1 f) - MvPolynomial.C c' * act ν 0 2 f

theorem dl_add (ν : Fin 3 → ℂ) (c' : ℂ) (f g : R9) : dl ν c' (f + g) = dl ν c' f + dl ν c' g := by
  simp only [dl, act_add]; ring

theorem dl_C_mul (ν : Fin 3 → ℂ) (c' : ℂ) (r : ℂ) (f : R9) : dl ν c' (MvPolynomial.C r * f) = MvPolynomial.C r * dl ν c' f := by
  simp only [dl, act_C_mul]; ring

theorem dl_detX_pow_mul (ν : Fin 3 → ℂ) (c' : ℂ) (n : ℕ) (f : R9) :
    dl ν c' (detX ^ n * f) = detX ^ n * dl ν c' f := by
  simp only [dl, act_detX_pow_mul]; ring

def perm (a : Fin 3) : E33 := fun i j =>
  if (i = a ∧ j = 0) ∨ (i = 0 ∧ j = a) ∨ (i = j ∧ i ≠ 0 ∧ i ≠ a) then 1 else 0

theorem perm_colOrth (a : Fin 3) : ColOrth (perm a) := by
  intro i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;> simp [perm, Fin.sum_univ_three]

theorem perm_col0 (a b : Fin 3) : perm a b 0 = if b = a then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> simp [perm]

theorem rowOrth_cast (o : E33) (ho : ColOrth o) (r s : Fin 3) :
    (∑ a : Fin 3, pt o (r, a) * pt o (s, a)) = if r = s then 1 else 0 := by
  have h1 : (Matrix.of o).transpose * Matrix.of o = 1 := (colOrth_iff o).mp ho
  have h2 : Matrix.of o * (Matrix.of o).transpose = 1 := mul_eq_one_comm.mp h1
  have h3 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => ((M r s : ℝ) : ℂ)) h2
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply] at h3
  push_cast at h3
  simp only [pt]
  rw [h3]
  split_ifs <;> simp

def realise0 (p : R3) : R9 :=
  MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p

theorem eval_realise0 (x : Fin 3 × Fin 3 → ℂ) (q : R3) :
    MvPolynomial.eval x (realise0 q) = MvPolynomial.eval (fun a => x (a, 0)) q := by
  have h := congrArg (fun φ : R3 →ₐ[ℂ] ℂ => φ q)
    (MvPolynomial.comp_aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : R9)) (MvPolynomial.aeval (R := ℂ) x))
  have h' : MvPolynomial.eval x (realise0 q) = MvPolynomial.eval (fun a => MvPolynomial.aeval x (MvPolynomial.X (a, 0) : R9)) q := h
  rw [h']
  exact congrArg (fun f : Fin 3 → ℂ => MvPolynomial.eval f q) (funext fun a => by simp)

theorem fin2_cases (v : Fin 2) : v = 0 ∨ v = 1 := by fin_cases v <;> simp

theorem msig_single_det (a : Fin 3) :
    (Matrix.of (msig (fun b : Fin 3 => if b = a then (1 : Fin 2) else 0))).det = -1 := by
  rw [Matrix.det_fin_three]
  fin_cases a <;> simp [msig_apply, sg]

theorem lift_msig_mul (τ : Fin 3 → Fin 2) (o : E33) (ho : ColOrth o) :
    WhittakerBlock.archRealLift3 (msig τ) * WhittakerBlock.archRealLift3 o =
      WhittakerBlock.archRealLift3 (fun a b => (Matrix.of (msig τ) * Matrix.of o) a b) :=
  lift_mul' (det_msig τ) (det_ne_zero_of_colOrth o ho)

theorem msig_mul_col0 (τ : Fin 3 → Fin 2) (o : E33) (b : Fin 3) :
    (Matrix.of (msig τ) * Matrix.of o) b 0 = sg (τ b) * o b 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply, msig_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem pin (ε : Fin 3 → Fin 2) (k₁ : G3) (F : G3 → ℂ)
    (hiso : ∀ (τ : Fin 3 → Fin 2) (g : G3), piF ε F (WhittakerBlock.archRealLift3 (msig τ) * g) = chi ε τ * piF ε F g)
    (α : ℕ) (c : Fin 3 → ℂ)
    (hread : ∀ o : E33, ColOrth o → piF ε F (WhittakerBlock.archRealLift3 o * k₁) =
      detC o ^ α * ∑ b : Fin 3, ((o b 0 : ℝ) : ℂ) * c b)
    (a : Fin 3) (hpar : (-1 : ℂ) ^ (α + 1) ≠ (-1 : ℂ) ^ (ε a : ℕ)) : c a = 0 := by
  classical
  set τ : Fin 3 → Fin 2 := fun b => if b = a then 1 else 0 with hτ
  set mo : E33 := fun i j => (Matrix.of (msig τ) * Matrix.of (perm a)) i j with hmo
  have hmo_orth : ColOrth mo := colOrth_mul _ _ (msig_colOrth τ) (perm_colOrth a)
  have h1 := hread mo hmo_orth
  have h2 := hread (perm a) (perm_colOrth a)
  have h3 := hiso τ (WhittakerBlock.archRealLift3 (perm a) * k₁)
  rw [← mul_assoc, lift_msig_mul τ (perm a) (perm_colOrth a)] at h3
  change piF ε F (WhittakerBlock.archRealLift3 mo * k₁) = _ at h3
  rw [h1, h2] at h3

  have hcol : ∀ b : Fin 3, ((mo b 0 : ℝ) : ℂ) = ((sg (τ b) : ℝ) : ℂ) * ((perm a b 0 : ℝ) : ℂ) := by
    intro b; rw [hmo]; simp only [msig_mul_col0]; push_cast; ring
  have hsum1 : (∑ b : Fin 3, ((mo b 0 : ℝ) : ℂ) * c b) = - c a := by
    simp only [hcol, perm_col0]
    simp [hτ, sg, Finset.sum_ite_eq', apply_ite]
  have hsum2 : (∑ b : Fin 3, ((perm a b 0 : ℝ) : ℂ) * c b) = c a := by
    rw [Finset.sum_eq_single a]
    · simp [perm_col0]
    · intro b _ hb; simp [perm_col0, hb]
    · intro h; exact absurd (Finset.mem_univ a) h
  have hdet : detC mo = -detC (perm a) := by
    rw [hmo, detC_mul, detC_eq (msig τ), hτ, msig_single_det]; push_cast; ring
  have hchi : chi ε τ = (-1 : ℂ) ^ (ε a : ℕ) := by
    simp only [chi, hτ]
    congr 1
    simp [Finset.sum_ite_eq', apply_ite]
  rw [hsum1, hsum2, hdet, hchi, neg_pow] at h3

  have hd : detC (perm a) ^ α ≠ 0 := pow_ne_zero _ (detC_ne_zero _ (perm_colOrth a))
  have : c a * (detC (perm a) ^ α * ((-1 : ℂ) ^ (α + 1) - (-1 : ℂ) ^ (ε a : ℕ))) = 0 := by
    rw [pow_succ]; linear_combination h3
  rcases mul_eq_zero.mp this with h | h
  · exact h
  · rcases mul_eq_zero.mp h with h | h
    · exact absurd h hd
    · exact absurd (sub_eq_zero.mp h) hpar

theorem whittaker_torus_eq_zero_of_minor_eq_zero
    (k₁ : G3) (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1)
    (w : G3 → ℂ) (hsm : WhittakerBlock.IsArchSmooth3 w)
    (hcont : ∀ wd : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) w wd))
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : G3), w (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = w g)
    (hsm11 : WhittakerBlock.IsArchSmooth3 (WhittakerBlock.archDeriv 1 1 w))
    (hcont11 : ∀ wd : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) (WhittakerBlock.archDeriv 1 1 w) wd))
    (haut11 : ∀ (γ : GL (Fin 3) ℚ) (g : G3), WhittakerBlock.archDeriv 1 1 w (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = WhittakerBlock.archDeriv 1 1 w g)
    (c' : ℂ)
    (hzero : ∀ g : G3, WhittakerBlock.archDeriv 0 1 (WhittakerBlock.archDeriv 1 2 w) g
        - WhittakerBlock.archDeriv 0 2 (WhittakerBlock.archDeriv 1 1 w) g - c' * WhittakerBlock.archDeriv 0 2 w g = 0)
    (y₁ y₂ : ℝ) (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) NumberField.StandardAddChar.psiQ w
      (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k₁) = 0 := by
  classical
  set φ : G3 → ℂ := Rt k₁ w with hφ
  set a : G3 := WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) with ha
  have hφsm : WhittakerBlock.IsArchSmooth3 φ := isArchSmooth3_Rt k₁ hk₁ w hsm
  have hφcont : ∀ wd : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) φ wd) := by
    intro wd; rw [hφ, foldr_Rt k₁ hk₁]; exact continuous_Rt k₁ _ (hcont wd)
  have hφaut : ∀ (γ : GL (Fin 3) ℚ) (g : G3), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g := by
    intro γ g; show w (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g * k₁) = w (g * k₁); rw [mul_assoc, haut]
  set φ11 : G3 → ℂ := Rt k₁ (WhittakerBlock.archDeriv 1 1 w) with hφ11
  have hφ11sm : WhittakerBlock.IsArchSmooth3 φ11 := isArchSmooth3_Rt k₁ hk₁ _ hsm11
  have hφ11cont : ∀ wd : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) φ11 wd) := by
    intro wd; rw [hφ11, foldr_Rt k₁ hk₁]; exact continuous_Rt k₁ _ (hcont11 wd)
  have hφ11aut : ∀ (γ : GL (Fin 3) ℚ) (g : G3), φ11 (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ11 g := by
    intro γ g; show WhittakerBlock.archDeriv 1 1 w (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g * k₁) = WhittakerBlock.archDeriv 1 1 w (g * k₁)
    rw [mul_assoc, haut11]
  obtain ⟨lam, hlam, hQ⟩ :=
    LanglandsTunnell.CubicInduction.exists_ne_zero_forall_whittaker3_archDeriv_archDeriv_diag_eq_mul_and_whittaker3_archDeriv_corner_eq_zero
  obtain ⟨hA, hB⟩ := hQ φ hφsm hφcont hφaut y₁ y₂ hy₁ hy₂
  obtain ⟨-, hC⟩ := hQ φ11 hφ11sm hφ11cont hφ11aut y₁ y₂ hy₁ hy₂
  have hφ11' : φ11 = WhittakerBlock.archDeriv 1 1 φ := by rw [hφ11, hφ, archDeriv_Rt k₁ hk₁]
  rw [hφ11'] at hC

  set Fv : Fin 3 → G3 → ℂ := ![WhittakerBlock.archDeriv 0 1 (WhittakerBlock.archDeriv 1 2 φ),
    WhittakerBlock.archDeriv 0 2 (WhittakerBlock.archDeriv 1 1 φ), WhittakerBlock.archDeriv 0 2 φ] with hFv
  set cv : Fin 3 → ℂ := ![1, -1, -c'] with hcv
  have hcomb0 : (fun x : G3 => ∑ i : Fin 3, cv i * Fv i x) = fun _ => (0 : ℂ) := by
    funext x
    simp only [hFv, hcv, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    have := hzero (x * k₁)
    have e1 : WhittakerBlock.archDeriv 0 1 (WhittakerBlock.archDeriv 1 2 φ) x =
        WhittakerBlock.archDeriv 0 1 (WhittakerBlock.archDeriv 1 2 w) (x * k₁) := by
      rw [hφ, archDeriv_Rt k₁ hk₁, archDeriv_Rt k₁ hk₁]; rfl
    have e2 : WhittakerBlock.archDeriv 0 2 (WhittakerBlock.archDeriv 1 1 φ) x =
        WhittakerBlock.archDeriv 0 2 (WhittakerBlock.archDeriv 1 1 w) (x * k₁) := by
      rw [hφ, archDeriv_Rt k₁ hk₁, archDeriv_Rt k₁ hk₁]; rfl
    have e3 : WhittakerBlock.archDeriv 0 2 φ x = WhittakerBlock.archDeriv 0 2 w (x * k₁) := by
      rw [hφ, archDeriv_Rt k₁ hk₁]; rfl
    rw [e1, e2, e3]; linear_combination this
  have hFc : ∀ i : Fin 3, Continuous (Fv i) := by
    intro i; fin_cases i
    · exact hφcont [(0, 1), (1, 2)]
    · exact hφcont [(0, 2), (1, 1)]
    · exact hφcont [(0, 2)]
  have hlin := whittaker3_sum_mul_of_continuous cv Fv hFc a
  rw [hcomb0] at hlin
  have hW0 : whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
      NumberField.StandardAddChar.psiQ (fun _ : G3 => (0 : ℂ)) a = 0 := by simp [whittaker3]
  rw [hW0] at hlin
  simp only [hFv, hcv, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at hlin
  rw [ha] at hlin
  rw [hA, hB, hC] at hlin
  have hWφ : whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
      NumberField.StandardAddChar.psiQ φ
      (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) = 0 := by
    have hy₁' : (y₁ : ℂ) ≠ 0 := by exact_mod_cast hy₁.ne'
    have hy₂' : (y₂ : ℂ) ≠ 0 := by exact_mod_cast hy₂.ne'
    have hne : lam ^ 2 * (y₁ : ℂ) * (y₂ : ℂ) ≠ 0 := mul_ne_zero (mul_ne_zero (pow_ne_zero _ hlam) hy₁') hy₂'
    have : lam ^ 2 * (y₁ : ℂ) * (y₂ : ℂ) * whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ φ
        (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0)) = 0 := by
      linear_combination -hlin
    exact (mul_eq_zero.mp this).resolve_left hne
  rw [hφ, whittaker3_Rt] at hWφ
  exact hWφ

end WsB.T2

namespace WsB
namespace T2

theorem positions (b₀ c₀ : Fin 3) (hb₀ : b₀ ≠ 0) (hc₀ : c₀ ≠ 0) (hbc : b₀ ≠ c₀) :
    (b₀ = 1 ∧ c₀ = 2) ∨ (b₀ = 2 ∧ c₀ = 1) := by
  fin_cases b₀ <;> fin_cases c₀ <;> simp_all

theorem parity_obstruction (ε : Fin 3 → Fin 2) (b₀ c₀ : Fin 3)
    (hcase : (b₀ = 1 ∧ c₀ = 2) ∨ (b₀ = 2 ∧ c₀ = 1))
    (hε1 : ε 0 = ε b₀) (hε2 : ε 0 ≠ ε c₀) (a : Fin 3) (ha : a ≠ c₀) :
    (-1 : ℂ) ^ ((1 + ∑ b : Fin 3, (ε b : ℕ)) % 2 + 1) ≠ (-1 : ℂ) ^ (ε a : ℕ) := by
  rcases hcase with ⟨hb, hc⟩ | ⟨hb, hc⟩ <;> subst hb hc <;>
    rcases fin2_cases (ε 0) with e0 | e0 <;> rcases fin2_cases (ε 1) with e1 | e1 <;>
    rcases fin2_cases (ε 2) with e2 | e2 <;> simp only [e0, e1, e2] at hε1 hε2 <;>
    fin_cases a <;> simp_all [Fin.sum_univ_three] <;> norm_num

end WsB.T2

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction
open WsB.T2 in
theorem solution
    (M : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (h1 :
      (∀ w ∈ M, WhittakerBlock.IsArchSmooth3 w ∧
        WhittakerBlock.IsArchSmooth3
          (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ w) ∧
        (∀ wd : List (Fin 3 × Fin 3),
          Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) w wd)) ∧
        ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), w (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = w g))
    (h3 :
      (∀ w ∈ M, ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))))
    (h4 :
      (∀ w ∈ M, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ M))
    (h5 : (∀ w ∈ M, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M))
    (h10 :
      (∃ B : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ℂ,
        (∀ w ∈ M, ∀ w' ∈ M, B w' w = (starRingEnd ℂ) (B w w')) ∧
        (∀ (z : ℂ), ∀ w₁ ∈ M, ∀ w₂ ∈ M, ∀ w' ∈ M, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w') ∧
        (∀ w ∈ M, w ≠ 0 → 0 < (B w w).re) ∧
        (∀ w ∈ M, ∀ w' ∈ M, ∀ i j : Fin 3,
          B (WhittakerBlock.archDeriv i j w) w' = - B w (WhittakerBlock.archDeriv i j w')) ∧
        ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            ∀ w ∈ M, ∀ w' ∈ M, B (fun g => w (g * k)) (fun g => w' (g * k)) = B w w'))
    (h11 :
      (∃ (N₁ N₂ N₃ : ℕ) (a₁ : Fin (N₁ + 1) → ℂ) (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ),
        a₁ (Fin.last N₁) = 1 ∧ a₂ (Fin.last N₂) = 1 ∧ a₃ (Fin.last N₃) = 1 ∧
        ∀ w ∈ M,
          (∑ l, a₁ l • (WhittakerBlock.casimir1^[l] w)) = 0 ∧
          (∑ l, a₂ l • (WhittakerBlock.casimir2^[l] w)) = 0 ∧
          (∑ l, a₃ l • (WhittakerBlock.casimir3^[l] w)) = 0))
    (h12 :
      (∀ v ∈ M, ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        v (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * v g))
    (h13 :
      (∀ v ∈ M, ∃ N : ℕ, ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) v w g‖ ≤ C * gauge3 ℚ g ^ N))
    (N₂ : ℕ) (a₂ : Fin (N₂ + 1) → ℂ) (ha₂ : a₂ (Fin.last N₂) = 1)
    (N₃ : ℕ) (a₃ : Fin (N₃ + 1) → ℂ) (ha₃ : a₃ (Fin.last N₃) = 1)
    (hrel : ∀ w ∈ M,
      (∑ l, a₂ l • (WhittakerBlock.casimir2^[l] w)) = 0 ∧ (∑ l, a₃ l • (WhittakerBlock.casimir3^[l] w)) = 0)
    (ρ : ℝ) (n J : ℕ) (e : Fin n → ℂ) (δ : ℝ) (hδ : 0 < δ) (he : Function.Injective e)
    (hre : ∀ i, (e i).re ≤ ρ)
    (hexp : ∀ (N : ℕ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w)) →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g) →
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g) →
      WhittakerBlock.IsArchSmooth3 u →
      (∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => u (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) →
      (∑ m, a₂ m • (WhittakerBlock.casimir2^[m] u) = 0) →
      (∑ m, a₃ m • (WhittakerBlock.casimir3^[m] u) = 0) →
      (∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w g‖ ≤ C * gauge3 ℚ g ^ N) →
      (∃ c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ (ρ + δ)) ∧
        ∃ c' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
          (∀ i j i' j', Continuous (c' i j i' j')) ∧
          (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
            ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
            ‖c i j y₂ k -
                (∑ i' : Fin n, ∑ j' : Fin J,
                  c' i j i' j' k * ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤
              C * y₂ ^ (ρ + δ)) ∧
          (∀ (i : Fin n) (j : Fin J),
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i'' : Fin n) (j'' : Fin J), (e i'').re < (e i).re →
              ∀ y₂ : ℝ, 0 < y₂ → c i'' j'' y₂ k = 0) →
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i' : Fin n) (j' : Fin J), c' i j i' j' k = 0) →
            ∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (y₂ : ℝ), 0 < y₂ → c i j y₂ k = 0)) ∧
      (∃ c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₁ : ℝ, b⁻¹ ≤ y₁ → y₁ ≤ b → ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₁ k * ((y₂ : ℂ) ^ e i * ((Real.log y₂ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₂ ^ (ρ + δ)) ∧
        ∃ c' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
          (∀ i j i' j', Continuous (c' i j i' j')) ∧
          (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
            ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
            ‖c i j y₁ k -
                (∑ i' : Fin n, ∑ j' : Fin J,
                  c' i j i' j' k * ((y₁ : ℂ) ^ e i' * ((Real.log y₁ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤
              C * y₁ ^ (ρ + δ)) ∧
          (∀ (i : Fin n) (j : Fin J),
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i'' : Fin n) (j'' : Fin J), (e i'').re < (e i).re →
              ∀ y₁ : ℝ, 0 < y₁ → c i'' j'' y₁ k = 0) →
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i' : Fin n) (j' : Fin J), c' i j i' j' k = 0) →
            ∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (y₁ : ℝ), 0 < y₁ → c i j y₁ k = 0)))
    (i9 i9' : Fin n) (j₀ j₀' : Fin J)
    (σ σ₃ : ℝ) (b₀ c₀ : Fin 3) (hb₀ : b₀ ≠ 0) (hc₀ : c₀ ≠ 0) (hbc : b₀ ≠ c₀)
    (ν : Fin 3 → ℂ) (hν0 : ν 0 = -1 / 2 + σ * Complex.I) (hνb : ν b₀ = 1 / 2 + σ * Complex.I)
    (hνc : ν c₀ = σ₃ * Complex.I)
    (Λ : ↥M →ₗ[ℂ] (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))
    (hΛa : (∀ (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv : v ∈ M)
        (cv : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
        (cv' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
        ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => cv i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
        ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ v
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
          (∑ i : Fin n, ∑ j : Fin J, cv i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
        C * y₁ ^ (ρ + δ)) ∧
        (∀ i j i' j', Continuous (cv' i j i' j')) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
        ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
        ‖cv i j y₂ k - (∑ i' : Fin n, ∑ j' : Fin J, cv' i j i' j' k *
          ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤ C * y₂ ^ (ρ + δ))) →
        ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, Λ ⟨v, hv⟩ k = cv' i9 j₀ i9' j₀' k))
    (hΛb : (∀ (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv : v ∈ M) (k' : AdelicGL 3 (𝓞 ℚ) ℚ)
        (hk'₁ : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1)
        (hk'₂ : archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3),
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
          Λ ⟨fun x => v (x * k'), h4 v hv k' hk'₁ hk'₂⟩ g = Λ ⟨v, hv⟩ (g * k')))
    (hΛc : (∀ (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv : v ∈ M) (c d : Fin 3) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        HasDerivAt
          (fun s : ℝ => Λ ⟨v, hv⟩ (g * WhittakerBlock.archRealLift3 fun a b =>
            (if a = b then (1 : ℝ) else 0) + if a = c ∧ b = d then s else 0))
          (Λ ⟨WhittakerBlock.archDeriv c d v, h5 v hv c d⟩ g) 0))
    (ε : Fin 3 → Fin 2) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ) (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1)
    (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ)
    (hcls : (ℓ = 0 ∧ ε 0 = ε b₀ ∧ ε 0 = ε c₀) ∨ (ℓ = 1 ∧ ε 0 = ε b₀ ∧ ε 0 ≠ ε c₀))
    (M' : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (hle : M' ≤ M)
    (hK : (∀ w ∈ M', ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ M'))
    (hD : (∀ w ∈ M', ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M'))
    (hEq : ∀ (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hu : u ∈ M'), (∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Λ ⟨u, hle hu⟩ (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * Λ ⟨u, hle hu⟩ g))
    (hsep : ∀ (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hu : u ∈ M'),
        (∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → ((1 / 8 : ℂ) * ∑ τ : Fin 3 → Fin 2, (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ)) *
          Λ ⟨u, hle hu⟩ (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) * (WhittakerBlock.archRealLift3 o * k₁))) = 0) → u = 0)
    (v' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv' : v' ∈ M')
    (hread' : ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        ((1 / 8 : ℂ) * ∑ τ : Fin 3 → Fin 2, (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ)) *
          Λ ⟨v', hle hv'⟩ (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) * (WhittakerBlock.archRealLift3 o * k₁))) =
          (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
          MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p)) :
    p = 0 := by
  classical
  have hv'M : v' ∈ M := hle hv'
  set α : ℕ := (ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2 with hα

  have hiso : ∀ (u : G3 → ℂ) (hu : u ∈ M') (τ : Fin 3 → Fin 2) (g : G3),
      piF ε (Λ ⟨u, hle hu⟩) (WhittakerBlock.archRealLift3 (msig τ) * g) = chi ε τ * piF ε (Λ ⟨u, hle hu⟩) g :=
    fun u hu τ g => (LanglandsTunnell.CubicInduction.upperTriangular_equivariant_and_signIsotypic_signProjection
      ν ε (Λ ⟨u, hle hu⟩) (hEq u hu)).2 τ g
  have hreadv : ∀ o : E33, ColOrth o → piF ε (Λ ⟨v', hv'M⟩) (WhittakerBlock.archRealLift3 o * k₁) =
      detC o ^ α * MvPolynomial.eval (pt o) (realise0 p) := fun o ho => hread' o ho

  set c' : ℂ := 1 / 2 - σ * Complex.I with hc'
  have hcase : (b₀ = 1 ∧ c₀ = 2) ∨ (b₀ = 2 ∧ c₀ = 1) := positions b₀ c₀ hb₀ hc₀ hbc
  have h48 := LanglandsTunnell.CubicInduction.inducedPicture_quantisedMinor_annihilates_lowest_of_matched σ σ₃
  have hkill : (∀ k : Fin 3 × Fin 3 → ℂ, (∀ i j : Fin 3, ∑ a : Fin 3, k (i, a) * k (j, a) = if i = j then 1 else 0) →
      MvPolynomial.eval k (dl ν c' 1) = 0) ∧
    (∀ k : Fin 3 × Fin 3 → ℂ, (∀ i j : Fin 3, ∑ a : Fin 3, k (i, a) * k (j, a) = if i = j then 1 else 0) →
      ∀ j : Fin 3, MvPolynomial.eval k (dl ν c' (MvPolynomial.X (c₀, j))) = 0) := by
    rcases hcase with ⟨hb, hc⟩ | ⟨hb, hc⟩
    · subst hb hc
      have hν : ν = ![-1 / 2 + σ * Complex.I, 1 / 2 + σ * Complex.I, σ₃ * Complex.I] := by
        funext a; fin_cases a <;> simp [hν0, hνb, hνc]
      subst hν
      exact ⟨fun k hk => h48.1 k hk, fun k hk j => h48.2.1 k hk j⟩
    · subst hb hc
      have hν : ν = ![-1 / 2 + σ * Complex.I, σ₃ * Complex.I, 1 / 2 + σ * Complex.I] := by
        funext a; fin_cases a <;> simp [hν0, hνb, hνc]
      subst hν
      exact ⟨fun k hk => h48.2.2.1 k hk, fun k hk j => h48.2.2.2 k hk j⟩
  obtain ⟨hkill1, hkillX⟩ := hkill

  have hstruct : ∃ c0 c1 : ℂ, (∀ x : Fin 3 → ℂ, MvPolynomial.eval x p = c0 + c1 * x c₀) ∧
      (c0 = 0 → c1 = 0 → p = 0) := by
    rcases hcls with ⟨hℓ, hε1, hε2⟩ | ⟨hℓ, hε1, hε2⟩
    · subst hℓ
      have hpC := eq_C_of_isHomogeneous_zero p hp
      refine ⟨p.coeff 0, 0, fun x => ?_, fun h0 _ => ?_⟩
      · conv_lhs => rw [hpC]
        simp
      · rw [hpC, h0, map_zero]
    · subst hℓ
      obtain ⟨c, hpc⟩ := exists_linear_of_isHomogeneous_one p hp
      have hevalp : ∀ x : Fin 3 → ℂ, MvPolynomial.eval x p = ∑ b : Fin 3, x b * c b := by
        intro x; rw [hpc]; simp [map_sum]
      have hreadc : ∀ o : E33, ColOrth o → piF ε (Λ ⟨v', hv'M⟩) (WhittakerBlock.archRealLift3 o * k₁) =
          detC o ^ α * ∑ b : Fin 3, ((o b 0 : ℝ) : ℂ) * c b := by
        intro o ho; rw [hreadv o ho, eval_realise0, hevalp]; rfl

      have hpar : ∀ a : Fin 3, a ≠ c₀ → (-1 : ℂ) ^ (α + 1) ≠ (-1 : ℂ) ^ (ε a : ℕ) := by
        intro a ha
        rw [hα]
        exact parity_obstruction ε b₀ c₀ hcase hε1 hε2 a ha
      have hpin : ∀ a : Fin 3, a ≠ c₀ → c a = 0 :=
        fun a ha => pin ε k₁ (Λ ⟨v', hv'M⟩) (hiso v' hv') α c hreadc a (hpar a ha)
      refine ⟨0, c c₀, fun x => ?_, fun _ h1 => ?_⟩
      · rw [hevalp, zero_add, Finset.sum_eq_single c₀ (fun b _ hb => by rw [hpin b hb, mul_zero])
          (fun h => absurd (Finset.mem_univ _) h)]
        ring
      · rw [hpc]
        refine Finset.sum_eq_zero (fun b _ => ?_)
        by_cases hb : b = c₀
        · subst hb; rw [h1, map_zero, mul_zero]
        · rw [hpin b hb, map_zero, mul_zero]
  obtain ⟨c0, c1, hq, hfin⟩ := hstruct

  have hΛzero : ∀ o₀ : E33, ColOrth o₀ → Λ ⟨v', hv'M⟩ (WhittakerBlock.archRealLift3 o₀ * k₁) = 0 := by
    intro o₀ ho₀
    have hdo₀ := det_ne_zero_of_colOrth o₀ ho₀
    have hko1 : ∀ q : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ q (WhittakerBlock.archRealLift3 o₀) = 1 :=
      fun q => componentAt3_lift o₀ hdo₀ q
    have hko2 : archComponent3 (𝓞 ℚ) ℚ (WhittakerBlock.archRealLift3 o₀) ∈ orth3 :=
      archComponent3_lift_mem_orth3 o₀ hdo₀ ((colOrth_iff o₀).mp ho₀)
    set w : G3 → ℂ := fun x => v' (x * WhittakerBlock.archRealLift3 o₀) with hw_def
    have hw : w ∈ M' := hK v' hv' _ hko1 hko2
    have hwM : w ∈ M := hle hw
    have hb : ∀ g : G3, Λ ⟨w, hwM⟩ g = Λ ⟨v', hv'M⟩ (g * WhittakerBlock.archRealLift3 o₀) :=
      fun g => hΛb v' hv'M _ hko1 hko2 g

    set Lw : R9 := MvPolynomial.C c0 + MvPolynomial.C c1 *
      ∑ cc : Fin 3, MvPolynomial.C ((o₀ cc 0 : ℝ) : ℂ) * MvPolynomial.X (c₀, cc) with hLw
    set Pw : R9 := MvPolynomial.C (detC o₀ ^ α) * (detX ^ α * Lw) with hPw
    have hreadw : Reads ε k₁ (Λ ⟨w, hwM⟩) Pw := by
      intro o ho
      set oo : E33 := fun a b => (Matrix.of o * Matrix.of o₀) a b with hoo
      have hoo_orth : ColOrth oo := colOrth_mul o o₀ ho ho₀
      have e1 : piF ε (Λ ⟨w, hwM⟩) (WhittakerBlock.archRealLift3 o * k₁) =
          piF ε (Λ ⟨v', hv'M⟩) (WhittakerBlock.archRealLift3 oo * k₁) := by
        unfold piF
        congr 1
        refine Finset.sum_congr rfl (fun τ _ => ?_)
        rw [hb]
        congr 2
        rw [mul_assoc, mul_assoc, ← lift_mul_comm_of_archComponent3_eq_one o₀ hdo₀ k₁ hk₁,
          ← mul_assoc (WhittakerBlock.archRealLift3 o), lift_mul' (det_ne_zero_of_colOrth o ho) hdo₀]
      rw [e1, hreadv oo hoo_orth, eval_realise0, hq]
      have hpt : pt oo (c₀, 0) = ∑ cc : Fin 3, ((o₀ cc 0 : ℝ) : ℂ) * ((o c₀ cc : ℝ) : ℂ) := by
        simp only [pt, hoo, Matrix.mul_apply, Matrix.of_apply]; push_cast
        exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
      rw [hpt]
      simp only [hPw, hLw, map_mul, map_add, map_pow, map_sum, MvPolynomial.eval_C, MvPolynomial.eval_X, eval_detX,
        hoo, detC_mul]
      simp only [pt]
      ring

    have hr12 := reads_archDeriv ν M h5 Λ hΛc ε k₁ hk₁ w hwM (hEq w hw) Pw hreadw 1 2
    have hr11 := reads_archDeriv ν M h5 Λ hΛc ε k₁ hk₁ w hwM (hEq w hw) Pw hreadw 1 1
    have hr02 := reads_archDeriv ν M h5 Λ hΛc ε k₁ hk₁ w hwM (hEq w hw) Pw hreadw 0 2
    have hr0112 := reads_archDeriv ν M h5 Λ hΛc ε k₁ hk₁ (WhittakerBlock.archDeriv 1 2 w) (h5 w hwM 1 2)
      (hEq _ (hD w hw 1 2)) (act ν 1 2 Pw) hr12 0 1
    have hr0211 := reads_archDeriv ν M h5 Λ hΛc ε k₁ hk₁ (WhittakerBlock.archDeriv 1 1 w) (h5 w hwM 1 1)
      (hEq _ (hD w hw 1 1)) (act ν 1 1 Pw) hr11 0 2

    have hm1 : WhittakerBlock.archDeriv 0 1 (WhittakerBlock.archDeriv 1 2 w) ∈ M' := hD _ (hD w hw 1 2) 0 1
    have hm2 : WhittakerBlock.archDeriv 0 2 (WhittakerBlock.archDeriv 1 1 w) ∈ M' := hD _ (hD w hw 1 1) 0 2
    have hm3 : WhittakerBlock.archDeriv 0 2 w ∈ M' := hD w hw 0 2
    set u : G3 → ℂ := WhittakerBlock.archDeriv 0 1 (WhittakerBlock.archDeriv 1 2 w) -
      WhittakerBlock.archDeriv 0 2 (WhittakerBlock.archDeriv 1 1 w) - c' • WhittakerBlock.archDeriv 0 2 w with hu_def
    have hu : u ∈ M' := M'.sub_mem (M'.sub_mem hm1 hm2) (M'.smul_mem c' hm3)
    have hΛu : Λ ⟨u, hle hu⟩ = Λ ⟨_, hle hm1⟩ - Λ ⟨_, hle hm2⟩ - c' • Λ ⟨_, hle hm3⟩ := by
      have : (⟨u, hle hu⟩ : ↥M) = ⟨_, hle hm1⟩ - ⟨_, hle hm2⟩ - c' • ⟨_, hle hm3⟩ := Subtype.ext rfl
      rw [this, map_sub, map_sub, map_smul]
    have hread_u : ∀ o : E33, ColOrth o →
        piF ε (Λ ⟨u, hle hu⟩) (WhittakerBlock.archRealLift3 o * k₁) = MvPolynomial.eval (pt o) (dl ν c' Pw) := by
      intro o ho
      rw [hΛu, piF_sub, piF_sub, piF_smul, hr0112 o ho, hr0211 o ho, hr02 o ho]
      simp only [dl, map_sub, map_mul, MvPolynomial.eval_C]
    have hkill_u : ∀ o : E33, ColOrth o → MvPolynomial.eval (pt o) (dl ν c' Pw) = 0 := by
      intro o ho
      have hro := rowOrth_cast o ho
      have hL : dl ν c' Lw = MvPolynomial.C c0 * dl ν c' 1 +
          ∑ cc : Fin 3, MvPolynomial.C (c1 * ((o₀ cc 0 : ℝ) : ℂ)) * dl ν c' (MvPolynomial.X (c₀, cc)) := by
        rw [hLw, dl_add, ← dl_C_mul, mul_one, Finset.mul_sum]
        congr 1
        have : ∀ s : Finset (Fin 3), dl ν c' (∑ cc ∈ s, MvPolynomial.C c1 * (MvPolynomial.C ((o₀ cc 0 : ℝ) : ℂ) * MvPolynomial.X (c₀, cc))) =
            ∑ cc ∈ s, MvPolynomial.C (c1 * ((o₀ cc 0 : ℝ) : ℂ)) * dl ν c' (MvPolynomial.X (c₀, cc)) := by
          intro s
          induction s using Finset.induction_on with
          | empty => simp [dl, act]
          | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dl_add, ih, ← mul_assoc, ← map_mul, dl_C_mul]
        exact this _
      rw [hPw, dl_C_mul, dl_detX_pow_mul, hL]
      simp only [map_mul, map_add, map_sum, map_pow, MvPolynomial.eval_C, hkill1 (pt o) hro, hkillX (pt o) hro,
        mul_zero, Finset.sum_const_zero, add_zero]
    have hu0 : u = 0 := hsep u hu (fun o ho => by
      have := hread_u o ho
      rw [hkill_u o ho] at this
      exact this)

    have h1w := h1 w hwM
    have h1w11 := h1 _ (h5 w hwM 1 1)
    have hWw : ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
        whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ w
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k₁) = 0 :=
      fun y₁ y₂ hy₁ hy₂ => whittaker_torus_eq_zero_of_minor_eq_zero k₁ hk₁ w h1w.1 h1w.2.2.1 h1w.2.2.2
        h1w11.1 h1w11.2.2.1 h1w11.2.2.2 c' (fun g => by
          have := congrFun hu0 g
          simpa [hu_def, smul_eq_mul] using this) y₁ y₂ hy₁ hy₂

    obtain ⟨N, hN⟩ := h13 w hwM
    obtain ⟨cw, hc1, hc2, cw', hc'1, hc'2, -⟩ := (hexp N w h1w.2.2.1 h1w.2.2.2 (h12 w hwM) h1w.1
      (h3 w hwM) (hrel w hwM).1 (hrel w hwM).2 hN).1
    have huniq := (LanglandsTunnell.CubicInduction.joint_expansion_coeff_eq_zero_of_forall_whittaker3_diag_mul_eq_zero
      w ρ n J e δ hδ he hre cw cw' ⟨hc1, hc2, hc'1, hc'2⟩ k₁ hWw).2
    have hΛw : Λ ⟨w, hwM⟩ k₁ = 0 := by
      rw [hΛa w hwM cw cw' ⟨hc1, hc2, hc'1, hc'2⟩ k₁]; exact huniq _ _ _ _
    rw [hb k₁, ← lift_mul_comm_of_archComponent3_eq_one o₀ hdo₀ k₁ hk₁] at hΛw
    exact hΛw

  have hrd : ∀ o : E33, ColOrth o → c0 + c1 * ((o c₀ 0 : ℝ) : ℂ) = 0 := by
    intro o ho
    have h := hreadv o ho
    rw [eval_realise0, hq] at h
    have hz : piF ε (Λ ⟨v', hv'M⟩) (WhittakerBlock.archRealLift3 o * k₁) = 0 := by
      unfold piF
      rw [Finset.sum_eq_zero, mul_zero]
      intro τ _
      rw [← mul_assoc, lift_msig_mul τ o ho, hΛzero _ (colOrth_mul _ _ (msig_colOrth τ) ho), mul_zero]
    rw [hz] at h
    have := (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (detC_ne_zero o ho))
    simpa [pt] using this
  have h0 := hrd (perm 0) (perm_colOrth 0)
  have h1' := hrd (perm c₀) (perm_colOrth c₀)
  rw [perm_col0, if_neg hc₀] at h0
  rw [perm_col0, if_pos rfl] at h1'
  have hc0 : c0 = 0 := by simpa using h0
  have hc1 : c1 = 0 := by rw [hc0] at h1'; simpa using h1'
  exact hfin hc0 hc1

end
end S_LanglandsTunnell_CubicInduction_eq_zero_of_read_signProjection_of_separating_stable_submodule
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_eq_zero_of_read_signProjection_of_separating_stable_submodule (solution)
