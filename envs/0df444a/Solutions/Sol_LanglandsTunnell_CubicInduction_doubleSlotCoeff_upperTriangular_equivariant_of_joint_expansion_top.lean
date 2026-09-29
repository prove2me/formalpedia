-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d42ffd89-98d1-5037-bfbd-4841ab799000

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_WhittakerBlock
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_LanglandsTunnell_CubicInduction_whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Theorems.Thm_LanglandsTunnell_CubicInduction_expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace R1CuspDeriv

open MeasureTheory Filter Metric Topology
open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

section Engine

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable (ν : Measure X) [IsFiniteMeasure ν] {C : Set X}

theorem integrable_of_continuous (hC : IsCompact C) (hνC : ∀ᵐ y ∂ν, y ∈ C) (φ : X → ℂ)
    (hφ : Continuous φ) : Integrable φ ν := by
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hφ.continuousOn
  exact Integrable.of_bound hφ.aestronglyMeasurable M (hνC.mono fun y hy => hM y hy)

theorem continuous_integral_of_continuous (hC : IsCompact C) (hνC : ∀ᵐ y ∂ν, y ∈ C)
    {P : Type*} [TopologicalSpace P] [LocallyCompactSpace P] [FirstCountableTopology P]
    (f : P → X → ℂ) (hf : Continuous fun q : P × X => f q.1 q.2) :
    Continuous fun p => ∫ y, f p y ∂ν := by
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨N, hN, hNp⟩ := exists_compact_mem_nhds p₀
  obtain ⟨M, hM⟩ := (hN.prod hC).exists_bound_of_continuousOn hf.continuousOn
  have hcont : ∀ p : P, Continuous fun y => f p y := fun p =>
    hf.comp (continuous_const.prodMk continuous_id)
  refine continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ (integrable_const M) ?_
  · exact Eventually.of_forall fun p => (hcont p).aestronglyMeasurable
  · filter_upwards [hNp] with p hp
    exact hνC.mono fun y hy => hM (p, y) ⟨hp, hy⟩
  · exact ae_of_all _ fun y => (hf.comp (continuous_id.prodMk continuous_const)).continuousAt

theorem hasDerivAt_integral_of_continuous (hC : IsCompact C) (hνC : ∀ᵐ y ∂ν, y ∈ C)
    (F F' : ℝ → X → ℂ) {r : ℝ} (hr : 0 < r)
    (hF : Continuous fun q : closedBall (0 : ℝ) r × X => F q.1 q.2)
    (hF' : Continuous fun q : closedBall (0 : ℝ) r × X => F' q.1 q.2)
    (hd : ∀ y, ∀ s ∈ ball (0 : ℝ) r, HasDerivAt (fun σ => F σ y) (F' s y) s) :
    ∀ s₀ ∈ ball (0 : ℝ) r, HasDerivAt (fun s => ∫ y, F s y ∂ν) (∫ y, F' s₀ y ∂ν) s₀ := by
  intro s₀ hs₀
  haveI : CompactSpace (closedBall (0 : ℝ) r) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := (isCompact_univ.prod hC).exists_bound_of_continuousOn hF'.continuousOn
  have hcF : ∀ s (hs : s ∈ closedBall (0 : ℝ) r), Continuous fun y => F s y := fun s hs =>
    hF.comp ((continuous_const (y := (⟨s, hs⟩ : closedBall (0 : ℝ) r))).prodMk continuous_id)
  have hcF' : ∀ s (hs : s ∈ closedBall (0 : ℝ) r), Continuous fun y => F' s y := fun s hs =>
    hF'.comp ((continuous_const (y := (⟨s, hs⟩ : closedBall (0 : ℝ) r))).prodMk continuous_id)
  have hball : ball (0 : ℝ) r ∈ 𝓝 s₀ := isOpen_ball.mem_nhds hs₀
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (F := F) (F' := F') (x₀ := s₀)
    (bound := fun _ => M) hball ?_ ?_ ?_ ?_ (integrable_const M) ?_).2
  · filter_upwards [hball] with s hs using (hcF s (ball_subset_closedBall hs)).aestronglyMeasurable
  · exact integrable_of_continuous ν hC hνC _ (hcF s₀ (ball_subset_closedBall hs₀))
  · exact (hcF' s₀ (ball_subset_closedBall hs₀)).aestronglyMeasurable
  · exact hνC.mono fun y hy s hs => hM (⟨s, ball_subset_closedBall hs⟩, y) ⟨Set.mem_univ _, hy⟩
  · exact ae_of_all _ fun y s hs => hd y s hs

end Engine

section Arch

def ofRealHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.toRingHom

theorem ofRealHom_apply (r : ℝ) : ofRealHom r = StandardKernel.ofReal r := rfl

theorem realCoord_ofReal (r : ℝ) : StandardKernel.realCoord (StandardKernel.ofReal r) = r := by
  show (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)
    ((InfinitePlace.Completion.ringEquivRealOfIsReal _).symm r) = r
  exact RingEquiv.apply_symm_apply _ _

def rho : Matrix (Fin 3) (Fin 3) ℝ →+* Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) := ofRealHom.mapMatrix

def psi : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) →+* Matrix (Fin 3) (Fin 3) ℝ :=
  (StandardKernel.realCoord.comp (AdelicLevel.adeleArch (𝓞 ℚ) ℚ)).mapMatrix

theorem archRealMat3_eq (e : Matrix (Fin 3) (Fin 3) ℝ) :
    WhittakerBlock.archRealMat3 e = archMatrixInclN (Fin 3) ℚ (rho e) := rfl

theorem psi_archRealMat3 (e : Matrix (Fin 3) (Fin 3) ℝ) : psi (WhittakerBlock.archRealMat3 e) = e := by
  ext i j
  change StandardKernel.realCoord (AdelicLevel.adeleArch (𝓞 ℚ) ℚ (archMatrixInclN (Fin 3) ℚ (rho e) i j)) = e i j
  rw [adeleArch_archMatrixInclN]
  exact realCoord_ofReal (e i j)

theorem isUnit_archRealMat3_iff (e : Matrix (Fin 3) (Fin 3) ℝ) :
    IsUnit (WhittakerBlock.archRealMat3 e) ↔ e.det ≠ 0 := by
  constructor
  · intro h
    have h' := h.map psi
    rw [psi_archRealMat3, Matrix.isUnit_iff_isUnit_det] at h'
    exact h'.ne_zero
  · intro h
    have hu : IsUnit e := (Matrix.isUnit_iff_isUnit_det e).mpr (isUnit_iff_ne_zero.mpr h)
    exact hu.map ((archMatrixInclHomN (Fin 3) ℚ).comp rho.toMonoidHom)

def liftGL : GL (Fin 3) ℝ →* AdelicGL 3 (𝓞 ℚ) ℚ := (archInclN (Fin 3) ℚ).comp (Units.map rho.toMonoidHom)

def toGL (e : Matrix (Fin 3) (Fin 3) ℝ) (h : e.det ≠ 0) : GL (Fin 3) ℝ :=
  Matrix.nonsingInvUnit e (isUnit_iff_ne_zero.mpr h)

@[scoped simp] theorem coe_toGL (e : Matrix (Fin 3) (Fin 3) ℝ) (h : e.det ≠ 0) : (toGL e h : Matrix (Fin 3) (Fin 3) ℝ) = e :=
  rfl

theorem archRealLift3_eq (e : Matrix (Fin 3) (Fin 3) ℝ) (h : e.det ≠ 0) :
    WhittakerBlock.archRealLift3 e = liftGL (toGL e h) := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_pos ((isUnit_archRealMat3_iff e).mpr h)]
  exact Units.ext (by rw [IsUnit.unit_spec]; rfl)

theorem archRealLift3_of_det (e : Matrix (Fin 3) (Fin 3) ℝ) (h : e.det = 0) : WhittakerBlock.archRealLift3 e = 1 := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_neg]
  rw [isUnit_archRealMat3_iff]
  exact fun h' => h' h

theorem coe_archRealLift3 (e : Matrix (Fin 3) (Fin 3) ℝ) (h : e.det ≠ 0) :
    ((WhittakerBlock.archRealLift3 e : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      WhittakerBlock.archRealMat3 e := by
  rw [archRealLift3_eq e h]; rfl

theorem archRealLift3_mul (e e' : Fin 3 → Fin 3 → ℝ) (h : (Matrix.of e).det ≠ 0) (h' : (Matrix.of e').det ≠ 0) :
    WhittakerBlock.archRealLift3 (Matrix.of e * Matrix.of e') =
      WhittakerBlock.archRealLift3 e * WhittakerBlock.archRealLift3 e' := by
  have hm : (Matrix.of e * Matrix.of e').det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero h h'
  have h1 : WhittakerBlock.archRealLift3 e = liftGL (toGL (Matrix.of e) h) := archRealLift3_eq (Matrix.of e) h
  have h2 : WhittakerBlock.archRealLift3 e' = liftGL (toGL (Matrix.of e') h') := archRealLift3_eq (Matrix.of e') h'
  rw [archRealLift3_eq _ hm, h1, h2, ← map_mul liftGL]
  congr 1
  exact Units.ext rfl

theorem archRealLift3_one : WhittakerBlock.archRealLift3 (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  rw [archRealLift3_eq _ (by simp)]
  have : toGL 1 (by simp) = 1 := Units.ext rfl
  rw [this, map_one]

theorem commute_archInclN (t : AdelicGL 3 (𝓞 ℚ) ℚ) (ht : archComponent3 (𝓞 ℚ) ℚ t = 1)
    (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) : t * archInclN (Fin 3) ℚ h = archInclN (Fin 3) ℚ h * t := by
  set A : AdelicGL 3 (𝓞 ℚ) ℚ := archInclN (Fin 3) ℚ h with hAdef
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  have hA1 : (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (A : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      (h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :=
    Matrix.ext fun a b => adeleArch_archMatrixInclN (Fin 3) ℚ (h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) a b
  have hA2 : (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (A : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = 1 :=
    Matrix.ext fun a b => adeleFin_archMatrixInclN (Fin 3) ℚ (h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) a b
  have hT : (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (t : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = 1 := by
    rw [← Units.val_one, ← ht]; rfl
  refine Matrix.ext fun i j => Prod.ext ?_ ?_
  · change ((AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
        ((t : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) * (A : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)))) i j =
      ((AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
        ((A : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) * (t : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)))) i j
    rw [map_mul, map_mul, hA1, hT, one_mul, mul_one]
  · change ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix
        ((t : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) * (A : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)))) i j =
      ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix
        ((A : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) * (t : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)))) i j
    rw [map_mul, map_mul, hA2, one_mul, mul_one]

theorem commute_archRealLift3 (t : AdelicGL 3 (𝓞 ℚ) ℚ) (ht : archComponent3 (𝓞 ℚ) ℚ t = 1)
    (e : Matrix (Fin 3) (Fin 3) ℝ) :
    t * WhittakerBlock.archRealLift3 e = WhittakerBlock.archRealLift3 e * t := by
  by_cases h : e.det = 0
  · rw [archRealLift3_of_det e h, mul_one, one_mul]
  · rw [archRealLift3_eq e h]
    exact commute_archInclN t ht _

def cfun (i j : Fin 3) (s : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0

def efun (i j : Fin 3) : Fin 3 → Fin 3 → ℝ := fun a b => if a = i ∧ b = j then 1 else 0

def kap (i j : Fin 3) (s : ℝ) : ℝ := 1 + if i = j then s else 0

theorem cfun_eq (i j : Fin 3) (s : ℝ) : cfun i j s = (fun a b => if a = b then (1 : ℝ) else 0) + s • efun i j := by
  funext a b
  simp only [cfun, efun, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

theorem of_cfun (i j : Fin 3) (s : ℝ) : Matrix.of (cfun i j s) = 1 + s • Matrix.single i j (1 : ℝ) := by
  ext a b
  simp only [cfun, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  congr 1
  by_cases h : a = i ∧ b = j
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]

theorem det_cfun (i j : Fin 3) (s : ℝ) : (Matrix.of (cfun i j s)).det = kap i j s := by
  unfold cfun kap
  fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_three]

theorem kap_pos (i j : Fin 3) {s : ℝ} (hs : |s| < 1) : 0 < kap i j s := by
  unfold kap
  split_ifs
  · have := (abs_lt.mp hs).1; linarith
  · norm_num

theorem continuous_kap (i j : Fin 3) : Continuous (kap i j) := by
  by_cases h : i = j
  · have : kap i j = fun s => 1 + s := funext fun s => by simp [kap, h]
    rw [this]; fun_prop
  · have : kap i j = fun _ => 1 := funext fun s => by simp [kap, h]
    rw [this]; fun_prop

theorem det_cfun_ne (i j : Fin 3) {s : ℝ} (hs : |s| < 1) : (Matrix.of (cfun i j s)).det ≠ 0 := by
  rw [det_cfun]; exact (kap_pos i j hs).ne'

theorem cfun_zero (i j : Fin 3) : Matrix.of (cfun i j 0) = 1 := by
  rw [of_cfun, zero_smul, add_zero]

theorem of_cfun_mul (i j : Fin 3) (s τ : ℝ) :
    Matrix.of (cfun i j s) * Matrix.of (cfun i j τ) = Matrix.of (cfun i j (s + kap i j s * τ)) := by
  rw [of_cfun, of_cfun, of_cfun]
  by_cases h : i = j
  · subst h
    have hE : Matrix.single i i (1 : ℝ) * Matrix.single i i (1 : ℝ) = Matrix.single i i (1 : ℝ) := by
      rw [Matrix.single_mul_single_same, one_mul]
    have hk : kap i i s = 1 + s := by simp [kap]
    rw [hk, add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, hE, smul_smul]
    module
  · have hE : Matrix.single i j (1 : ℝ) * Matrix.single i j (1 : ℝ) = 0 :=
      Matrix.single_mul_single_of_ne 1 i j i (Ne.symm h) 1
    have hk : kap i j s = 1 := by simp [kap, h]
    rw [hk, add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, hE]
    module

theorem continuous_cfun (i j : Fin 3) : Continuous (cfun i j) := by
  rw [show cfun i j = fun s => (fun a b => if a = b then (1 : ℝ) else 0) + s • efun i j from funext (cfun_eq i j)]
  fun_prop

theorem hasDerivAt_cfun (i j : Fin 3) (s : ℝ) : HasDerivAt (cfun i j) (efun i j) s := by
  rw [show cfun i j = fun s => (fun a b => if a = b then (1 : ℝ) else 0) + s • efun i j from funext (cfun_eq i j)]
  have h := ((hasDerivAt_id s).smul_const (efun i j)).const_add (fun a b : Fin 3 => if a = b then (1 : ℝ) else 0)
  rw [one_smul] at h
  exact h

def U : Set (Fin 3 → Fin 3 → ℝ) := {e | (Matrix.of e).det ≠ 0}

theorem isOpen_U : IsOpen U := by
  have hc : Continuous fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).det :=
    (continuous_id : Continuous fun e : Fin 3 → Fin 3 → ℝ => Matrix.of e).matrix_det
  exact isOpen_compl_singleton.preimage hc

theorem cfun_mem_U (i j : Fin 3) {s : ℝ} (hs : |s| < 1) : cfun i j s ∈ U := det_cfun_ne i j hs

def L (i j : Fin 3) (s : ℝ) : AdelicGL 3 (𝓞 ℚ) ℚ := WhittakerBlock.archRealLift3 (cfun i j s)

theorem L_zero (i j : Fin 3) : L i j 0 = 1 := by
  show WhittakerBlock.archRealLift3 (Matrix.of (cfun i j 0)) = 1
  rw [cfun_zero]
  exact archRealLift3_one

theorem L_mul_L (i j : Fin 3) {s τ : ℝ} (hs : |s| < 1) (hτ : |τ| < 1) :
    L i j s * L i j τ = L i j (s + kap i j s * τ) := by
  have h := archRealLift3_mul (cfun i j s) (cfun i j τ) (det_cfun_ne i j hs) (det_cfun_ne i j hτ)
  rw [of_cfun_mul] at h
  exact h.symm

theorem archDeriv_apply (i j : Fin 3) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.archDeriv i j φ g = deriv (fun s => φ (g * L i j s)) 0 := rfl

variable {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}

theorem differentiableAt_slice (hΦ : WhittakerBlock.IsArchSmooth3 Φ) (h : AdelicGL 3 (𝓞 ℚ) ℚ)
    {e : Fin 3 → Fin 3 → ℝ} (he : e ∈ U) :
    DifferentiableAt ℝ (fun e : Fin 3 → Fin 3 → ℝ => Φ (h * WhittakerBlock.archRealLift3 e)) e :=
  ((hΦ h).differentiableOn (by simp)).differentiableAt (isOpen_U.mem_nhds he)

theorem differentiableAt_comp_L (hΦ : WhittakerBlock.IsArchSmooth3 Φ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3)
    {s : ℝ} (hs : |s| < 1) : DifferentiableAt ℝ (fun σ => Φ (h * L i j σ)) s :=
  (differentiableAt_slice hΦ h (cfun_mem_U i j hs)).comp s (hasDerivAt_cfun i j s).differentiableAt

theorem archDeriv_apply_mul_L (hΦ : WhittakerBlock.IsArchSmooth3 Φ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3)
    {s : ℝ} (hs : |s| < 1) :
    WhittakerBlock.archDeriv i j Φ (h * L i j s) = (kap i j s : ℂ) * deriv (fun σ => Φ (h * L i j σ)) s := by
  rw [archDeriv_apply]

  have hev : (fun τ => Φ (h * L i j s * L i j τ)) =ᶠ[𝓝 0] fun τ => (fun σ => Φ (h * L i j σ)) (s + kap i j s * τ) := by
    have hnb : ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := isOpen_ball.mem_nhds (by simp)
    filter_upwards [hnb] with τ hτ
    have hτ' : |τ| < 1 := by simpa [Real.dist_eq] using hτ
    rw [mul_assoc, L_mul_L i j hs hτ']
  rw [hev.deriv_eq]
  rw [show (fun τ => (fun σ => Φ (h * L i j σ)) (s + kap i j s * τ)) =
      fun τ => (fun σ' => (fun σ => Φ (h * L i j σ)) (s + σ')) (kap i j s * τ) from rfl]
  rw [deriv_comp_mul_left (kap i j s) (fun σ' => (fun σ => Φ (h * L i j σ)) (s + σ')) 0, mul_zero,
    deriv_comp_const_add (fun σ => Φ (h * L i j σ)) s 0, add_zero, Complex.real_smul]

theorem hasDerivAt_comp_L (hΦ : WhittakerBlock.IsArchSmooth3 Φ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3)
    {s : ℝ} (hs : |s| < 1) :
    HasDerivAt (fun σ => Φ (h * L i j σ)) ((kap i j s : ℂ)⁻¹ * WhittakerBlock.archDeriv i j Φ (h * L i j s)) s := by
  have hk : (kap i j s : ℂ) ≠ 0 := by exact_mod_cast (kap_pos i j hs).ne'
  rw [archDeriv_apply_mul_L hΦ h i j hs, ← mul_assoc, inv_mul_cancel₀ hk, one_mul]
  exact (differentiableAt_comp_L hΦ h i j hs).hasDerivAt

def mulE (i j : Fin 3) (e : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun a b => (Matrix.of e * Matrix.single i j (1 : ℝ)) a b

theorem mulE_eq (i j : Fin 3) : mulE i j = fun e a b => if b = j then e a i else 0 := by
  funext e a b
  simp only [mulE, Matrix.mul_apply, Matrix.of_apply, Matrix.single_apply, mul_ite, mul_one, mul_zero]
  by_cases hb : b = j
  · rw [if_pos hb, Finset.sum_eq_single i (fun k _ hk => if_neg (fun h => hk h.1.symm)) (by simp)]
    rw [if_pos ⟨rfl, hb.symm⟩]
  · rw [if_neg hb]
    exact Finset.sum_eq_zero fun k _ => if_neg fun h => hb h.2.symm

theorem contDiff_mulE (i j : Fin 3) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mulE i j) := by
  rw [mulE_eq]
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  by_cases hb : b = j
  · simp only [if_pos hb]; exact contDiff_apply_apply ℝ ℝ a i
  · simp only [if_neg hb]; exact contDiff_const

theorem of_mul_of_cfun (i j : Fin 3) (e : Fin 3 → Fin 3 → ℝ) (τ : ℝ) :
    Matrix.of e * Matrix.of (cfun i j τ) = Matrix.of (e + τ • mulE i j e) := by
  rw [of_cfun, mul_add, mul_one, Matrix.mul_smul]
  rfl

theorem hasDerivAt_mul_cfun (i j : Fin 3) (e : Fin 3 → Fin 3 → ℝ) :
    HasDerivAt (fun τ : ℝ => e + τ • mulE i j e) (mulE i j e) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const (mulE i j e)).const_add e
  rw [one_smul] at h
  exact h

theorem archDeriv_slice_eq (hΦ : WhittakerBlock.IsArchSmooth3 Φ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3)
    {e : Fin 3 → Fin 3 → ℝ} (he : e ∈ U) :
    WhittakerBlock.archDeriv i j Φ (g * WhittakerBlock.archRealLift3 e) =
      fderiv ℝ (fun e' : Fin 3 → Fin 3 → ℝ => Φ (g * WhittakerBlock.archRealLift3 e')) e (mulE i j e) := by
  rw [archDeriv_apply]
  have hev : (fun τ => Φ (g * WhittakerBlock.archRealLift3 e * L i j τ)) =ᶠ[𝓝 0]
      (fun e' : Fin 3 → Fin 3 → ℝ => Φ (g * WhittakerBlock.archRealLift3 e')) ∘ fun τ => e + τ • mulE i j e := by
    have hnb : ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := isOpen_ball.mem_nhds (by simp)
    filter_upwards [hnb] with τ hτ
    have hτ' : |τ| < 1 := by simpa [Real.dist_eq] using hτ
    simp only [Function.comp_apply, L]
    rw [mul_assoc, ← archRealLift3_mul e (cfun i j τ) he (det_cfun_ne i j hτ'), of_mul_of_cfun]
    rfl
  rw [hev.deriv_eq]
  exact ((differentiableAt_slice hΦ g he).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
    (hasDerivAt_mul_cfun i j e) (by simp)).deriv

theorem isArchSmooth3_archDeriv (hΦ : WhittakerBlock.IsArchSmooth3 Φ) (i j : Fin 3) :
    WhittakerBlock.IsArchSmooth3 (WhittakerBlock.archDeriv i j Φ) := by
  intro g
  have hψ := hΦ g
  have hU : {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} = U := rfl
  rw [hU] at hψ ⊢
  have hd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun e => fderiv ℝ (fun e' : Fin 3 → Fin 3 → ℝ => Φ (g * WhittakerBlock.archRealLift3 e')) e (mulE i j e))
      U :=
    (hψ.fderiv_of_isOpen isOpen_U (by simp)).clm_apply (contDiff_mulE i j).contDiffOn
  exact hd.congr fun e he => archDeriv_slice_eq hΦ g i j he

theorem continuous_archRealMat3_cfun (i j : Fin 3) :
    Continuous fun s => WhittakerBlock.archRealMat3 (cfun i j s) := by
  have h1 : Continuous fun s => rho (Matrix.of (cfun i j s)) :=
    (continuous_cfun i j).matrix_map StandardKernel.continuous_ofReal
  refine continuous_pi fun a => continuous_pi fun b => ?_
  exact ((continuous_apply_apply a b).comp h1).prodMk continuous_const

theorem abs_neg_div_kap_lt (i j : Fin 3) {s : ℝ} (hs : |s| ≤ 1 / 3) : |-(s / kap i j s)| < 1 := by
  have hs1 : |s| < 1 := lt_of_le_of_lt hs (by norm_num)
  have hk := kap_pos i j hs1
  rw [abs_neg, abs_div, abs_of_pos hk, div_lt_one hk]
  unfold kap
  split_ifs with h
  · have := (abs_le.mp hs).1; have := (abs_le.mp hs).2
    rw [abs_lt]; constructor <;> linarith
  · simpa using hs1

theorem L_inv_eq (i j : Fin 3) {s : ℝ} (hs : |s| ≤ 1 / 3) :
    (L i j s)⁻¹ = L i j (-(s / kap i j s)) := by
  have hs1 : |s| < 1 := lt_of_le_of_lt hs (by norm_num)
  have hk := kap_pos i j hs1
  rw [inv_eq_iff_mul_eq_one, L_mul_L i j hs1 (abs_neg_div_kap_lt i j hs)]
  have : s + kap i j s * -(s / kap i j s) = 0 := by field_simp; ring
  rw [this, L_zero]

theorem continuousOn_L (i j : Fin 3) : ContinuousOn (L i j) (closedBall (0 : ℝ) (1 / 3)) := by
  rw [continuousOn_iff_continuous_restrict]
  have hmem : ∀ s : closedBall (0 : ℝ) (1 / 3), |(s : ℝ)| ≤ 1 / 3 := fun s => by
    have := s.2; simpa [Real.dist_eq] using this
  have hmem1 : ∀ s : closedBall (0 : ℝ) (1 / 3), |(s : ℝ)| < 1 := fun s => lt_of_le_of_lt (hmem s) (by norm_num)
  rw [Units.continuous_iff]
  constructor
  · have : (Units.val ∘ (closedBall (0 : ℝ) (1 / 3)).domRestrict (L i j)) =
        fun s : closedBall (0 : ℝ) (1 / 3) => WhittakerBlock.archRealMat3 (cfun i j s) := by
      funext s
      exact coe_archRealLift3 _ (det_cfun_ne i j (hmem1 s))
    rw [this]
    exact (continuous_archRealMat3_cfun i j).comp continuous_subtype_val
  · have : (fun s : closedBall (0 : ℝ) (1 / 3) => Units.val (((closedBall (0 : ℝ) (1 / 3)).domRestrict (L i j) s)⁻¹)) =
        fun s : closedBall (0 : ℝ) (1 / 3) => WhittakerBlock.archRealMat3 (cfun i j (-(s / kap i j s))) := by
      funext s
      show Units.val (L i j s)⁻¹ = _
      rw [L_inv_eq i j (hmem s)]
      exact coe_archRealLift3 _ (det_cfun_ne i j (abs_neg_div_kap_lt i j (hmem s)))
    rw [this]
    refine (continuous_archRealMat3_cfun i j).comp ?_
    have hk : ∀ s : closedBall (0 : ℝ) (1 / 3), kap i j s ≠ 0 := fun s => (kap_pos i j (hmem1 s)).ne'
    have hkc : Continuous fun s : closedBall (0 : ℝ) (1 / 3) => kap i j s :=
      (continuous_kap i j).comp continuous_subtype_val
    exact (continuous_subtype_val.div hkc hk).neg

end Arch

section Cusp

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

def ν0 : Measure (AdeleRing (𝓞 ℚ) ℚ) :=
  ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)

scoped instance : IsProbabilityMeasure ν0 := AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ

scoped instance : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdeleRing.secondCountableTopology ℚ

theorem exists_compact_ae : ∃ C : Set (AdeleRing (𝓞 ℚ) ℚ), IsCompact C ∧ ∀ᵐ y ∂ν0, y ∈ C := by
  obtain ⟨C, hC, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  exact ⟨C, hC, (ProbabilityTheory.ae_cond_mem (AdelicBox.measurableSet_adelicBox ℚ)).mono fun y hy => hsub hy⟩

variable (u : AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → AdelicGL 3 (𝓞 ℚ) ℚ)
  (hu : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => u p.1 p.2)

include hu

theorem integral_integral_sum_translate (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous f)
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∫ x, ∫ y, (∑ i, c i * f (u x y * g * t i)) ∂ν0 ∂ν0 = ∑ i, c i * ∫ x, ∫ y, f (u x y * (g * t i)) ∂ν0 ∂ν0 := by
  obtain ⟨C, hC, hνC⟩ := exists_compact_ae
  have hjc : ∀ i, Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => f (u q.1 q.2 * (g * t i)) :=
    fun i => hc.comp (hu.mul continuous_const)
  have hin : ∀ i x, Integrable (fun y => f (u x y * (g * t i))) ν0 := fun i x =>
    integrable_of_continuous ν0 hC hνC _ (hc.comp ((hu.comp (Continuous.prodMk_right x)).mul continuous_const))
  have hout : ∀ i, Integrable (fun x => ∫ y, f (u x y * (g * t i)) ∂ν0) ν0 := fun i =>
    integrable_of_continuous ν0 hC hνC _ (continuous_integral_of_continuous ν0 hC hνC _ (hjc i))
  have hinner : ∀ x, ∫ y, (∑ i, c i * f (u x y * g * t i)) ∂ν0 = ∑ i, c i * ∫ y, f (u x y * (g * t i)) ∂ν0 := by
    intro x
    simp_rw [mul_assoc]
    rw [integral_finsetSum _ fun i _ => (hin i x).const_mul (c i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  simp_rw [hinner]
  rw [integral_finsetSum _ fun i _ => (hout i).const_mul (c i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

theorem integral_integral_archDeriv_eq_zero {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hΦc : Continuous Φ)
    (hΦs : WhittakerBlock.IsArchSmooth3 Φ) (i j : Fin 3)
    (hΦ'c : Continuous (WhittakerBlock.archDeriv i j Φ))
    (hcusp : ∀ g, ∫ x, ∫ y, Φ (u x y * g) ∂ν0 ∂ν0 = 0) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∫ x, ∫ y, WhittakerBlock.archDeriv i j Φ (u x y * g) ∂ν0 ∂ν0 = 0 := by
  obtain ⟨C, hC, hνC⟩ := exists_compact_ae

  set F : ℝ → AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ := fun s x y => Φ (u x y * g * L i j s) with hF
  set F' : ℝ → AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ :=
    fun s x y => ((kap i j s : ℂ)⁻¹) * WhittakerBlock.archDeriv i j Φ (u x y * g * L i j s) with hF'
  have hr : (0 : ℝ) < 1 / 3 := by norm_num
  have hI : ∀ s : closedBall (0 : ℝ) (1 / 3), |(s : ℝ)| < 1 := fun s => by
    have := s.2; have h' : |(s : ℝ)| ≤ 1 / 3 := by simpa [Real.dist_eq] using this
    exact lt_of_le_of_lt h' (by norm_num)
  have hball : ∀ s ∈ ball (0 : ℝ) (1 / 3), |s| < 1 := fun s hs => by
    have h' : |s| < 1 / 3 := by simpa [Real.dist_eq] using hs
    exact lt_trans h' (by norm_num)

  have hLc : Continuous fun s : closedBall (0 : ℝ) (1 / 3) => L i j s :=
    continuousOn_iff_continuous_restrict.mp (continuousOn_L i j)
  have huq : Continuous fun q : closedBall (0 : ℝ) (1 / 3) × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) =>
      u q.2.1 q.2.2 * g * L i j q.1 :=
    (((hu.comp (continuous_snd (X := closedBall (0 : ℝ) (1 / 3))) :)).mul continuous_const).mul
      (hLc.comp (continuous_fst (Y := (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ))) :)
  have hFc : Continuous fun q : closedBall (0 : ℝ) (1 / 3) × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) =>
      F q.1 q.2.1 q.2.2 :=
    hΦc.comp huq
  have hkc : Continuous fun s : closedBall (0 : ℝ) (1 / 3) => ((kap i j s : ℂ)⁻¹) := by
    refine Continuous.inv₀ (Complex.continuous_ofReal.comp ((continuous_kap i j).comp continuous_subtype_val))
      fun s => ?_
    exact_mod_cast (kap_pos i j (hI s)).ne'
  have hF'c : Continuous fun q : closedBall (0 : ℝ) (1 / 3) × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) =>
      F' q.1 q.2.1 q.2.2 :=
    ((hkc.comp (continuous_fst (Y := (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ))) :)).mul (hΦ'c.comp huq)

  have hd : ∀ x y, ∀ s ∈ ball (0 : ℝ) (1 / 3), HasDerivAt (fun σ => F σ x y) (F' s x y) s :=
    fun x y s hs => hasDerivAt_comp_L hΦs (u x y * g) i j (hball s hs)

  have hG : ∀ x, ∀ s₀ ∈ ball (0 : ℝ) (1 / 3),
      HasDerivAt (fun s => ∫ y, F s x y ∂ν0) (∫ y, F' s₀ x y ∂ν0) s₀ := fun x =>
    hasDerivAt_integral_of_continuous ν0 hC hνC (fun s y => F s x y) (fun s y => F' s x y) hr
      (hFc.comp (continuous_fst.prodMk ((continuous_const (y := x)).prodMk continuous_snd)) :)
      (hF'c.comp (continuous_fst.prodMk ((continuous_const (y := x)).prodMk continuous_snd)) :) (fun y => hd x y)

  have hGc : Continuous fun q : closedBall (0 : ℝ) (1 / 3) × AdeleRing (𝓞 ℚ) ℚ => ∫ y, F q.1 q.2 y ∂ν0 :=
    continuous_integral_of_continuous ν0 hC hνC (fun q : closedBall (0 : ℝ) (1 / 3) × AdeleRing (𝓞 ℚ) ℚ =>
      fun y => F q.1 q.2 y) (hFc.comp ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)) :)
  have hG'c : Continuous fun q : closedBall (0 : ℝ) (1 / 3) × AdeleRing (𝓞 ℚ) ℚ => ∫ y, F' q.1 q.2 y ∂ν0 :=
    continuous_integral_of_continuous ν0 hC hνC (fun q : closedBall (0 : ℝ) (1 / 3) × AdeleRing (𝓞 ℚ) ℚ =>
      fun y => F' q.1 q.2 y) (hF'c.comp ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)) :)
  have hH : HasDerivAt (fun s => ∫ x, ∫ y, F s x y ∂ν0 ∂ν0) (∫ x, ∫ y, F' 0 x y ∂ν0 ∂ν0) 0 :=
    hasDerivAt_integral_of_continuous ν0 hC hνC (fun s x => ∫ y, F s x y ∂ν0) (fun s x => ∫ y, F' s x y ∂ν0)
      hr hGc hG'c hG 0 (mem_ball_self hr)

  have hzero : (fun s => ∫ x, ∫ y, F s x y ∂ν0 ∂ν0) = fun _ => 0 := by
    funext s
    have := hcusp (g * L i j s)
    simp only [hF, mul_assoc] at this ⊢
    exact this
  rw [hzero] at hH
  have h0 : (∫ x, ∫ y, F' 0 x y ∂ν0 ∂ν0) = 0 := hH.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ)) ▸ rfl
  have hF'0 : ∀ x y, F' 0 x y = WhittakerBlock.archDeriv i j Φ (u x y * g) := fun x y => by
    simp only [hF', L_zero, mul_one, kap, ite_self, add_zero]
    simp
  simp_rw [hF'0] at h0
  exact h0

end Cusp

section Words

theorem isArchSmooth3_sum_translate (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 f)
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (ht : ∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1) :
    WhittakerBlock.IsArchSmooth3 (fun x => ∑ i, c i * f (x * t i)) := by
  intro g
  have heq : (fun e : Fin 3 → Fin 3 → ℝ => ∑ i, c i * f (g * WhittakerBlock.archRealLift3 e * t i)) =
      fun e => ∑ i, c i * f (g * t i * WhittakerBlock.archRealLift3 e) := by
    funext e
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcomm : t i * WhittakerBlock.archRealLift3 e = WhittakerBlock.archRealLift3 e * t i :=
      commute_archRealLift3 (t i) (ht i) (Matrix.of e)
    rw [mul_assoc, ← hcomm, ← mul_assoc]
  rw [heq]
  exact ContDiffOn.sum fun i _ => contDiffOn_const.mul (hsa (g * t i))

theorem isArchSmooth3_foldr (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv : WhittakerBlock.IsArchSmooth3 v)
    (w : List (Fin 3 × Fin 3)) :
    WhittakerBlock.IsArchSmooth3 (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) v w) := by
  induction w with
  | nil => exact hv
  | cons ij w ih => exact isArchSmooth3_archDeriv ih ij.1 ij.2

end Words

section Radicals

theorem continuous_radicalP21 :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => (radicalP21 ![p.1, p.2] : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Function.comp_apply, radicalP21_coe]
    fin_cases a <;> fin_cases b <;> simp <;> fun_prop
  · have : (fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
        (((radicalP21 ![p.1, p.2] : AdelicGL 3 (𝓞 ℚ) ℚ)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) :
          Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) =
        fun p => !![1, -0, 0 * p.2 - p.1; 0, 1, -p.2; 0, 0, 1] := by
      funext p; rfl
    rw [this]
    refine continuous_pi fun a => continuous_pi fun b => ?_
    fin_cases a <;> fin_cases b <;> simp <;> fun_prop

theorem continuous_radicalP12 :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => (radicalP12 ![p.1, p.2] : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Function.comp_apply, radicalP12_coe]
    fin_cases a <;> fin_cases b <;> simp <;> fun_prop
  · have : (fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
        (((radicalP12 ![p.1, p.2] : AdelicGL 3 (𝓞 ℚ) ℚ)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) :
          Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) =
        fun p => !![1, -p.1, p.1 * 0 - p.2; 0, 1, -0; 0, 0, 1] := by
      funext p; rfl
    rw [this]
    refine continuous_pi fun a => continuous_pi fun b => ?_
    fin_cases a <;> fin_cases b <;> simp <;> fun_prop

end Radicals

end R1CuspDeriv
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top.R1CuspDeriv"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top.R1CuspDeriv"

section CentralChar

open IsDedekindDomain NumberField AutomorphicForm Filter Topology
open LanglandsTunnell.CubicInduction R1CuspDeriv

local notation "GA" => AdelicGL 3 (𝓞 ℚ) ℚ

def DS.idArr : Fin 3 → Fin 3 → ℝ := fun a b => if a = b then (1 : ℝ) else 0

theorem DS.of_idArr : Matrix.of DS.idArr = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext a b; simp [DS.idArr, Matrix.one_apply]

theorem DS.of_smul_idArr (lam : ℝ) : Matrix.of (lam • DS.idArr) = lam • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [← DS.of_idArr]; rfl

theorem DS.det_smul_idArr {lam : ℝ} (hlam : lam ≠ 0) : (Matrix.of (lam • DS.idArr)).det ≠ 0 := by
  rw [DS.of_smul_idArr, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  exact pow_ne_zero _ hlam

noncomputable def DS.scal (lam : ℝ) : GA := WhittakerBlock.archRealLift3 (lam • DS.idArr)

theorem DS.scal_one : DS.scal 1 = 1 := by
  show WhittakerBlock.archRealLift3 (Matrix.of ((1 : ℝ) • DS.idArr)) = 1
  rw [one_smul, DS.of_idArr]; exact archRealLift3_one

theorem DS.scal_mul {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) : DS.scal a * DS.scal b = DS.scal (a * b) := by
  unfold DS.scal
  rw [← archRealLift3_mul _ _ (DS.det_smul_idArr ha) (DS.det_smul_idArr hb)]
  congr 1
  show (Matrix.of (a • DS.idArr) * Matrix.of (b • DS.idArr) : Matrix (Fin 3) (Fin 3) ℝ) = Matrix.of ((a * b) • DS.idArr)
  rw [DS.of_smul_idArr, DS.of_smul_idArr, DS.of_smul_idArr, smul_mul_smul_comm, one_mul, mul_smul]

theorem DS.sum_mulE_idArr : ∑ i : Fin 3, mulE i i DS.idArr = DS.idArr := by
  funext a b
  simp only [Finset.sum_apply, mulE_eq, DS.idArr, Fin.sum_univ_three]
  fin_cases a <;> fin_cases b <;> simp

theorem DS.casimir1_eq_fderiv {u : GA → ℂ} (hsa : WhittakerBlock.IsArchSmooth3 u) (g : GA) :
    WhittakerBlock.casimir1 u g =
      fderiv ℝ (fun e' : Fin 3 → Fin 3 → ℝ => u (g * WhittakerBlock.archRealLift3 e')) DS.idArr DS.idArr := by
  have hid : DS.idArr ∈ U := by
    show (Matrix.of DS.idArr).det ≠ 0
    rw [DS.of_idArr, Matrix.det_one]; exact one_ne_zero
  have hg : g = g * WhittakerBlock.archRealLift3 DS.idArr := by
    rw [show WhittakerBlock.archRealLift3 DS.idArr = WhittakerBlock.archRealLift3 (Matrix.of DS.idArr) from rfl,
      DS.of_idArr, archRealLift3_one, mul_one]
  show ∑ i : Fin 3, WhittakerBlock.archDeriv i i u g = _
  conv_lhs => arg 2; ext i; rw [hg, archDeriv_slice_eq hsa g i i hid]
  rw [← map_sum, DS.sum_mulE_idArr]

theorem DS.apply_mul_scal {u : GA → ℂ} (hsa : WhittakerBlock.IsArchSmooth3 u) {c₁ : ℂ}
    (hc₁ : WhittakerBlock.casimir1 u = c₁ • u) {lam : ℝ} (hlam : 0 < lam) (g : GA) :
    u (g * DS.scal lam) = ((lam : ℝ) : ℂ) ^ c₁ * u g := by
  set F : ℝ → ℂ := fun μ => u (g * DS.scal μ) with hF
  have hslice : ∀ {μ : ℝ}, 0 < μ →
      HasDerivAt F (μ⁻¹ • fderiv ℝ (fun e' : Fin 3 → Fin 3 → ℝ =>
        u (g * DS.scal μ * WhittakerBlock.archRealLift3 e')) DS.idArr DS.idArr) μ := by
    intro μ hμ
    have hev : F =ᶠ[𝓝 μ] fun ν => (fun e' : Fin 3 → Fin 3 → ℝ => u (g * DS.scal μ * WhittakerBlock.archRealLift3 e'))
        ((μ⁻¹ * ν) • DS.idArr) := by
      have hnb : Set.Ioi (0 : ℝ) ∈ 𝓝 μ := isOpen_Ioi.mem_nhds hμ
      filter_upwards [hnb] with ν hν
      have hsc : DS.scal μ * DS.scal (μ⁻¹ * ν) = DS.scal ν := by
        rw [DS.scal_mul hμ.ne' (mul_ne_zero (inv_ne_zero hμ.ne') (ne_of_gt hν)), ← mul_assoc,
          mul_inv_cancel₀ hμ.ne', one_mul]
      show u (g * DS.scal ν) = u (g * DS.scal μ * DS.scal (μ⁻¹ * ν))
      rw [mul_assoc, hsc]
    refine HasDerivAt.congr_of_eventuallyEq ?_ hev
    have hid : DS.idArr ∈ U := by
      show (Matrix.of DS.idArr).det ≠ 0
      rw [DS.of_idArr, Matrix.det_one]; exact one_ne_zero
    have hcurve : HasDerivAt (fun ν : ℝ => (μ⁻¹ * ν) • DS.idArr) (μ⁻¹ • DS.idArr) μ := by
      have h := ((hasDerivAt_id μ).const_mul μ⁻¹).smul_const DS.idArr
      simpa using h
    have hD := differentiableAt_slice hsa (g * DS.scal μ) hid
    have hpt : (fun ν : ℝ => (μ⁻¹ * ν) • DS.idArr) μ = DS.idArr := by
      show (μ⁻¹ * μ) • DS.idArr = DS.idArr
      rw [inv_mul_cancel₀ hμ.ne', one_smul]
    have hD' : HasFDerivAt (fun e' : Fin 3 → Fin 3 → ℝ => u (g * DS.scal μ * WhittakerBlock.archRealLift3 e'))
        (fderiv ℝ (fun e' : Fin 3 → Fin 3 → ℝ => u (g * DS.scal μ * WhittakerBlock.archRealLift3 e')) DS.idArr)
        ((fun ν : ℝ => (μ⁻¹ * ν) • DS.idArr) μ) := by
      rw [hpt]; exact hD.hasFDerivAt
    have hcomp := hD'.comp_hasDerivAt μ hcurve
    rw [map_smul] at hcomp
    exact hcomp
  have hODE : ∀ {μ : ℝ}, 0 < μ → HasDerivAt F ((μ : ℂ)⁻¹ * (c₁ * F μ)) μ := by
    intro μ hμ
    have h := hslice hμ
    have hcas := DS.casimir1_eq_fderiv hsa (g * DS.scal μ)
    rw [hc₁, Pi.smul_apply, smul_eq_mul] at hcas
    rw [← hcas, Complex.real_smul, Complex.ofReal_inv] at h
    exact h
  set H : ℝ → ℂ := fun x => Complex.exp (-(c₁ * x)) * F (Real.exp x) with hH
  have hHd : ∀ x, HasDerivAt H 0 x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => Complex.exp (-(c₁ * x))) (Complex.exp (-(c₁ * x)) * (-c₁)) x := by
      have := ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c₁).neg.cexp
      simpa [mul_comm] using this
    have h2 : HasDerivAt (fun x : ℝ => F (Real.exp x))
        (Real.exp x • (((Real.exp x : ℝ) : ℂ)⁻¹ * (c₁ * F (Real.exp x)))) x :=
      (hODE (Real.exp_pos x)).scomp x (Real.hasDerivAt_exp x)
    have h := h1.fun_mul h2
    have hex : ((Real.exp x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos x).ne'
    convert h using 1
    all_goals try rfl
    rw [Complex.real_smul]
    field_simp
    ring
  have hHconst : ∀ x, H x = H 0 := fun x =>
    is_const_of_deriv_eq_zero (fun x => (hHd x).differentiableAt) (fun x => (hHd x).deriv) x 0
  have hmain := hHconst (Real.log lam)
  simp only [hH, Real.exp_log hlam, Real.exp_zero, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero,
    one_mul] at hmain
  have hF1 : F 1 = u g := by simp [hF, DS.scal_one]
  rw [hF1] at hmain
  have hcpow : ((lam : ℝ) : ℂ) ^ c₁ = Complex.exp (c₁ * Real.log lam) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hlam.ne'), ← Complex.ofReal_log hlam.le, mul_comm]
  calc u (g * DS.scal lam) = F lam := rfl
    _ = Complex.exp (c₁ * Real.log lam) * (Complex.exp (-(c₁ * Real.log lam)) * F lam) := by
        rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
    _ = ((lam : ℝ) : ℂ) ^ c₁ * u g := by rw [hmain, hcpow]

end CentralChar
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top.R1CuspDeriv"

section Translation

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory NumberField.StandardAddChar
open LanglandsTunnell.CubicInduction R1CuspDeriv

local notation "GA" => AdelicGL 3 (𝓞 ℚ) ℚ
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "Wh" => whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
  NumberField.StandardAddChar.psiQ

noncomputable def DS.ofR (a : ℝ) : 𝔸 := (ofRealHom a, 0)

theorem DS.ofR_add (a b : ℝ) : DS.ofR a + DS.ofR b = DS.ofR (a + b) := by
  refine Prod.ext ?_ ?_
  · show ofRealHom a + ofRealHom b = ofRealHom (a + b); rw [map_add]
  · show (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) + 0 = 0; rw [add_zero]

noncomputable def DS.cA (lam : ℝ) : 𝔸 := (ofRealHom lam, 1)

theorem DS.psiQ_ofR (a : ℝ) : psiQ (DS.ofR a) = Complex.exp (2 * Real.pi * Complex.I * a) := by
  rw [psiQ_apply]
  show psiArch (ofRealHom a) * psiFin 0 = _
  rw [AddChar.map_zero_eq_one, mul_one, psiArch_apply, finprod_unique, psiArchPlace_apply]
  congr 2
  show (((InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal _))
      ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal _)).symm a) : ℝ) : ℂ) = (a : ℂ)
  congr 1
  exact RingEquiv.apply_symm_apply (InfinitePlace.Completion.ringEquivRealOfIsReal _) a

theorem DS.archRealMat3_apply (e : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    WhittakerBlock.archRealMat3 e i j = ((ofRealHom (e i j), (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : 𝔸) :=
  rfl

theorem DS.mul_scal_comm {lam : ℝ} (hlam : lam ≠ 0) (x : GA) : x * DS.scal lam = DS.scal lam * x := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  have hc : ((DS.scal lam : GA) : Matrix (Fin 3) (Fin 3) 𝔸) = DS.cA lam • (1 : Matrix (Fin 3) (Fin 3) 𝔸) := by
    show ((WhittakerBlock.archRealLift3 (Matrix.of (lam • DS.idArr)) : GA) : Matrix (Fin 3) (Fin 3) 𝔸) = _
    rw [coe_archRealLift3 _ (DS.det_smul_idArr hlam)]
    ext i j
    rw [DS.archRealMat3_apply, Matrix.smul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply, Pi.smul_apply, DS.idArr, smul_eq_mul]
    by_cases hij : i = j
    · subst hij; simp [Matrix.one_apply_eq, DS.cA]
    · simp [Matrix.one_apply_ne hij, hij, DS.cA]; rfl
  rw [hc, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]

theorem DS.whittaker3_mul_scal {u : GA → ℂ} (hsa : WhittakerBlock.IsArchSmooth3 u) {c₁ : ℂ}
    (hc₁ : WhittakerBlock.casimir1 u = c₁ • u) {lam : ℝ} (hlam : 0 < lam) (x : GA) :
    Wh u (x * DS.scal lam) = ((lam : ℝ) : ℂ) ^ c₁ * Wh u x := by
  unfold whittaker3
  simp only [← mul_assoc]
  simp_rw [show ∀ (a b c : 𝔸), u (upperUnipotent3 a b c * x * DS.scal lam) * psiQ (-(a + b)) =
      ((lam : ℝ) : ℂ) ^ c₁ * (u (upperUnipotent3 a b c * x) * psiQ (-(a + b))) from
    fun a b c => by rw [DS.apply_mul_scal hsa hc₁ hlam, mul_assoc]]
  simp_rw [integral_const_mul]

noncomputable def DS.dArr (y₁ y₂ : ℝ) : Fin 3 → Fin 3 → ℝ := fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0

theorem DS.det_dArr {y₁ y₂ : ℝ} (h₁ : y₁ ≠ 0) (h₂ : y₂ ≠ 0) : (Matrix.of (DS.dArr y₁ y₂)).det ≠ 0 := by
  rw [Matrix.det_fin_three]
  simp [DS.dArr, h₁, h₂]

noncomputable def DS.nArr (t : Fin 3 → Fin 3 → ℝ) (y₁ y₂ : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j => (!![1, y₁ * t 0 1 / t 1 1, y₁ * y₂ * t 0 2 / t 2 2; 0, 1, y₂ * t 1 2 / t 2 2; 0, 0, 1] :
    Matrix (Fin 3) (Fin 3) ℝ) i j

theorem DS.det_nArr (t : Fin 3 → Fin 3 → ℝ) (y₁ y₂ : ℝ) : (Matrix.of (DS.nArr t y₁ y₂)).det ≠ 0 := by
  rw [Matrix.det_fin_three]
  simp [DS.nArr]

theorem DS.archRealLift3_nArr (t : Fin 3 → Fin 3 → ℝ) (y₁ y₂ : ℝ) :
    WhittakerBlock.archRealLift3 (DS.nArr t y₁ y₂) =
      upperUnipotent3 (DS.ofR (y₁ * t 0 1 / t 1 1)) (DS.ofR (y₂ * t 1 2 / t 2 2)) (DS.ofR (y₁ * y₂ * t 0 2 / t 2 2)) := by
  apply Units.ext
  rw [show WhittakerBlock.archRealLift3 (DS.nArr t y₁ y₂) = WhittakerBlock.archRealLift3 (Matrix.of (DS.nArr t y₁ y₂))
    from rfl, coe_archRealLift3 _ (DS.det_nArr t y₁ y₂)]
  ext i j
  rw [DS.archRealMat3_apply]
  fin_cases i <;> fin_cases j <;>
    simp [DS.nArr, DS.ofR, upperUnipotent3] <;> rfl

theorem DS.of_dArr_mul_of (t : Fin 3 → Fin 3 → ℝ) (ht : ∀ i j : Fin 3, j < i → t i j = 0)
    (hpos : ∀ i : Fin 3, 0 < t i i) {y₁ y₂ : ℝ} :
    Matrix.of (DS.dArr y₁ y₂) * Matrix.of t =
      Matrix.of (DS.nArr t y₁ y₂) *
        (Matrix.of (DS.dArr (y₁ * t 0 0 / t 1 1) (y₂ * t 1 1 / t 2 2)) * Matrix.of (t 2 2 • DS.idArr)) := by
  have h10 : t 1 0 = 0 := ht 1 0 (by decide)
  have h20 : t 2 0 = 0 := ht 2 0 (by decide)
  have h21 : t 2 1 = 0 := ht 2 1 (by decide)
  have h1 : t 1 1 ≠ 0 := (hpos 1).ne'
  have h2 : t 2 2 ≠ 0 := (hpos 2).ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, DS.dArr, DS.nArr, DS.idArr, h10, h20, h21] <;>
    field_simp

theorem DS.whittaker3_dArr_mul_upperTriangular {u : GA → ℂ}
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : GA), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g)
    (hsa : WhittakerBlock.IsArchSmooth3 u) {c₁ : ℂ} (hc₁ : WhittakerBlock.casimir1 u = c₁ • u)
    (t : Fin 3 → Fin 3 → ℝ) (ht : ∀ i j : Fin 3, j < i → t i j = 0) (hpos : ∀ i : Fin 3, 0 < t i i)
    {y₁ y₂ : ℝ} (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (g : GA) :
    Wh u (WhittakerBlock.archRealLift3 (DS.dArr y₁ y₂) * WhittakerBlock.archRealLift3 t * g) =
      Complex.exp (2 * Real.pi * Complex.I * ((y₁ * t 0 1 / t 1 1 + y₂ * t 1 2 / t 2 2 : ℝ) : ℂ)) *
        ((t 2 2 : ℝ) : ℂ) ^ c₁ *
        Wh u (WhittakerBlock.archRealLift3 (DS.dArr (y₁ * t 0 0 / t 1 1) (y₂ * t 1 1 / t 2 2)) * g) := by
  have hdetT : (Matrix.of t).det ≠ 0 := by
    have h := Matrix.det_of_upperTriangular (M := Matrix.of t) (fun i j hij => ht i j hij)
    rw [h]
    exact Finset.prod_ne_zero_iff.2 fun i _ => (hpos i).ne'
  have hy₁' : 0 < y₁ * t 0 0 / t 1 1 := by have := hpos 0; have := hpos 1; positivity
  have hy₂' : 0 < y₂ * t 1 1 / t 2 2 := by have := hpos 1; have := hpos 2; positivity
  have hprod : WhittakerBlock.archRealLift3 (DS.dArr y₁ y₂) * WhittakerBlock.archRealLift3 t =
      WhittakerBlock.archRealLift3 (DS.nArr t y₁ y₂) *
        (WhittakerBlock.archRealLift3 (DS.dArr (y₁ * t 0 0 / t 1 1) (y₂ * t 1 1 / t 2 2)) * DS.scal (t 2 2)) := by
    rw [DS.scal, ← archRealLift3_mul _ _ (DS.det_dArr hy₁'.ne' hy₂'.ne') (DS.det_smul_idArr (hpos 2).ne'),
      ← archRealLift3_mul _ _ (DS.det_nArr t y₁ y₂) (by
        rw [show (Matrix.of (Matrix.of (DS.dArr (y₁ * t 0 0 / t 1 1) (y₂ * t 1 1 / t 2 2)) *
            Matrix.of (t 2 2 • DS.idArr)) : Matrix (Fin 3) (Fin 3) ℝ) =
            Matrix.of (DS.dArr (y₁ * t 0 0 / t 1 1) (y₂ * t 1 1 / t 2 2)) * Matrix.of (t 2 2 • DS.idArr) from rfl,
          Matrix.det_mul]
        exact mul_ne_zero (DS.det_dArr hy₁'.ne' hy₂'.ne') (DS.det_smul_idArr (hpos 2).ne')),
      ← archRealLift3_mul _ _ (DS.det_dArr hy₁.ne' hy₂.ne') hdetT]
    congr 1
    exact DS.of_dArr_mul_of t ht hpos
  rw [hprod, DS.archRealLift3_nArr, mul_assoc, mul_assoc,
    (whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul u haut).1,
    DS.ofR_add, DS.psiQ_ofR, mul_assoc (WhittakerBlock.archRealLift3 _) (DS.scal _) g,
    ← DS.mul_scal_comm (hpos 2).ne' g, ← mul_assoc, DS.whittaker3_mul_scal hsa hc₁ (hpos 2), ← mul_assoc]

end Translation
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top.R1CuspDeriv"

section Slot

open Finset

noncomputable def DS.term (e : ℂ) (m : ℕ) (y : ℝ) : ℂ := ((y : ℝ) : ℂ) ^ e * ((Real.log y : ℝ) : ℂ) ^ m

noncomputable def DS.transport {n J : ℕ} (σ : ℝ) (e : Fin n → ℂ) (c : Fin n → Fin J → ℂ)
    (i : Fin n) (m : Fin J) : ℂ :=
  ∑ j : Fin J, (if (m : ℕ) ≤ (j : ℕ) then (((j : ℕ).choose m : ℕ) : ℂ) * ((Real.log σ : ℝ) : ℂ) ^ ((j : ℕ) - m)
    else 0) * ((((σ : ℝ) : ℂ) ^ e i) * c i j)

theorem DS.sum_range_eq_sum_fin_ite {M : Type*} [AddCommMonoid M] {J : ℕ} (j : Fin J) (f : ℕ → M) :
    ∑ m ∈ range ((j : ℕ) + 1), f m = ∑ m : Fin J, if (m : ℕ) ≤ (j : ℕ) then f m else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun m => if m ≤ (j : ℕ) then f m else 0) J, ← Finset.sum_filter]
  congr 1
  ext m
  simp only [mem_range, mem_filter]
  constructor
  · intro h; exact ⟨lt_of_le_of_lt (Nat.lt_succ_iff.1 h) j.2, Nat.lt_succ_iff.1 h⟩
  · intro h; exact Nat.lt_succ_iff.2 h.2

theorem DS.sum_term_mul {n J : ℕ} {σ y : ℝ} (hσ : 0 < σ) (hy : 0 < y) (e : Fin n → ℂ)
    (c : Fin n → Fin J → ℂ) :
    ∑ i, ∑ j, c i j * DS.term (e i) j (σ * y) = ∑ i, ∑ m, DS.transport σ e c i m * DS.term (e i) m y := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpow : (((σ * y : ℝ) : ℂ)) ^ e i = ((σ : ℝ) : ℂ) ^ e i * ((y : ℝ) : ℂ) ^ e i := by
    push_cast
    exact Complex.mul_cpow_ofReal_nonneg hσ.le hy.le (e i)
  have hlog : ((Real.log (σ * y) : ℝ) : ℂ) = ((Real.log y : ℝ) : ℂ) + ((Real.log σ : ℝ) : ℂ) := by
    rw [Real.log_mul hσ.ne' hy.ne']; push_cast; ring

  have hj : ∀ j : Fin J, c i j * DS.term (e i) j (σ * y) =
      ∑ m : Fin J, (if (m : ℕ) ≤ (j : ℕ) then (((j : ℕ).choose m : ℕ) : ℂ) *
        ((Real.log σ : ℝ) : ℂ) ^ ((j : ℕ) - m) else 0) * ((((σ : ℝ) : ℂ) ^ e i) * c i j) * DS.term (e i) m y := by
    intro j
    simp only [DS.term]
    rw [hpow, hlog, add_pow, Finset.mul_sum, Finset.mul_sum]
    rw [DS.sum_range_eq_sum_fin_ite j]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : (m : ℕ) ≤ (j : ℕ)
    · simp only [if_pos hm]; ring
    · simp only [if_neg hm, zero_mul]
  simp_rw [hj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [DS.transport, Finset.sum_mul]

theorem DS.transport_top {n J : ℕ} (σ : ℝ) (e : Fin n → ℂ) (c : Fin n → Fin J → ℂ) (i₀ : Fin n)
    (j₀ : Fin J) (htop : ∀ j : Fin J, (j₀ : ℕ) < (j : ℕ) → c i₀ j = 0) :
    DS.transport σ e c i₀ j₀ = ((σ : ℝ) : ℂ) ^ e i₀ * c i₀ j₀ := by
  rw [DS.transport, Finset.sum_eq_single j₀]
  · simp
  · intro j _ hj
    rcases lt_or_gt_of_ne (fun h : (j : ℕ) = (j₀ : ℕ) => hj (Fin.ext h)) with h | h
    · rw [if_neg (not_le.2 h), zero_mul]
    · rw [htop j h, mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem DS.abs_log_pow_mul_rpow_half_le (j : ℕ) {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) :
    |Real.log w| ^ j * w ^ (1 / 2 : ℝ) ≤ (2 * ((j : ℝ) + 1)) ^ j := by
  have ht : (0 : ℝ) < 1 / (2 * ((j : ℝ) + 1)) := by positivity
  have h1 : |Real.log w| * w ^ (1 / (2 * ((j : ℝ) + 1))) ≤ 2 * ((j : ℝ) + 1) := by
    have h := (Real.abs_log_mul_self_rpow_lt w _ hw hw1 ht).le
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hw.le _), one_div_one_div] at h
    exact h
  have h2 : w ^ (1 / 2 : ℝ) ≤ w ^ ((j : ℝ) * (1 / (2 * ((j : ℝ) + 1)))) := by
    apply Real.rpow_le_rpow_of_exponent_ge hw hw1
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith
  calc |Real.log w| ^ j * w ^ (1 / 2 : ℝ)
      ≤ |Real.log w| ^ j * w ^ ((j : ℝ) * (1 / (2 * ((j : ℝ) + 1)))) :=
        mul_le_mul_of_nonneg_left h2 (pow_nonneg (abs_nonneg _) _)
    _ = (|Real.log w| * w ^ (1 / (2 * ((j : ℝ) + 1)))) ^ j := by
        rw [mul_pow, ← Real.rpow_natCast (w ^ _) j, ← Real.rpow_mul hw.le, mul_comm (1 / _)]
    _ ≤ (2 * ((j : ℝ) + 1)) ^ j :=
        pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hw.le _)) h1 j

theorem DS.norm_term_le {e : ℂ} {r₀ : ℝ} (he : r₀ ≤ e.re) (m : ℕ) {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) :
    ‖DS.term e m w‖ ≤ (2 * ((m : ℝ) + 1)) ^ m * w ^ (r₀ - 1 / 2) := by
  rw [DS.term, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hw, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have h1 : w ^ e.re ≤ w ^ r₀ := Real.rpow_le_rpow_of_exponent_ge hw hw1 he
  have h2 := DS.abs_log_pow_mul_rpow_half_le m hw hw1
  have hsplit : w ^ r₀ = w ^ (r₀ - 1 / 2) * w ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hw]; ring_nf
  calc w ^ e.re * |Real.log w| ^ m ≤ w ^ r₀ * |Real.log w| ^ m :=
        mul_le_mul_of_nonneg_right h1 (pow_nonneg (abs_nonneg _) _)
    _ = w ^ (r₀ - 1 / 2) * (|Real.log w| ^ m * w ^ (1 / 2 : ℝ)) := by rw [hsplit]; ring
    _ ≤ w ^ (r₀ - 1 / 2) * (2 * ((m : ℝ) + 1)) ^ m :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hw.le _)
    _ = (2 * ((m : ℝ) + 1)) ^ m * w ^ (r₀ - 1 / 2) := mul_comm _ _

theorem DS.slot {n J : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) (τ : ℝ)
    (i₀ : Fin n) (hτ : (e i₀).re < τ) (j₀ : Fin J)
    (a b : Fin n → Fin J → ℂ)
    (hbot : ∀ (i : Fin n) (j : Fin J), (e i).re < (e i₀).re → b i j = 0)
    (hloga : ∀ j : Fin J, (j₀ : ℕ) < (j : ℕ) → a i₀ j = 0) (hlogb : ∀ j : Fin J, (j₀ : ℕ) < (j : ℕ) → b i₀ j = 0)
    (F G : ℝ → ℂ) (ρ : ℝ) (hρ : 0 < ρ) (Λ : ℂ) (κ : ℝ)
    (hF : ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖F y - ∑ i, ∑ j, a i j * DS.term (e i) j y‖ ≤ C * y ^ τ)
    (hG : ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖G y - ∑ i, ∑ j, b i j * DS.term (e i) j y‖ ≤ C * y ^ τ)
    (hFG : ∀ y : ℝ, 0 < y → F y = Complex.exp (2 * Real.pi * Complex.I * ((κ * y : ℝ) : ℂ)) * Λ * G (ρ * y)) :
    a i₀ j₀ = Λ * ((ρ : ℝ) : ℂ) ^ e i₀ * b i₀ j₀ := by
  classical
  obtain ⟨CF, hCF⟩ := hF
  obtain ⟨CG, hCG⟩ := hG
  set r₀ : ℝ := (e i₀).re with hr₀
  set η : ℝ := min (1 / 2) ((τ - r₀) / 2) with hη
  have hη0 : 0 < η := lt_min (by norm_num) (by linarith)
  have hη1 : η ≤ 1 / 2 := min_le_left _ _
  have hη2 : η ≤ (τ - r₀) / 2 := min_le_right _ _
  set θ₀ : ℝ := r₀ + η with hθ₀
  have hθτ : θ₀ ≤ τ := by linarith
  have hθr : r₀ < θ₀ := by linarith
  have hθh : θ₀ ≤ r₀ + 1 / 2 := by linarith

  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = min 1 ρ⁻¹ := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; exact lt_min one_pos (inv_pos.2 hρ)
  have hs1 : s ≤ 1 := by rw [hs]; exact min_le_left _ _
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = s * ρ := ⟨_, rfl⟩
  have hσ0 : 0 < σ := by rw [hσ]; exact mul_pos hs0 hρ
  have hσ1 : σ ≤ 1 := by
    rw [hσ]
    calc s * ρ ≤ ρ⁻¹ * ρ := mul_le_mul_of_nonneg_right (by rw [hs]; exact min_le_right _ _) hρ.le
      _ = 1 := inv_mul_cancel₀ hρ.ne'

  set A := DS.transport s e a with hA
  set B := DS.transport σ e b with hB
  set cc : Fin n × Fin J → ℂ := fun p => A p.1 p.2 - Λ * B p.1 p.2 with hcc
  set Rf : ℝ → ℂ := fun y => -∑ p : Fin n × Fin J, cc p * DS.term (e p.1) p.2 y with hRf

  have hkey : ∀ y : ℝ, 0 < y → y ≤ 1 →
      ∑ p : Fin n × Fin J, cc p * DS.term (e p.1) p.2 y =
        (Complex.exp (2 * Real.pi * Complex.I * ((κ * (s * y) : ℝ) : ℂ)) - 1) * Λ * G (σ * y) -
          (F (s * y) - ∑ i, ∑ j, a i j * DS.term (e i) j (s * y)) +
          Λ * (G (σ * y) - ∑ i, ∑ j, b i j * DS.term (e i) j (σ * y)) := by
    intro y hy hy1
    have h1 : ∑ p : Fin n × Fin J, cc p * DS.term (e p.1) p.2 y =
        ∑ i, ∑ m, A i m * DS.term (e i) m y - Λ * ∑ i, ∑ m, B i m * DS.term (e i) m y := by
      simp only [hcc, sub_mul, Finset.sum_sub_distrib, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
    rw [h1, hA, hB, ← DS.sum_term_mul hs0 hy e a, ← DS.sum_term_mul hσ0 hy e b, hFG (s * y) (mul_pos hs0 hy),
      show ρ * (s * y) = σ * y by rw [hσ]; ring]
    ring

  set Mb : ℝ := ∑ i : Fin n, ∑ j : Fin J, ‖b i j‖ * (2 * ((j : ℕ) : ℝ) + 1 + 1) ^ (j : ℕ) with hMb
  have hGbound : ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖G (σ * y)‖ ≤ (∑ i : Fin n, ∑ j : Fin J, ‖b i j‖ * (2 * (((j : ℕ) : ℝ) + 1)) ^ (j : ℕ) + |CG|) *
        (σ * y) ^ (r₀ - 1 / 2) := by
    intro y hy hy1
    have hw : 0 < σ * y := mul_pos hσ0 hy
    have hw1 : σ * y ≤ 1 := by nlinarith
    have hR := hCG (σ * y) hw hw1
    have hmain : ‖∑ i, ∑ j, b i j * DS.term (e i) j (σ * y)‖ ≤
        (∑ i : Fin n, ∑ j : Fin J, ‖b i j‖ * (2 * (((j : ℕ) : ℝ) + 1)) ^ (j : ℕ)) * (σ * y) ^ (r₀ - 1 / 2) := by
      rw [Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      by_cases hi : (e i).re < r₀
      · rw [hbot i j hi, zero_mul, norm_zero]; positivity
      · rw [norm_mul]
        calc ‖b i j‖ * ‖DS.term (e i) j (σ * y)‖ ≤ ‖b i j‖ * ((2 * (((j : ℕ) : ℝ) + 1)) ^ (j : ℕ) * (σ * y) ^ (r₀ - 1 / 2)) :=
              mul_le_mul_of_nonneg_left (DS.norm_term_le (not_lt.1 hi) j hw hw1) (norm_nonneg _)
          _ = _ := by ring
    have htail : ‖G (σ * y) - ∑ i, ∑ j, b i j * DS.term (e i) j (σ * y)‖ ≤ |CG| * (σ * y) ^ (r₀ - 1 / 2) := by
      refine hR.trans ?_
      calc CG * (σ * y) ^ τ ≤ |CG| * (σ * y) ^ τ :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hw.le _)
        _ ≤ |CG| * (σ * y) ^ (r₀ - 1 / 2) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hw hw1 (by linarith)) (abs_nonneg _)
    calc ‖G (σ * y)‖ = ‖∑ i, ∑ j, b i j * DS.term (e i) j (σ * y) +
          (G (σ * y) - ∑ i, ∑ j, b i j * DS.term (e i) j (σ * y))‖ := by rw [add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add hmain htail
      _ = _ := by ring
  set CB : ℝ := ∑ i : Fin n, ∑ j : Fin J, ‖b i j‖ * (2 * (((j : ℕ) : ℝ) + 1)) ^ (j : ℕ) + |CG| with hCB
  have hCB0 : 0 ≤ CB := by positivity

  have huniq := LanglandsTunnell.CubicInduction.expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow
    (fun p : Fin n × Fin J => e p.1) (fun p => (p.2 : ℕ)) cc
    (fun p q h => by
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      exact Prod.ext (he h1) (Fin.ext h2))
    θ₀ (fun _ => 0) Rf
    (fun y hy hy1 => by simp only [hRf, DS.term]; rw [add_neg_cancel])
    ⟨2 * Real.pi * |κ| * s * ‖Λ‖ * CB * σ ^ (r₀ - 1 / 2) + |CF| * s ^ τ + ‖Λ‖ * |CG| * σ ^ τ,
      fun y hy hy1 => by
        rw [hRf, norm_neg, hkey y hy hy1]
        have hsy : 0 < s * y := mul_pos hs0 hy
        have hsy1 : s * y ≤ 1 := by nlinarith
        have hσy : 0 < σ * y := mul_pos hσ0 hy
        have hσy1 : σ * y ≤ 1 := by nlinarith
        have hph : ‖Complex.exp (2 * Real.pi * Complex.I * ((κ * (s * y) : ℝ) : ℂ)) - 1‖ ≤ 2 * Real.pi * |κ| * s * y := by
          have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * (κ * (s * y)))
          rw [show Complex.I * ((2 * Real.pi * (κ * (s * y)) : ℝ) : ℂ) =
              2 * Real.pi * Complex.I * ((κ * (s * y) : ℝ) : ℂ) by push_cast; ring] at h
          refine h.trans (le_of_eq ?_)
          rw [Real.norm_eq_abs, show 2 * Real.pi * (κ * (s * y)) = κ * (2 * Real.pi * s * y) by ring, abs_mul,
            abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi * s * y)]
          ring
        have hyθ : ∀ {x : ℝ}, θ₀ ≤ x → y ^ x ≤ y ^ θ₀ := fun hx => Real.rpow_le_rpow_of_exponent_ge hy hy1 hx
        have t1 : ‖(Complex.exp (2 * Real.pi * Complex.I * ((κ * (s * y) : ℝ) : ℂ)) - 1) * Λ * G (σ * y)‖ ≤
            2 * Real.pi * |κ| * s * ‖Λ‖ * CB * σ ^ (r₀ - 1 / 2) * y ^ θ₀ := by
          rw [norm_mul, norm_mul]
          calc ‖Complex.exp (2 * Real.pi * Complex.I * ((κ * (s * y) : ℝ) : ℂ)) - 1‖ * ‖Λ‖ * ‖G (σ * y)‖
              ≤ (2 * Real.pi * |κ| * s * y) * ‖Λ‖ * (CB * (σ * y) ^ (r₀ - 1 / 2)) := by
                apply mul_le_mul (mul_le_mul_of_nonneg_right hph (norm_nonneg _)) (hGbound y hy hy1)
                  (norm_nonneg _) (by positivity)
            _ = 2 * Real.pi * |κ| * s * ‖Λ‖ * CB * σ ^ (r₀ - 1 / 2) * y ^ (r₀ + 1 / 2) := by
                rw [Real.mul_rpow hσ0.le hy.le,
                  show y ^ (r₀ + 1 / 2) = y * y ^ (r₀ - 1 / 2) by
                    rw [show r₀ + 1 / 2 = 1 + (r₀ - 1 / 2) by ring, Real.rpow_add hy, Real.rpow_one]]
                ring
            _ ≤ 2 * Real.pi * |κ| * s * ‖Λ‖ * CB * σ ^ (r₀ - 1 / 2) * y ^ θ₀ :=
                mul_le_mul_of_nonneg_left (hyθ hθh) (by positivity)
        have t2 : ‖F (s * y) - ∑ i, ∑ j, a i j * DS.term (e i) j (s * y)‖ ≤ |CF| * s ^ τ * y ^ θ₀ := by
          refine (hCF (s * y) hsy hsy1).trans ?_
          rw [Real.mul_rpow hs0.le hy.le]
          calc CF * (s ^ τ * y ^ τ) ≤ |CF| * (s ^ τ * y ^ τ) :=
                mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
            _ ≤ |CF| * (s ^ τ * y ^ θ₀) := by
                apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
                exact mul_le_mul_of_nonneg_left (hyθ hθτ) (by positivity)
            _ = _ := by ring
        have t3 : ‖Λ * (G (σ * y) - ∑ i, ∑ j, b i j * DS.term (e i) j (σ * y))‖ ≤ ‖Λ‖ * |CG| * σ ^ τ * y ^ θ₀ := by
          rw [norm_mul]
          refine (mul_le_mul_of_nonneg_left (hCG (σ * y) hσy hσy1) (norm_nonneg _)).trans ?_
          rw [Real.mul_rpow hσ0.le hy.le]
          calc ‖Λ‖ * (CG * (σ ^ τ * y ^ τ)) ≤ ‖Λ‖ * (|CG| * (σ ^ τ * y ^ τ)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
                  (norm_nonneg _)
            _ ≤ ‖Λ‖ * (|CG| * (σ ^ τ * y ^ θ₀)) := by
                apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
                apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
                exact mul_le_mul_of_nonneg_left (hyθ hθτ) (by positivity)
            _ = _ := by ring
        calc _ ≤ ‖(Complex.exp (2 * Real.pi * Complex.I * ((κ * (s * y) : ℝ) : ℂ)) - 1) * Λ * G (σ * y) -
              (F (s * y) - ∑ i, ∑ j, a i j * DS.term (e i) j (s * y))‖ +
              ‖Λ * (G (σ * y) - ∑ i, ∑ j, b i j * DS.term (e i) j (σ * y))‖ := norm_add_le _ _
          _ ≤ (‖(Complex.exp (2 * Real.pi * Complex.I * ((κ * (s * y) : ℝ) : ℂ)) - 1) * Λ * G (σ * y)‖ +
              ‖F (s * y) - ∑ i, ∑ j, a i j * DS.term (e i) j (s * y)‖) +
              ‖Λ * (G (σ * y) - ∑ i, ∑ j, b i j * DS.term (e i) j (σ * y))‖ :=
            add_le_add (norm_sub_le _ _) le_rfl
          _ ≤ _ := add_le_add (add_le_add t1 t2) t3
          _ = _ := by ring⟩
    ⟨0, fun y _ _ => by simp⟩
    (i₀, j₀) hθr

  have hA0 : A i₀ j₀ = ((s : ℝ) : ℂ) ^ e i₀ * a i₀ j₀ := DS.transport_top s e a i₀ j₀ hloga
  have hB0 : B i₀ j₀ = ((σ : ℝ) : ℂ) ^ e i₀ * b i₀ j₀ := DS.transport_top σ e b i₀ j₀ hlogb
  have hσpow : ((σ : ℝ) : ℂ) ^ e i₀ = ((s : ℝ) : ℂ) ^ e i₀ * ((ρ : ℝ) : ℂ) ^ e i₀ := by
    rw [hσ]; push_cast; exact Complex.mul_cpow_ofReal_nonneg hs0.le hρ.le _
  have hs_ne : ((s : ℝ) : ℂ) ^ e i₀ ≠ 0 :=
    Complex.cpow_ne_zero_iff.2 (Or.inl (by exact_mod_cast hs0.ne'))
  have h0 : cc (i₀, j₀) = 0 := huniq
  simp only [hcc] at h0
  rw [sub_eq_zero, hA0, hB0, hσpow] at h0
  apply mul_left_cancel₀ hs_ne
  rw [h0]; ring

end Slot
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top.R1CuspDeriv"

section Main

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory NumberField.StandardAddChar
open LanglandsTunnell.CubicInduction R1CuspDeriv

local notation "GA" => AdelicGL 3 (𝓞 ℚ) ℚ
local notation "Wh" => whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
  NumberField.StandardAddChar.psiQ

theorem DS.ofReal_cpow_eq_exp {a : ℝ} (ha : 0 < a) (z : ℂ) :
    ((a : ℝ) : ℂ) ^ z = Complex.exp (z * ((Real.log a : ℝ) : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ha.ne'), ← Complex.ofReal_log ha.le, mul_comm]

theorem DS.le_max_bounds {y : ℝ} (hy : 0 < y) :
    1 ≤ max 1 (max y y⁻¹) ∧ (max 1 (max y y⁻¹))⁻¹ ≤ y ∧ y ≤ max 1 (max y y⁻¹) := by
  refine ⟨le_max_left _ _, ?_, (le_max_left _ _).trans (le_max_right _ _)⟩
  rw [inv_le_comm₀ (lt_of_lt_of_le one_pos (le_max_left _ _)) hy]
  exact (le_max_right _ _).trans (le_max_right _ _)

theorem DS.main
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (u : GA → ℂ)
    (hcw : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w))
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : GA), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : GA), u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g)
    (hsa : WhittakerBlock.IsArchSmooth3 u)
    (c₁ : ℂ) (hc₁ : WhittakerBlock.casimir1 u = c₁ • u)
    (n J : ℕ) (e : Fin n → ℂ) (he : Function.Injective e) (τ : ℝ) (hτ : ∀ i, (e i).re < τ)
    (cf : Fin n → Fin J → ℝ → GA → ℂ)
    (hcf : ∀ i j, ContinuousOn (fun p : ℝ × GA => cf i j p.1 p.2) {p | 0 < p.1})
    (hexp₁ : ∀ K : Set GA, IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
      ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
      ‖Wh u (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
        (∑ i : Fin n, ∑ j : Fin J, cf i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
      C * y₁ ^ τ)
    (cf' : Fin n → Fin J → Fin n → Fin J → GA → ℂ)
    (hcf' : ∀ i j i' j', Continuous (cf' i j i' j'))
    (hexp₂ : ∀ K : Set GA, IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
      ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
      ‖cf i j y₂ k - (∑ i' : Fin n, ∑ j' : Fin J, cf' i j i' j' k * ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤
        C * y₂ ^ τ)
    (i₀ i₀' : Fin n) (j₀ j₀' : Fin J)
    (hbot₁ : ∀ (i : Fin n) (j : Fin J), (e i).re < (e i₀).re → ∀ y₂ : ℝ, 0 < y₂ → ∀ k, cf i j y₂ k = 0)
    (hbot₂ : ∀ (i' : Fin n) (j' : Fin J), (e i').re < (e i₀').re → ∀ k, cf' i₀ j₀ i' j' k = 0)
    (hlog₁ : ∀ j : Fin J, (j₀ : ℕ) < (j : ℕ) → ∀ y₂ : ℝ, 0 < y₂ → ∀ k, cf i₀ j y₂ k = 0)
    (hlog₂ : ∀ j' : Fin J, (j₀' : ℕ) < (j' : ℕ) → ∀ k, cf' i₀ j₀ i₀' j' k = 0) :
    ∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
      ∀ g : GA,
        cf' i₀ j₀ i₀' j₀' (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^
            ((![e i₀ - 1, e i₀' - e i₀, c₁ - e i₀' + 1] : Fin 3 → ℂ) a + (![1, 0, -1] : Fin 3 → ℂ) a)) *
          cf' i₀ j₀ i₀' j₀' g := by
  intro t ht hpos g
  have h0 := hpos 0
  have h1 := hpos 1
  have h2 := hpos 2
  have hr₁ : 0 < t 0 0 / t 1 1 := div_pos h0 h1
  have hr₂ : 0 < t 1 1 / t 2 2 := div_pos h1 h2
  set Lt : GA := WhittakerBlock.archRealLift3 t with hLt
  set Λ₀ : ℂ := ((t 2 2 : ℝ) : ℂ) ^ c₁ with hΛ₀

  have hc : ∀ y₂ : ℝ, 0 < y₂ →
      cf i₀ j₀ y₂ (Lt * g) =
        Complex.exp (2 * Real.pi * Complex.I * ((t 1 2 / t 2 2 * y₂ : ℝ) : ℂ)) * Λ₀ *
          ((t 0 0 / t 1 1 : ℝ) : ℂ) ^ e i₀ * cf i₀ j₀ (t 1 1 / t 2 2 * y₂) g := by
    intro y₂ hy₂
    have hy₂' : 0 < t 1 1 / t 2 2 * y₂ := mul_pos hr₂ hy₂
    obtain ⟨hb1, hbl, hbu⟩ := DS.le_max_bounds hy₂
    obtain ⟨hb1', hbl', hbu'⟩ := DS.le_max_bounds hy₂'
    obtain ⟨CF, hCF⟩ := hexp₁ {Lt * g} isCompact_singleton _ hb1
    obtain ⟨CG, hCG⟩ := hexp₁ {g} isCompact_singleton _ hb1'
    have h := DS.slot e he τ i₀ (hτ i₀) j₀
      (fun i j => cf i j y₂ (Lt * g)) (fun i j => cf i j (t 1 1 / t 2 2 * y₂) g)
      (fun i j hij => hbot₁ i j hij _ hy₂' g)
      (fun j hj => hlog₁ j hj y₂ hy₂ _) (fun j hj => hlog₁ j hj _ hy₂' g)
      (fun y => Wh u (WhittakerBlock.archRealLift3 (DS.dArr y y₂) * (Lt * g)))
      (fun y => Wh u (WhittakerBlock.archRealLift3 (DS.dArr y (t 1 1 / t 2 2 * y₂)) * g))
      (t 0 0 / t 1 1) hr₁
      (Complex.exp (2 * Real.pi * Complex.I * ((t 1 2 / t 2 2 * y₂ : ℝ) : ℂ)) * Λ₀) (t 0 1 / t 1 1)
      ⟨CF, fun y hy hy1 => hCF _ (Set.mem_singleton _) y₂ hbl hbu y hy hy1⟩
      ⟨CG, fun y hy hy1 => hCG _ (Set.mem_singleton _) _ hbl' hbu' y hy hy1⟩
      (fun y hy => by
        have hb := DS.whittaker3_dArr_mul_upperTriangular haut hsa hc₁ t ht hpos hy hy₂ g
        rw [← mul_assoc, hb, hΛ₀]
        rw [show t 0 0 / t 1 1 * y = y * t 0 0 / t 1 1 by ring,
          show t 1 1 / t 2 2 * y₂ = y₂ * t 1 1 / t 2 2 by ring]
        have hexp : Complex.exp (2 * Real.pi * Complex.I * ((y * t 0 1 / t 1 1 + y₂ * t 1 2 / t 2 2 : ℝ) : ℂ)) =
            Complex.exp (2 * Real.pi * Complex.I * ((t 0 1 / t 1 1 * y : ℝ) : ℂ)) *
              Complex.exp (2 * Real.pi * Complex.I * ((t 1 2 / t 2 2 * y₂ : ℝ) : ℂ)) := by
          rw [← Complex.exp_add]; congr 1; push_cast; ring
        rw [hexp]; ring)
    exact h

  have hd : cf' i₀ j₀ i₀' j₀' (Lt * g) =
      Λ₀ * ((t 0 0 / t 1 1 : ℝ) : ℂ) ^ e i₀ * ((t 1 1 / t 2 2 : ℝ) : ℂ) ^ e i₀' * cf' i₀ j₀ i₀' j₀' g := by
    obtain ⟨CF, hCF⟩ := hexp₂ {Lt * g} isCompact_singleton
    obtain ⟨CG, hCG⟩ := hexp₂ {g} isCompact_singleton
    have h := DS.slot e he τ i₀' (hτ i₀') j₀'
      (fun i' j' => cf' i₀ j₀ i' j' (Lt * g)) (fun i' j' => cf' i₀ j₀ i' j' g)
      (fun i' j' hij => hbot₂ i' j' hij g)
      (fun j' hj' => hlog₂ j' hj' _) (fun j' hj' => hlog₂ j' hj' g)
      (fun y => cf i₀ j₀ y (Lt * g)) (fun y => cf i₀ j₀ y g)
      (t 1 1 / t 2 2) hr₂ (Λ₀ * ((t 0 0 / t 1 1 : ℝ) : ℂ) ^ e i₀) (t 1 2 / t 2 2)
      ⟨CF, fun y hy hy1 => hCF _ (Set.mem_singleton _) i₀ j₀ y hy hy1⟩
      ⟨CG, fun y hy hy1 => hCG _ (Set.mem_singleton _) i₀ j₀ y hy hy1⟩
      (fun y hy => by rw [hc y hy]; ring)
    exact h

  rw [hd, hΛ₀, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  rw [DS.ofReal_cpow_eq_exp h2, DS.ofReal_cpow_eq_exp hr₁, DS.ofReal_cpow_eq_exp hr₂, DS.ofReal_cpow_eq_exp h0,
    DS.ofReal_cpow_eq_exp h1, DS.ofReal_cpow_eq_exp h2, Real.log_div h0.ne' h1.ne', Real.log_div h1.ne' h2.ne',
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  push_cast
  ring

end Main
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top.R1CuspDeriv"

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcw : ∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w))
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g)
    (hsa : WhittakerBlock.IsArchSmooth3 u)
    (c₁ : ℂ) (hc₁ : WhittakerBlock.casimir1 u = c₁ • u)
    (n J : ℕ) (e : Fin n → ℂ) (he : Function.Injective e) (τ : ℝ) (hτ : ∀ i, (e i).re < τ)
    (cf : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcf : ∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => cf i j p.1 p.2) {p | 0 < p.1})
    (hexp₁ : ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
      ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
      ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ u
          (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
        (∑ i : Fin n, ∑ j : Fin J, cf i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
      C * y₁ ^ τ)
    (cf' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcf' : ∀ i j i' j', Continuous (cf' i j i' j'))
    (hexp₂ : ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
      ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
      ‖cf i j y₂ k - (∑ i' : Fin n, ∑ j' : Fin J, cf' i j i' j' k * ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤
        C * y₂ ^ τ)
    (i₀ i₀' : Fin n) (j₀ j₀' : Fin J)
    (hbot₁ : ∀ (i : Fin n) (j : Fin J), (e i).re < (e i₀).re → ∀ y₂ : ℝ, 0 < y₂ → ∀ k, cf i j y₂ k = 0)
    (hbot₂ : ∀ (i' : Fin n) (j' : Fin J), (e i').re < (e i₀').re → ∀ k, cf' i₀ j₀ i' j' k = 0)
    (htop₁ : ∀ j : Fin J, (j₀ : ℕ) < (j : ℕ) → ∀ y₂ : ℝ, 0 < y₂ → ∀ k, cf i₀ j y₂ k = 0)
    (htop₂ : ∀ j' : Fin J, (j₀' : ℕ) < (j' : ℕ) → ∀ k, cf' i₀ j₀ i₀' j' k = 0) :
    ∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
      ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        cf' i₀ j₀ i₀' j₀' (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^
            ((![e i₀ - 1, e i₀' - e i₀, c₁ - e i₀' + 1] : Fin 3 → ℂ) a + (![1, 0, -1] : Fin 3 → ℂ) a)) *
          cf' i₀ j₀ i₀' j₀' g :=
  DS.main ω u hcw haut hcen hsa c₁ hc₁ n J e he τ hτ cf hcf hexp₁ cf' hcf' hexp₂ i₀ i₀' j₀ j₀' hbot₁ hbot₂ htop₁ htop₂

end S_LanglandsTunnell_CubicInduction_doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top (solution)
