-- Prove2me | solution 1 for NoHair.kerrNewman_stationaryFlatEnd
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T20:12:46.916515+00:00
-- url     : https://prove2.me/submissions/495f029b-fc1a-4e14-9883-d9211aa398ac

import Theorems.Thm_NoHair_kerrNewman_asymptoticComponentBounds
import Definitions.Def_NoHair_KerrNewmanEinstein_Base

open NoHair Set
open scoped ContDiff Manifold BigOperators Topology

noncomputable section

private abbrev I4 := 𝓘(ℝ, E4)

private theorem inclusion_deriv (U : TopologicalSpace.Opens E4) (x : U) :
    (mfderiv I4 I4 (Subtype.val : U → E4) x : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 :=
  mfderiv_extChartAt_self (I := I4) (x := x)

private theorem inclusion_diff (U : TopologicalSpace.Opens E4) (x : U) :
    MDifferentiableAt I4 I4 (Subtype.val : U → E4) x :=
  (contMDiff_subtype_val (I := I4) (U := U) (n := ∞)).mdifferentiableAt (by simp)

private theorem translate_the_fields (m a e s : ℝ) (y : E4) :
    kerrNewmanMetric m a e (y + s • coordBasis 0) = kerrNewmanMetric m a e y ∧
    kerrNewmanField a e (y + s • coordBasis 0) = kerrNewmanField a e y := by
  have h3 (x : E4) : (x + s • coordBasis 0) 3 = x 3 := NoHair.KNE.time_shift x s 3 (by decide)
  have hA (j : Fin 4) : (fun x : E4 => kerrNewmanPotential a e (x + s • coordBasis 0) j) =
      (fun x : E4 => kerrNewmanPotential a e x j) := by
    funext x
    simp only [kerrNewmanPotential, NoHair.KNE.ksRadius_time, NoHair.KNE.ksNull_time, h3]
  have hd (j : Fin 4) : fderiv ℝ (fun x => kerrNewmanPotential a e x j) (y + s • coordBasis 0) =
      fderiv ℝ (fun x => kerrNewmanPotential a e x j) y := by
    rw [← fderiv_comp_add_right (f := fun x => kerrNewmanPotential a e x j), hA]
  constructor
  · funext i j
    simp only [kerrNewmanMetric, ksProfile, NoHair.KNE.ksRadius_time, NoHair.KNE.ksNull_time, h3]
  · funext i j
    simp only [kerrNewmanField, coordPartial, hd]

private theorem stationary_translation (m a e : ℝ) :
    ∃ φ : ℝ → kerrNewmanSpacetime a → kerrNewmanSpacetime a,
      (∀ s x, (φ s x).val = x.val + s • coordBasis 0) ∧
      IsSymmetryFlow (kerrNewmanMetricField m a e) (kerrNewmanFieldField a e) φ := by
  let U := kerrNewmanSpacetime a
  let φ (s : ℝ) (x : U) : U := ⟨x.val + s • coordBasis 0, by
    change 0 < ksRadius a (x.val + s • coordBasis 0)
    rw [NoHair.KNE.ksRadius_time]
    exact x.property⟩
  have hV : ContMDiff I4 I4 ∞ (Subtype.val : U → E4) := contMDiff_subtype_val
  have hφ (t : ℝ) : ContMDiff I4 I4 ∞ (φ t) := by
    apply (ContMDiff.subtypeVal_comp_iff U (φ t)).mp
    exact hV.add contMDiff_const
  have hD (s : ℝ) (x : U) : (mfderiv I4 I4 (φ s) x : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 := by
    let shift (y : E4) := y + s • coordBasis 0
    have hs : HasFDerivAt shift (ContinuousLinearMap.id ℝ E4) x.val := (hasFDerivAt_id x.val).add_const _
    calc
      _ = (mfderiv I4 I4 (Subtype.val : U → E4) (φ s x)).comp (mfderiv I4 I4 (φ s) x) := by
        rw [inclusion_deriv]
        rfl
      _ = mfderiv I4 I4 ((Subtype.val : U → E4) ∘ φ s) x :=
        (mfderiv_comp x (inclusion_diff U _) ((hφ s).mdifferentiableAt (by simp))).symm
      _ = (mfderiv I4 I4 shift x.val).comp (mfderiv I4 I4 (Subtype.val : U → E4) x) :=
        mfderiv_comp x hs.differentiableAt.mdifferentiableAt (inclusion_diff U x)
      _ = _ := by
        rw [inclusion_deriv, mfderiv_eq_fderiv, hs.fderiv]
        rfl
  refine ⟨φ, fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    simp [φ]
  · intro s t x
    apply Subtype.ext
    change x.val + (s + t) • coordBasis 0 = x.val + t • coordBasis 0 + s • coordBasis 0
    rw [add_smul]
    abel
  · apply (ContMDiff.subtypeVal_comp_iff U _).mp
    exact (hV.comp contMDiff_snd).add (contMDiff_fst.smul contMDiff_const)
  · intro s x v w
    rw [hD]
    change matrixBilin (kerrNewmanMetric m a e (x.val + s • coordBasis 0)) v w = _
    rw [(translate_the_fields m a e s x.val).1]
    rfl
  · intro s x v w
    rw [hD]
    change matrixBilin (kerrNewmanField a e (x.val + s • coordBasis 0)) v w = _
    rw [(translate_the_fields m a e s x.val).2]
    rfl

private theorem basis_entry (A : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    matrixBilin A (coordBasis i) (coordBasis j) = A i j := by
  change Matrix.toLinearMap₂' ℝ A (WithLp.ofLp (coordBasis i)) (WithLp.ofLp (coordBasis j)) = _
  simp only [coordBasis, EuclideanSpace.single, PiLp.ofLp_single]
  rw [Matrix.toLinearMap₂'_apply]
  simp_rw [← Finset.smul_sum]
  simp [Pi.single_apply, ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem solution (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) :
    ∃ (φ : ℝ → kerrNewmanSpacetime a → kerrNewmanSpacetime a)
      (E : AsymptoticallyFlatEnd (kerrNewmanMetricField m a e) (kerrNewmanFieldField a e) φ),
      (∀ s x, (φ s x).val = x.val + s • coordBasis 0) ∧
      IsSymmetryFlow (kerrNewmanMetricField m a e) (kerrNewmanFieldField a e) φ ∧
      kerrNewmanOuterRadius m a e + |a| < E.R ∧
      E.region = (Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' exteriorRegion E.R := by
  classical
  let U := kerrNewmanSpacetime a
  obtain ⟨φ, hφ, hstation⟩ := stationary_translation m a e
  obtain ⟨R, C, hR, hbounds⟩ := kerrNewman_asymptoticComponentBounds m a e (kerrNewmanOuterRadius m a e + |a|)
  have hR0 : 0 < R := (le_max_left _ _).trans_lt hR
  let S := exteriorRegion R
  have hS : IsOpen S := by
    apply isOpen_lt continuous_const
    unfold spatialRadius
    fun_prop
  let y₀ : E4 := WithLp.toLp 2 ![0, R+1, 0, 0]
  have hy₀ : y₀ ∈ S := by
    change R < Real.sqrt ((R+1)^2 + 0^2 + 0^2)
    simp [Real.sqrt_sq_eq_abs, abs_of_pos (show 0 < R+1 by linarith)]
  let x₀ : U := ⟨y₀, (hbounds y₀ hy₀).1⟩
  let ψ (y : E4) : U := if h : y ∈ U then ⟨y,h⟩ else x₀
  have hv' (y : E4) (hy : y ∈ U) : (ψ y).val = y := by simp [ψ, hy]
  have hv (y : E4) (hy : y ∈ S) : (ψ y).val = y := hv' y (hbounds y hy).1
  have himg : ψ '' S = (Subtype.val : U → E4) ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change (ψ y).val ∈ S
      rwa [hv y hy]
    · intro hx
      exact ⟨x.val, hx, Subtype.ext (hv x.val hx)⟩
  have hgerm : EqOn ((Subtype.val : U → E4) ∘ ψ) id S := hv
  have hsm : ContMDiffOn I4 I4 ∞ ψ S := by
    intro z hz
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U ψ S z).mp
    exact ((contMDiff_id (I := I4)).contMDiffOn.congr (fun w hw => hgerm hw)) z hz
  have hder (y : E4) (hy : y ∈ S) :
      (mfderiv I4 I4 ψ y : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 := by
    have hψ := ((hsm y hy).contMDiffAt (hS.mem_nhds hy)).mdifferentiableAt (by simp)
    have hc := mfderiv_comp y (inclusion_diff U (ψ y)) hψ
    rw [inclusion_deriv] at hc
    change mfderiv I4 I4 ((Subtype.val : U → E4) ∘ ψ) y = (mfderiv I4 I4 ψ y : E4 →L[ℝ] E4) at hc
    rw [← hc, mfderiv_eq_fderiv, (hgerm.eventuallyEq_of_mem (hS.mem_nhds hy)).fderiv_eq, fderiv_id]
  have hcoeff (A : E4 → Matrix (Fin 4) (Fin 4) ℝ) (y : E4) (hy : y ∈ S) (i j : Fin 4) :
      pullbackCoeffs (M := U) (fun x => matrixBilin (A x.val)) ψ y i j = A y i j := by
    unfold pullbackCoeffs
    rw [hder y hy]
    change matrixBilin (A (ψ y).val) (coordBasis i) (coordBasis j) = A y i j
    rw [hv y hy, basis_entry]
  let E : AsymptoticallyFlatEnd (kerrNewmanMetricField m a e) (kerrNewmanFieldField a e) φ := {
    R := R, ψ := ψ, C := C, R_pos := hR0
    diffeo := by
      refine ⟨Subtype.val, mapsTo_image _ _, ?_, hv, ?_, hsm, contMDiff_subtype_val.contMDiffOn⟩
      · rw [himg]; exact fun _ hx => hx
      · rw [himg]; exact fun x hx => Subtype.ext (hv x.val hx)
    isOpen_image := by rw [himg]; exact hS.preimage continuous_subtype_val
    equivariant := by
      intro s y hy
      have hshift : y + s • coordBasis 0 ∈ S := by
        change R < spatialRadius (y + s • coordBasis 0)
        have heq : spatialRadius (y + s • coordBasis 0) = spatialRadius y := by
          simp only [spatialRadius, NoHair.KNE.time_shift y s 1 (by decide),
            NoHair.KNE.time_shift y s 2 (by decide), NoHair.KNE.time_shift y s 3 (by decide)]
        rwa [heq]
      exact Subtype.ext (by rw [hv _ hshift, hφ, hv y hy])
    metric_decay := by
      intro y hy i j
      have hentry : pullbackCoeffs (kerrNewmanMetricField m a e) ψ y i j = _ := hcoeff (kerrNewmanMetric m a e) y hy i j
      rw [hentry]
      exact (hbounds y hy).2.1 i j
    metric_deriv_decay := by
      intro y hy i j k
      have he : EqOn (fun w => pullbackCoeffs (kerrNewmanMetricField m a e) ψ w i j)
          (fun w => kerrNewmanMetric m a e w i j) S := fun w hw => hcoeff _ w hw i j
      unfold coordPartial
      rw [(he.eventuallyEq_of_mem (hS.mem_nhds hy)).fderiv_eq]
      exact (hbounds y hy).2.2.1 i j k
    field_decay := by
      intro y hy i j
      have hentry : pullbackCoeffs (kerrNewmanFieldField a e) ψ y i j = _ := hcoeff (kerrNewmanField a e) y hy i j
      rw [hentry]
      exact (hbounds y hy).2.2.2 i j }
  exact ⟨φ, E, hφ, hstation, (le_max_right _ _).trans_lt hR, himg⟩
