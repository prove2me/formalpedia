-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.SlabL2.casimir_apply_eq_kernelCasimir_archChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/fbabdfbc-ed41-5519-b2f2-fe92ad06b81b

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2KernelCasimir
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_apply_eq_kernelCasimir_archChart

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm Matrix MeasureTheory Topology Filter TopologicalSpace

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.archChart SlabL2.realCoordinate SlabL2.archEntries SlabL2.IsSmoothArchFactor AdelicGL archComponent3 WhittakerBlock.archDeriv WhittakerBlock.casimir1 WhittakerBlock.casimir2 WhittakerBlock.casimir3"
namespace ArchConvCalculus
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

abbrev E33 : Type := Fin 3 → Fin 3 → ℝ

theorem realCoord_ofReal (r : ℝ) : StandardKernel.realCoord (StandardKernel.ofReal r) = r :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

def realEquiv : InfiniteAdeleRing ℚ ≃+* ℝ where
  toFun := StandardKernel.realCoord
  invFun := StandardKernel.ofReal
  left_inv := StandardKernel.ofReal_realCoord
  right_inv := realCoord_ofReal
  map_mul' := map_mul _
  map_add' := map_add _

theorem realEquiv_apply (x : InfiniteAdeleRing ℚ) : realEquiv x = StandardKernel.realCoord x := rfl

theorem realEquiv_symm_apply (r : ℝ) : realEquiv.symm r = StandardKernel.ofReal r := rfl

theorem continuous_realCoord : Continuous StandardKernel.realCoord :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).continuous.comp
    (continuous_apply Rat.infinitePlace)

def realHomeo : InfiniteAdeleRing ℚ ≃ₜ ℝ where
  toEquiv := realEquiv.toEquiv
  continuous_toFun := continuous_realCoord
  continuous_invFun := StandardKernel.continuous_ofReal

def ent (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) : E33 :=
  fun a b => StandardKernel.realCoord ((h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) a b)

theorem ent_apply (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) (a b : Fin 3) :
    ent h a b = StandardKernel.realCoord ((h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) a b) := rfl

theorem of_ent (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    Matrix.of (ent h) = ((StandardKernel.realGL h : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext a b; rfl

theorem of_ent_mul (h h' : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    Matrix.of (ent (h * h')) = Matrix.of (ent h) * Matrix.of (ent h') := by
  rw [of_ent, of_ent, of_ent, map_mul, Units.val_mul]

theorem of_ent_inv (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    Matrix.of (ent h⁻¹) = (Matrix.of (ent h))⁻¹ := by
  rw [of_ent, of_ent, map_inv, Matrix.coe_units_inv]

theorem det_of_ent_ne_zero (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) : (Matrix.of (ent h)).det ≠ 0 := by
  rw [of_ent]
  exact Matrix.GeneralLinearGroup.det_ne_zero _

theorem continuous_ent : Continuous ent :=
  continuous_pi fun a => continuous_pi fun b =>
    continuous_realCoord.comp (Units.continuous_val.matrix_elem a b)

theorem archEntries_archInclN (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    SlabL2.archEntries (archInclN (Fin 3) ℚ h) = ent h := rfl

def toGinf : GL (Fin 3) ℝ →* GL (Fin 3) (InfiniteAdeleRing ℚ) :=
  Matrix.GeneralLinearGroup.map (realEquiv.symm : ℝ ≃+* InfiniteAdeleRing ℚ).toRingHom

def liftE (e : E33) (he : (Matrix.of e).det ≠ 0) : GL (Fin 3) (InfiniteAdeleRing ℚ) :=
  toGinf (Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) he)

theorem coe_liftE (e : E33) (he : (Matrix.of e).det ≠ 0) (a b : Fin 3) :
    (liftE e he : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) a b = StandardKernel.ofReal (e a b) := rfl

theorem ent_liftE (e : E33) (he : (Matrix.of e).det ≠ 0) : ent (liftE e he) = e := by
  funext a b
  rw [ent_apply, coe_liftE, realCoord_ofReal]

theorem realGL_toGinf (u : GL (Fin 3) ℝ) : StandardKernel.realGL (toGinf u) = u := by
  ext a b
  exact realCoord_ofReal _

theorem toGinf_realGL (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) : toGinf (StandardKernel.realGL h) = h := by
  ext a b
  exact StandardKernel.ofReal_realCoord _

theorem liftE_ent (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) : liftE (ent h) (det_of_ent_ne_zero h) = h := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [coe_liftE, ent_apply, StandardKernel.ofReal_realCoord]

theorem archRealLift3_eq (e : E33) (he : (Matrix.of e).det ≠ 0) :
    WhittakerBlock.archRealLift3 e = archInclN (Fin 3) ℚ (liftE e he) := by
  have hval : WhittakerBlock.archRealMat3 e =
      ((archInclN (Fin 3) ℚ (liftE e he) : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) := by
    rfl
  have hu : IsUnit (WhittakerBlock.archRealMat3 e) := ⟨archInclN (Fin 3) ℚ (liftE e he), hval.symm⟩
  unfold WhittakerBlock.archRealLift3
  rw [dif_pos hu]
  exact Units.ext (by rw [hu.unit_spec, hval])

theorem archInclN_eq_archRealLift3 (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    archInclN (Fin 3) ℚ h = WhittakerBlock.archRealLift3 (ent h) := by
  rw [archRealLift3_eq (ent h) (det_of_ent_ne_zero h), liftE_ent]

theorem continuous_archInclN : Continuous (archInclN (Fin 3) ℚ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun a : GL (Fin 3) (InfiniteAdeleRing ℚ) =>
      (((a : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j,
        (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)
    exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const
  · refine continuous_matrix fun i j => ?_
    show Continuous fun a : GL (Fin 3) (InfiniteAdeleRing ℚ) =>
      ((((a⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j,
        (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)
    exact (Units.continuous_coe_inv.matrix_elem i j).prodMk continuous_const

theorem continuous_toGinf : Continuous toGinf :=
  Continuous.units_map _
    ((continuous_id.matrix_map StandardKernel.continuous_ofReal :
      Continuous fun m : Matrix (Fin 3) (Fin 3) ℝ => m.map StandardKernel.ofReal))

theorem continuous_liftE_subtype {T : Set E33} (hTloc : T ⊆ {m | (Matrix.of m).det ≠ 0}) :
    Continuous fun x : T => liftE x.1 (hTloc x.2) := by
  refine continuous_toGinf.comp ?_
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact continuous_subtype_val
  · have hfun : (fun x : T => (((Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of x.1) (hTloc x.2))⁻¹ :
        GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)) = fun x : T => (Matrix.of x.1)⁻¹ :=
      funext fun x => Matrix.coe_units_inv _
    rw [hfun]
    refine continuous_iff_continuousAt.mpr fun x => ?_
    have hdet : IsUnit (Matrix.of x.1).det := isUnit_iff_ne_zero.mpr (hTloc x.2)
    have hc : ContinuousAt Ring.inverse (Matrix.of x.1).det := by
      simpa using NormedRing.inverse_continuousAt hdet.unit
    exact (continuousAt_matrix_inv (Matrix.of x.1) hc).comp (f := fun x : T => Matrix.of x.1)
      continuous_subtype_val.continuousAt

theorem isCompact_preimage_ent {T : Set E33} (hT : IsCompact T) (hTloc : T ⊆ {m | (Matrix.of m).det ≠ 0}) :
    IsCompact (ent ⁻¹' T) := by
  haveI : CompactSpace T := isCompact_iff_compactSpace.mp hT
  have hj := continuous_liftE_subtype hTloc
  have hsub : ent ⁻¹' T ⊆ Set.range fun x : T => liftE x.1 (hTloc x.2) := by
    intro a ha
    exact ⟨⟨ent a, ha⟩, liftE_ent a⟩
  exact (isCompact_range hj).of_isClosed_subset (hT.isClosed.preimage continuous_ent) hsub

theorem hasCompactSupport_comp_ent {β : E33 → ℂ} (hβ : SlabL2.IsSmoothArchFactor β) :
    HasCompactSupport fun h => β (ent h) :=
  (isCompact_preimage_ent hβ.2.1 hβ.2.2).of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (fun _ ha => subset_closure ha) ((isClosed_tsupport β).preimage continuous_ent))

def dirE (i j : Fin 3) (s : ℝ) : E33 :=
  fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0

theorem of_dirE (i j : Fin 3) (s : ℝ) : Matrix.of (dirE i j s) = 1 + s • Matrix.single i j (1 : ℝ) := by
  ext a b
  simp only [dirE, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  congr 1
  by_cases h : a = i ∧ b = j
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
  · rw [if_neg h, if_neg fun h' => h ⟨h'.1.symm, h'.2.symm⟩]

theorem dirE_zero (i j : Fin 3) : Matrix.of (dirE i j 0) = 1 := by
  rw [of_dirE, zero_smul, add_zero]

theorem of_dirE_mul_of_dirE (i j : Fin 3) (s t : ℝ) :
    Matrix.of (dirE i j s) * Matrix.of (dirE i j t) =
      1 + (s + t) • Matrix.single i j (1 : ℝ) + (s * t) • (Matrix.single i j (1 : ℝ) * Matrix.single i j 1) := by
  rw [of_dirE, of_dirE, add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_smul_comm, add_smul]
  abel

def invParam (i j : Fin 3) (s : ℝ) : ℝ := if i = j then -s / (1 + s) else -s

theorem invParam_zero (i j : Fin 3) : invParam i j 0 = 0 := by
  simp [invParam]

theorem of_dirE_mul_of_dirE_invParam (i j : Fin 3) {s : ℝ} (hs : 1 + s ≠ 0) :
    Matrix.of (dirE i j s) * Matrix.of (dirE i j (invParam i j s)) = 1 := by
  rw [of_dirE_mul_of_dirE]
  by_cases hij : i = j
  · subst hij
    have hσ : s + invParam i i s = -(s * invParam i i s) := by
      simp only [invParam, if_true]
      field_simp
      ring
    rw [Matrix.single_mul_single_same, mul_one, hσ, neg_smul, add_assoc, neg_add_cancel, add_zero]
  · have hσ : s + invParam i j s = 0 := by simp [invParam, hij]
    rw [Matrix.single_mul_single_of_ne (h := Ne.symm hij), hσ, zero_smul, smul_zero, add_zero, add_zero]

theorem of_dirE_invParam_mul_of_dirE (i j : Fin 3) {s : ℝ} (hs : 1 + s ≠ 0) :
    Matrix.of (dirE i j (invParam i j s)) * Matrix.of (dirE i j s) = 1 := by
  rw [of_dirE_mul_of_dirE]
  by_cases hij : i = j
  · subst hij
    have hσ : invParam i i s + s = -(invParam i i s * s) := by
      simp only [invParam, if_true]
      field_simp
      ring
    rw [Matrix.single_mul_single_same, mul_one, hσ, neg_smul, add_assoc, neg_add_cancel, add_zero]
  · have hσ : invParam i j s + s = 0 := by simp [invParam, hij]
    rw [Matrix.single_mul_single_of_ne (h := Ne.symm hij), hσ, zero_smul, smul_zero, add_zero, add_zero]

theorem det_of_dirE_ne_zero (i j : Fin 3) {s : ℝ} (hs : 1 + s ≠ 0) : (Matrix.of (dirE i j s)).det ≠ 0 := by
  intro h0
  have h := congrArg Matrix.det (of_dirE_invParam_mul_of_dirE i j hs)
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at h
  exact zero_ne_one h

theorem det_of_dirE_invParam_ne_zero (i j : Fin 3) {s : ℝ} (hs : 1 + s ≠ 0) :
    (Matrix.of (dirE i j (invParam i j s))).det ≠ 0 := by
  intro h0
  have h := congrArg Matrix.det (of_dirE_invParam_mul_of_dirE i j hs)
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h
  exact zero_ne_one h

def lineElt (i j : Fin 3) (s : ℝ) (hs : 1 + s ≠ 0) : GL (Fin 3) (InfiniteAdeleRing ℚ) :=
  liftE (dirE i j s) (det_of_dirE_ne_zero i j hs)

theorem liftE_mul_liftE (e e' : E33) (he : (Matrix.of e).det ≠ 0) (he' : (Matrix.of e').det ≠ 0)
    (hee' : (Matrix.of e * Matrix.of e').det ≠ 0) :
    liftE e he * liftE e' he' = liftE (fun a b => (Matrix.of e * Matrix.of e') a b) hee' := by
  unfold liftE
  rw [← map_mul]
  congr 1
  exact Units.ext rfl

theorem lineElt_inv (i j : Fin 3) (s : ℝ) (hs : 1 + s ≠ 0) :
    (lineElt i j s hs)⁻¹ = liftE (dirE i j (invParam i j s)) (det_of_dirE_invParam_ne_zero i j hs) := by
  refine inv_eq_of_mul_eq_one_right ?_
  unfold lineElt liftE
  rw [← map_mul]
  convert map_one toGinf
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_one]
  exact of_dirE_mul_of_dirE_invParam i j hs

def shear (i j : Fin 3) (t : ℝ) (m : E33) : E33 :=
  fun a b => m a b + t * (if a = i then m j b else 0)

def rowDir (i j : Fin 3) (m : E33) : E33 :=
  fun a b => if a = i then m j b else 0

theorem shear_eq (i j : Fin 3) (t : ℝ) (m : E33) : shear i j t m = m + t • rowDir i j m := by
  funext a b
  simp [shear, rowDir]

theorem of_dirE_mul (i j : Fin 3) (t : ℝ) (m : E33) :
    (fun a b => (Matrix.of (dirE i j t) * Matrix.of m) a b) = shear i j t m := by
  funext a b
  rw [of_dirE, add_mul, one_mul, Matrix.add_apply, Matrix.of_apply, Matrix.smul_mul, Matrix.smul_apply,
    smul_eq_mul, shear]
  congr 1
  by_cases ha : a = i
  · subst ha
    rw [Matrix.single_mul_apply_same, one_mul, if_pos rfl, Matrix.of_apply]
  · rw [Matrix.single_mul_apply_of_ne (h := ha), if_neg ha]

theorem ent_liftE_mul (e : E33) (he : (Matrix.of e).det ≠ 0) (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    ent (liftE e he * h) = fun a b => (Matrix.of e * Matrix.of (ent h)) a b := by
  have := of_ent_mul (liftE e he) h
  rw [ent_liftE] at this
  funext a b
  rw [← Matrix.of_apply (ent (liftE e he * h)) a b, this]

theorem ent_lineElt_inv_mul (i j : Fin 3) (s : ℝ) (hs : 1 + s ≠ 0) (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    ent ((lineElt i j s hs)⁻¹ * h) = shear i j (invParam i j s) (ent h) := by
  rw [lineElt_inv, ent_liftE_mul, of_dirE_mul]

theorem archRealLift3_dirE (i j : Fin 3) (s : ℝ) (hs : 1 + s ≠ 0) :
    WhittakerBlock.archRealLift3 (dirE i j s) = archInclN (Fin 3) ℚ (lineElt i j s hs) :=
  archRealLift3_eq _ _

def rowDirL (i j : Fin 3) : E33 →L[ℝ] E33 :=
  LinearMap.toContinuousLinearMap
    { toFun := rowDir i j
      map_add' := fun m m' => by funext a b; simp only [rowDir, Pi.add_apply]; split_ifs <;> simp
      map_smul' := fun c m => by funext a b; simp only [rowDir, Pi.smul_apply, smul_eq_mul, RingHom.id_apply];
                                 split_ifs <;> simp }

theorem rowDirL_apply (i j : Fin 3) (m : E33) : rowDirL i j m = rowDir i j m := rfl

theorem norm_rowDir_le (i j : Fin 3) (m : E33) : ‖rowDir i j m‖ ≤ ‖m‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg m)).mpr fun a => ?_
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg m)).mpr fun b => ?_
  simp only [rowDir]
  split_ifs with ha
  · exact (norm_le_pi_norm (m j) b).trans (norm_le_pi_norm m j)
  · rw [norm_zero]; exact norm_nonneg m

def leftDeriv (i j : Fin 3) (β : E33 → ℂ) : E33 → ℂ :=
  fun m => -(fderiv ℝ β m (rowDir i j m))

theorem leftDeriv_apply (i j : Fin 3) (β : E33 → ℂ) (m : E33) :
    leftDeriv i j β m = -(fderiv ℝ β m (rowDir i j m)) := rfl

theorem support_leftDeriv_subset (i j : Fin 3) (β : E33 → ℂ) :
    Function.support (leftDeriv i j β) ⊆ tsupport β := by
  intro m hm
  by_contra h
  exact hm (by rw [leftDeriv_apply, fderiv_of_notMem_tsupport ℝ h, ContinuousLinearMap.zero_apply, neg_zero])

theorem tsupport_leftDeriv_subset (i j : Fin 3) (β : E33 → ℂ) : tsupport (leftDeriv i j β) ⊆ tsupport β :=
  closure_minimal (support_leftDeriv_subset i j β) (isClosed_tsupport β)

theorem isSmoothArchFactor_leftDeriv (i j : Fin 3) {β : E33 → ℂ} (hβ : SlabL2.IsSmoothArchFactor β) :
    SlabL2.IsSmoothArchFactor (leftDeriv i j β) := by
  refine ⟨?_, ?_, (tsupport_leftDeriv_subset i j β).trans hβ.2.2⟩
  · have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ β) := hβ.1.fderiv_right (by norm_cast)
    have h2 : ContDiff ℝ (⊤ : ℕ∞) fun m : E33 => rowDirL i j m := (rowDirL i j).contDiff
    exact (h1.clm_apply h2).neg
  · exact HasCompactSupport.of_support_subset_isCompact hβ.2.1 (support_leftDeriv_subset i j β)

theorem one_add_ne_zero_of_abs_le {s : ℝ} (hs : |s| ≤ 1 / 2) : 1 + s ≠ 0 := by
  have := neg_abs_le s
  intro h
  linarith

theorem one_add_ne_zero_of_mem_ball {s : ℝ} (hs : s ∈ Metric.ball (0 : ℝ) (1 / 2)) : 1 + s ≠ 0 := by
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
  exact one_add_ne_zero_of_abs_le hs.le

def omega1 (β : E33 → ℂ) : E33 → ℂ := fun m => ∑ i : Fin 3, leftDeriv i i β m

def omega2 (β : E33 → ℂ) : E33 → ℂ := fun m => ∑ i : Fin 3, ∑ j : Fin 3, leftDeriv i j (leftDeriv j i β) m

def omega3 (β : E33 → ℂ) : E33 → ℂ :=
  fun m => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, leftDeriv i j (leftDeriv j k (leftDeriv k i β)) m

def invLocus : Set E33 := {m | (Matrix.of m).det ≠ 0}

theorem isOpen_invLocus : IsOpen invLocus := by
  have hc : Continuous fun e : E33 => (Matrix.of e).det :=
    (continuous_id : Continuous fun e : E33 => (Matrix.of e : Matrix (Fin 3) (Fin 3) ℝ)).matrix_det
  exact isOpen_ne_fun hc continuous_const

theorem ent_mem_invLocus (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) : ent h ∈ invLocus := det_of_ent_ne_zero h

theorem continuous_archComponent3 : Continuous (archComponent3 (𝓞 ℚ) ℚ) :=
  Continuous.units_map _ ((continuous_id.matrix_map (AdelicLevel.continuous_adeleArch (𝓞 ℚ) ℚ) :
    Continuous fun m : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) => m.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ)))

theorem archEntries_eq_ent (g : AdelicGL 3 (𝓞 ℚ) ℚ) : SlabL2.archEntries g = ent (archComponent3 (𝓞 ℚ) ℚ g) := by
  funext a b
  change SlabL2.realCoordinate ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) a b).1 =
    StandardKernel.realCoord (AdelicLevel.adeleArch (𝓞 ℚ) ℚ ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) a b))
  rw [AdelicLevel.adeleArch_apply]
  rfl

theorem continuous_archEntries : Continuous (SlabL2.archEntries) := by
  have : SlabL2.archEntries = fun g => ent (archComponent3 (𝓞 ℚ) ℚ g) := funext archEntries_eq_ent
  rw [this]
  exact continuous_ent.comp continuous_archComponent3

theorem archEntries_mem_invLocus (g : AdelicGL 3 (𝓞 ℚ) ℚ) : SlabL2.archEntries g ∈ invLocus := by
  rw [archEntries_eq_ent]
  exact ent_mem_invLocus _

theorem continuous_comp_archEntries {f : E33 → ℂ} (hf : ContinuousOn f invLocus) :
    Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => f (SlabL2.archEntries g) :=
  hf.comp_continuous continuous_archEntries archEntries_mem_invLocus

def omega3T (f : E33 → ℂ) : E33 → ℂ :=
  fun m => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, leftDeriv k i (leftDeriv j k (leftDeriv i j f)) m

def idE : E33 := fun a b => if a = b then 1 else 0

theorem of_idE : Matrix.of idE = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext a b; rw [Matrix.of_apply, idE, Matrix.one_apply]

theorem idE_mem_invLocus : idE ∈ invLocus := by
  show (Matrix.of idE).det ≠ 0
  rw [of_idE, Matrix.det_one]; exact one_ne_zero

theorem dirE_eq_zero_add (i j : Fin 3) : dirE i j 0 = idE := by
  funext a b; simp [dirE, idE]

def stdE (i j : Fin 3) : E33 := fun a b => if a = i ∧ b = j then 1 else 0

theorem dirE_eq (i j : Fin 3) (s : ℝ) : dirE i j s = idE + s • stdE i j := by
  funext a b
  simp only [dirE, idE, stdE, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

theorem rowDir_idE (i j : Fin 3) : rowDir i j idE = stdE i j := by
  funext a b
  simp only [rowDir, idE, stdE]
  by_cases ha : a = i
  · by_cases hb : b = j
    · simp [ha, hb]
    · simp [ha, hb, Ne.symm hb]
  · simp [ha]

theorem rowDir_stdE (j i : Fin 3) : rowDir j i (stdE i j) = stdE j j := by
  funext a b
  simp only [rowDir, stdE, true_and]
  by_cases ha : a = j <;> simp [ha]

def colDir (i j : Fin 3) (m : E33) : E33 := fun a b => if b = j then m a i else 0

def colDirL (i j : Fin 3) : E33 →L[ℝ] E33 :=
  LinearMap.toContinuousLinearMap
    { toFun := colDir i j
      map_add' := fun m m' => by funext a b; simp only [colDir, Pi.add_apply]; split_ifs <;> simp
      map_smul' := fun c m => by funext a b; simp only [colDir, Pi.smul_apply, smul_eq_mul, RingHom.id_apply];
                                 split_ifs <;> simp }

theorem colDirL_apply (i j : Fin 3) (m : E33) : colDirL i j m = colDir i j m := rfl

theorem colDir_idE (i j : Fin 3) : colDir i j idE = stdE i j := by
  funext a b
  simp only [colDir, idE, stdE]
  by_cases ha : a = i <;> by_cases hb : b = j <;> simp [ha, hb]

theorem colDir_stdE (j i : Fin 3) : colDir j i (stdE i j) = stdE i i := by
  funext a b
  simp only [colDir, stdE, and_true]
  by_cases hb : b = i <;> simp [hb]

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

theorem liftE_idE : liftE idE idE_mem_invLocus = 1 := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [coe_liftE, Units.val_one, idE]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, Matrix.one_apply_eq, ← realEquiv_symm_apply, map_one]
  · rw [if_neg hab, Matrix.one_apply_ne hab, ← realEquiv_symm_apply, map_zero]

theorem archRealLift3_idE : WhittakerBlock.archRealLift3 idE = 1 := by
  rw [archRealLift3_eq idE idE_mem_invLocus, liftE_idE, map_one]

theorem archRealLift3_mul {m m' : E33} (hm : m ∈ invLocus) (hm' : m' ∈ invLocus) :
    WhittakerBlock.archRealLift3 m * WhittakerBlock.archRealLift3 m' =
      WhittakerBlock.archRealLift3 (fun a b => (Matrix.of m * Matrix.of m') a b) := by
  have hmm' : (Matrix.of m * Matrix.of m').det ≠ 0 := by
    rw [Matrix.det_mul]; exact mul_ne_zero hm hm'
  rw [archRealLift3_eq m hm, archRealLift3_eq m' hm', ← map_mul, liftE_mul_liftE m m' hm hm' hmm']
  exact (archRealLift3_eq _ hmm').symm

def chart (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (x : AdelicGL 3 (𝓞 ℚ) ℚ) : E33 → ℂ :=
  fun m => F (x * WhittakerBlock.archRealLift3 m)

theorem chart_idE (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (x : AdelicGL 3 (𝓞 ℚ) ℚ) : chart F x idE = F x := by
  rw [chart, archRealLift3_idE, mul_one]

theorem contDiffOn_chart {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : WhittakerBlock.IsArchSmooth3 F) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (chart F x) invLocus :=
  hF x

theorem archDeriv_apply_chart {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : WhittakerBlock.IsArchSmooth3 F)
    (x : AdelicGL 3 (𝓞 ℚ) ℚ) {m : E33} (hm : m ∈ invLocus) (i j : Fin 3) :
    WhittakerBlock.archDeriv i j F (x * WhittakerBlock.archRealLift3 m) = fderiv ℝ (chart F x) m (colDir i j m) := by
  have hev : (fun s => F (x * WhittakerBlock.archRealLift3 m * WhittakerBlock.archRealLift3 (dirE i j s))) =ᶠ[𝓝 0]
      fun s => chart F x (m + s • colDir i j m) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with s hs
    have hs1 := one_add_ne_zero_of_mem_ball hs
    rw [mul_assoc, archRealLift3_mul hm (det_of_dirE_ne_zero i j hs1), chart, of_mul_of_dirE]
  have hd : HasFDerivAt (chart F x) (fderiv ℝ (chart F x) m) m :=
    (((contDiffOn_chart hF x).differentiableOn (by simp)) m hm).differentiableAt
      (isOpen_invLocus.mem_nhds hm) |>.hasFDerivAt
  have hc : HasDerivAt (fun s : ℝ => m + s • colDir i j m) (colDir i j m) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (colDir i j m)).const_add m
  have hd' : HasFDerivAt (chart F x) (fderiv ℝ (chart F x) m) (m + (0 : ℝ) • colDir i j m) := by simpa using hd
  show deriv (fun s => F (x * WhittakerBlock.archRealLift3 m * WhittakerBlock.archRealLift3 (dirE i j s))) 0 = _
  rw [hev.deriv_eq,
    show (fun s : ℝ => chart F x (m + s • colDir i j m)) = chart F x ∘ fun s : ℝ => m + s • colDir i j m from rfl]
  exact (hd'.comp_hasDerivAt (0 : ℝ) hc).deriv

theorem hasFDerivAt_fderiv_chart {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : WhittakerBlock.IsArchSmooth3 F)
    (x : AdelicGL 3 (𝓞 ℚ) ℚ) {m : E33} (hm : m ∈ invLocus) :
    HasFDerivAt (fderiv ℝ (chart F x)) (fderiv ℝ (fderiv ℝ (chart F x)) m) m := by
  have h := (contDiffOn_chart hF x).fderiv_of_isOpen isOpen_invLocus (m := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (by exact_mod_cast le_top)
  exact ((h.differentiableOn (by simp)) m hm).differentiableAt (isOpen_invLocus.mem_nhds hm) |>.hasFDerivAt

theorem casimir1_eq_neg_omega1_chart {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : WhittakerBlock.IsArchSmooth3 F)
    (x : AdelicGL 3 (𝓞 ℚ) ℚ) : WhittakerBlock.casimir1 F x = -omega1 (chart F x) idE := by
  show ∑ i : Fin 3, WhittakerBlock.archDeriv i i F x = _
  simp only [omega1, leftDeriv_apply, Finset.sum_neg_distrib, neg_neg, rowDir_idE]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := archDeriv_apply_chart hF x idE_mem_invLocus i i
  rw [archRealLift3_idE, mul_one, colDir_idE] at this
  exact this

theorem casimir2_eq_omega2_chart {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : WhittakerBlock.IsArchSmooth3 F)
    (x : AdelicGL 3 (𝓞 ℚ) ℚ) : WhittakerBlock.casimir2 F x = omega2 (chart F x) idE := by
  set f := chart F x with hf
  set D1 := fderiv ℝ f idE with hD1
  set D2 := fderiv ℝ (fderiv ℝ f) idE with hD2
  have hfd : HasFDerivAt f D1 idE :=
    (((contDiffOn_chart hF x).differentiableOn (by simp)) idE idE_mem_invLocus).differentiableAt
      (isOpen_invLocus.mem_nhds idE_mem_invLocus) |>.hasFDerivAt
  have hffd : HasFDerivAt (fderiv ℝ f) D2 idE := hasFDerivAt_fderiv_chart hF x idE_mem_invLocus

  have hR : ∀ i j : Fin 3, WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j i F) x =
      D1 (stdE i i) + D2 (stdE i j) (stdE j i) := by
    intro i j
    have hev : (fun s => WhittakerBlock.archDeriv j i F (x * WhittakerBlock.archRealLift3 (dirE i j s))) =ᶠ[𝓝 0]
        fun s => (fderiv ℝ f (idE + s • stdE i j)) (colDirL j i (idE + s • stdE i j)) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with s hs
      rw [archDeriv_apply_chart hF x (det_of_dirE_ne_zero i j (one_add_ne_zero_of_mem_ball hs)), colDirL_apply,
        dirE_eq]
    have hg : HasFDerivAt (fun m => (fderiv ℝ f m) (colDirL j i m))
        ((fderiv ℝ f idE).comp (colDirL j i) + D2.flip (colDirL j i idE)) idE :=
      hffd.clm_apply (colDirL j i).hasFDerivAt
    have hc : HasDerivAt (fun s : ℝ => idE + s • stdE i j) (stdE i j) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (stdE i j)).const_add idE
    have hg' : HasFDerivAt (fun m => (fderiv ℝ f m) (colDirL j i m))
        ((fderiv ℝ f idE).comp (colDirL j i) + D2.flip (colDirL j i idE)) (idE + (0 : ℝ) • stdE i j) := by
      simpa using hg
    show deriv (fun s => WhittakerBlock.archDeriv j i F (x * WhittakerBlock.archRealLift3 (dirE i j s))) 0 = _
    rw [hev.deriv_eq, show (fun s : ℝ => (fderiv ℝ f (idE + s • stdE i j)) ((colDirL j i) (idE + s • stdE i j))) =
      (fun m => (fderiv ℝ f m) (colDirL j i m)) ∘ (fun s : ℝ => idE + s • stdE i j) from rfl,
      (hg'.comp_hasDerivAt (0 : ℝ) hc).deriv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, colDirL_apply, colDir_stdE,
      ContinuousLinearMap.flip_apply, colDir_idE, hD1]

  have hL : ∀ i j : Fin 3, leftDeriv i j (leftDeriv j i f) idE = D1 (stdE j j) + D2 (stdE i j) (stdE j i) := by
    intro i j
    have hg : HasFDerivAt (fun m => (fderiv ℝ f m) (rowDirL j i m))
        ((fderiv ℝ f idE).comp (rowDirL j i) + D2.flip (rowDirL j i idE)) idE :=
      hffd.clm_apply (rowDirL j i).hasFDerivAt
    have hneg : leftDeriv j i f = fun m => -((fderiv ℝ f m) (rowDirL j i m)) := rfl
    rw [leftDeriv_apply, hneg, hg.fun_neg.fderiv, ContinuousLinearMap.neg_apply, neg_neg]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, rowDirL_apply, rowDir_idE, rowDir_stdE,
      ContinuousLinearMap.flip_apply, hD1]
  show ∑ i : Fin 3, ∑ j : Fin 3, WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j i F) x = _
  simp only [omega2, hR, hL, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]

def mulE (m n : E33) : E33 := fun a b => (Matrix.of m * Matrix.of n) a b

theorem of_mulE (m n : E33) : Matrix.of (mulE m n) = Matrix.of m * Matrix.of n := rfl

theorem mulE_assoc (m n p : E33) : mulE (mulE m n) p = mulE m (mulE n p) := by
  show (fun a b => (Matrix.of (mulE m n) * Matrix.of p) a b) = fun a b => (Matrix.of m * Matrix.of (mulE n p)) a b
  rw [of_mulE, of_mulE, Matrix.mul_assoc]

theorem of_stdE (i j : Fin 3) : Matrix.of (stdE i j) = Matrix.single i j (1 : ℝ) := by
  ext a b
  simp only [Matrix.of_apply, stdE, Matrix.single_apply]
  by_cases h : a = i ∧ b = j
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
  · rw [if_neg h, if_neg fun h' => h ⟨h'.1.symm, h'.2.symm⟩]

theorem colDir_eq_mulE (i j : Fin 3) (m : E33) : colDir i j m = mulE m (stdE i j) := by
  funext a b
  simp only [colDir, mulE, of_stdE]
  by_cases hb : b = j
  · subst hb; rw [Matrix.mul_single_apply_same, mul_one, if_pos rfl, Matrix.of_apply]
  · rw [Matrix.mul_single_apply_of_ne (hbj := hb), if_neg hb]

theorem rowDir_eq_mulE (i j : Fin 3) (m : E33) : rowDir i j m = mulE (stdE i j) m := by
  funext a b
  simp only [rowDir, mulE, of_stdE]
  by_cases ha : a = i
  · subst ha; rw [Matrix.single_mul_apply_same, one_mul, if_pos rfl, Matrix.of_apply]
  · rw [Matrix.single_mul_apply_of_ne (h := ha), if_neg ha]

theorem mulE_idE_left (m : E33) : mulE idE m = m := by
  funext a b; simp only [mulE, of_idE, Matrix.one_mul, Matrix.of_apply]

theorem mulE_idE_right (m : E33) : mulE m idE = m := by
  funext a b; simp only [mulE, of_idE, Matrix.mul_one, Matrix.of_apply]

theorem hasFDerivAt_fderiv_fderiv_chart {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : WhittakerBlock.IsArchSmooth3 F)
    (x : AdelicGL 3 (𝓞 ℚ) ℚ) {m : E33} (hm : m ∈ invLocus) :
    HasFDerivAt (fderiv ℝ (fderiv ℝ (chart F x))) (fderiv ℝ (fderiv ℝ (fderiv ℝ (chart F x))) m) m := by
  have h := ((contDiffOn_chart hF x).fderiv_of_isOpen isOpen_invLocus (m := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (by exact_mod_cast le_top)).fderiv_of_isOpen isOpen_invLocus (m := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (by exact_mod_cast le_top)
  exact ((h.differentiableOn (by simp)) m hm).differentiableAt (isOpen_invLocus.mem_nhds hm) |>.hasFDerivAt

theorem fderiv_fderiv_chart_symm {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : WhittakerBlock.IsArchSmooth3 F)
    (x : AdelicGL 3 (𝓞 ℚ) ℚ) {m : E33} (hm : m ∈ invLocus) (v w : E33) :
    fderiv ℝ (fderiv ℝ (chart F x)) m v w = fderiv ℝ (fderiv ℝ (chart F x)) m w v :=
  (((contDiffOn_chart hF x).contDiffAt (isOpen_invLocus.mem_nhds hm)).isSymmSndFDerivAt
    (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)) v w

theorem fderiv3_chart_symm₂₃ {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : WhittakerBlock.IsArchSmooth3 F)
    (x : AdelicGL 3 (𝓞 ℚ) ℚ) (v w u : E33) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (chart F x))) idE v w u = fderiv ℝ (fderiv ℝ (fderiv ℝ (chart F x))) idE v u w := by
  set f := chart F x with hf
  set D3 := fderiv ℝ (fderiv ℝ (fderiv ℝ f)) idE with hD3
  have hfffd : HasFDerivAt (fderiv ℝ (fderiv ℝ f)) D3 idE := hasFDerivAt_fderiv_fderiv_chart hF x idE_mem_invLocus

  have hsc : ∀ a b : E33, HasFDerivAt (fun m => fderiv ℝ (fderiv ℝ f) m a b)
      ((((fderiv ℝ (fderiv ℝ f) idE) a).comp (0 : E33 →L[ℝ] E33) + (D3.flip a).flip b)) idE := by
    intro a b
    have h1 : HasFDerivAt (fun m => fderiv ℝ (fderiv ℝ f) m a)
        ((fderiv ℝ (fderiv ℝ f) idE).comp (0 : E33 →L[ℝ] E33) + D3.flip a) idE :=
      hfffd.clm_apply (hasFDerivAt_const a idE)
    have h1' : HasFDerivAt (fun m => fderiv ℝ (fderiv ℝ f) m a) (D3.flip a) idE := by
      simpa using h1
    exact h1'.clm_apply (hasFDerivAt_const b idE)
  have hEq : (fun m => fderiv ℝ (fderiv ℝ f) m w u) =ᶠ[𝓝 idE] fun m => fderiv ℝ (fderiv ℝ f) m u w := by
    filter_upwards [isOpen_invLocus.mem_nhds idE_mem_invLocus] with m hm
    exact fderiv_fderiv_chart_symm hF x hm w u
  have h := hEq.fderiv_eq (𝕜 := ℝ)
  rw [(hsc w u).fderiv, (hsc u w).fderiv] at h
  have h2 := congrArg (fun T : E33 →L[ℝ] ℂ => T v) h
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
    map_zero, zero_add, ContinuousLinearMap.flip_apply] at h2
  exact h2

theorem casimir3_eq_neg_omega3T_chart {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : WhittakerBlock.IsArchSmooth3 F)
    (x : AdelicGL 3 (𝓞 ℚ) ℚ) : WhittakerBlock.casimir3 F x = -omega3T (chart F x) idE := by
  set f := chart F x with hf
  set D1 := fderiv ℝ f idE with hD1
  set D2 := fderiv ℝ (fderiv ℝ f) idE with hD2
  set D3 := fderiv ℝ (fderiv ℝ (fderiv ℝ f)) idE with hD3
  have hcf := contDiffOn_chart hF x
  have hfd : ∀ {m}, m ∈ invLocus → HasFDerivAt f (fderiv ℝ f m) m := fun {m} hm =>
    ((hcf.differentiableOn (by simp)) m hm).differentiableAt (isOpen_invLocus.mem_nhds hm) |>.hasFDerivAt
  have hffd : ∀ {m}, m ∈ invLocus → HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) m) m := fun {m} hm =>
    hasFDerivAt_fderiv_chart hF x hm
  have hfffd : HasFDerivAt (fderiv ℝ (fderiv ℝ f)) D3 idE := hasFDerivAt_fderiv_fderiv_chart hF x idE_mem_invLocus

  have hR2 : ∀ (j k l i : Fin 3) {m : E33}, m ∈ invLocus →
      WhittakerBlock.archDeriv j k (WhittakerBlock.archDeriv l i F) (x * WhittakerBlock.archRealLift3 m) =
        (fderiv ℝ f m) (colDirL l i (colDirL j k m)) + (fderiv ℝ (fderiv ℝ f) m) (colDirL j k m) (colDirL l i m) := by
    intro j k l i m hm
    have hev : (fun t => WhittakerBlock.archDeriv l i F
        (x * WhittakerBlock.archRealLift3 m * WhittakerBlock.archRealLift3 (dirE j k t))) =ᶠ[𝓝 0]
        fun t => (fderiv ℝ f (m + t • colDir j k m)) (colDirL l i (m + t • colDir j k m)) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with t ht
      have ht1 := one_add_ne_zero_of_mem_ball ht
      have hmt : (fun a b => (Matrix.of m * Matrix.of (dirE j k t)) a b) ∈ invLocus := by
        show (Matrix.of (fun a b => (Matrix.of m * Matrix.of (dirE j k t)) a b)).det ≠ 0
        change (Matrix.of m * Matrix.of (dirE j k t)).det ≠ 0
        rw [Matrix.det_mul]; exact mul_ne_zero hm (det_of_dirE_ne_zero j k ht1)
      rw [mul_assoc, archRealLift3_mul hm (det_of_dirE_ne_zero j k ht1), archDeriv_apply_chart hF x hmt,
        of_mul_of_dirE, colDirL_apply]
    have hg : HasFDerivAt (fun m => (fderiv ℝ f m) (colDirL l i m))
        ((fderiv ℝ f m).comp (colDirL l i) + (fderiv ℝ (fderiv ℝ f) m).flip (colDirL l i m)) (m + (0 : ℝ) • colDir j k m) := by
      simpa using (hffd hm).clm_apply (colDirL l i).hasFDerivAt
    have hc : HasDerivAt (fun t : ℝ => m + t • colDir j k m) (colDir j k m) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (colDir j k m)).const_add m
    show deriv (fun t => WhittakerBlock.archDeriv l i F
      (x * WhittakerBlock.archRealLift3 m * WhittakerBlock.archRealLift3 (dirE j k t))) 0 = _
    rw [hev.deriv_eq, show (fun t : ℝ => (fderiv ℝ f (m + t • colDir j k m)) (colDirL l i (m + t • colDir j k m))) =
      (fun m => (fderiv ℝ f m) (colDirL l i m)) ∘ (fun t : ℝ => m + t • colDir j k m) from rfl,
      (hg.comp_hasDerivAt (0 : ℝ) hc).deriv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      colDirL_apply]

  have hR3 : ∀ i j k : Fin 3,
      WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j k (WhittakerBlock.archDeriv k i F)) x =
        D1 (mulE (mulE (stdE i j) (stdE j k)) (stdE k i)) + D2 (stdE i j) (mulE (stdE j k) (stdE k i)) +
          (D2 (stdE j k) (mulE (stdE i j) (stdE k i)) + D2 (mulE (stdE i j) (stdE j k)) (stdE k i) +
            D3 (stdE i j) (stdE j k) (stdE k i)) := by
    intro i j k

    set g₂ : E33 → ℂ := fun m => (fderiv ℝ f m) (((colDirL k i).comp (colDirL j k)) m) +
      ((fderiv ℝ (fderiv ℝ f) m) (colDirL j k m)) (colDirL k i m) with hg₂
    have hev : (fun s => WhittakerBlock.archDeriv j k (WhittakerBlock.archDeriv k i F)
        (x * WhittakerBlock.archRealLift3 (dirE i j s))) =ᶠ[𝓝 0] fun s => g₂ (idE + s • stdE i j) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with s hs
      rw [hR2 j k k i (det_of_dirE_ne_zero i j (one_add_ne_zero_of_mem_ball hs)), dirE_eq]
      simp only [hg₂, ContinuousLinearMap.comp_apply]

    have h1 : HasFDerivAt (fun m => (fderiv ℝ f m) (((colDirL k i).comp (colDirL j k)) m))
        (D1.comp ((colDirL k i).comp (colDirL j k)) + D2.flip (((colDirL k i).comp (colDirL j k)) idE)) idE :=
      (hffd idE_mem_invLocus).clm_apply ((colDirL k i).comp (colDirL j k)).hasFDerivAt
    have h2a : HasFDerivAt (fun m => (fderiv ℝ (fderiv ℝ f) m) (colDirL j k m))
        (D2.comp (colDirL j k) + D3.flip (colDirL j k idE)) idE :=
      hfffd.clm_apply (colDirL j k).hasFDerivAt
    have h2 : HasFDerivAt (fun m => ((fderiv ℝ (fderiv ℝ f) m) (colDirL j k m)) (colDirL k i m))
        (((fderiv ℝ (fderiv ℝ f) idE) (colDirL j k idE)).comp (colDirL k i) +
          (D2.comp (colDirL j k) + D3.flip (colDirL j k idE)).flip (colDirL k i idE)) idE :=
      h2a.clm_apply (colDirL k i).hasFDerivAt
    have hg' := h1.add h2
    have hg : HasFDerivAt g₂ _ idE := hg'
    have hc : HasDerivAt (fun s : ℝ => idE + s • stdE i j) (stdE i j) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (stdE i j)).const_add idE
    show deriv (fun s => WhittakerBlock.archDeriv j k (WhittakerBlock.archDeriv k i F)
      (x * WhittakerBlock.archRealLift3 (dirE i j s))) 0 = _
    rw [hev.deriv_eq, show (fun s : ℝ => g₂ (idE + s • stdE i j)) = g₂ ∘ (fun s : ℝ => idE + s • stdE i j) from rfl,
      (hg.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)).deriv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      colDirL_apply, colDir_eq_mulE, mulE_idE_left, ← hD2]
    abel

  have hL2 : ∀ (j k i j' : Fin 3) {m : E33}, m ∈ invLocus →
      leftDeriv j k (leftDeriv i j' f) m =
        (fderiv ℝ f m) (rowDirL i j' (rowDirL j k m)) + (fderiv ℝ (fderiv ℝ f) m) (rowDirL j k m) (rowDirL i j' m) := by
    intro j k i j' m hm
    have hg : HasFDerivAt (fun m => (fderiv ℝ f m) (rowDirL i j' m))
        ((fderiv ℝ f m).comp (rowDirL i j') + (fderiv ℝ (fderiv ℝ f) m).flip (rowDirL i j' m)) m :=
      (hffd hm).clm_apply (rowDirL i j').hasFDerivAt
    have hneg : leftDeriv i j' f = fun m => -((fderiv ℝ f m) (rowDirL i j' m)) := rfl
    rw [leftDeriv_apply, hneg, hg.fun_neg.fderiv, ContinuousLinearMap.neg_apply, neg_neg]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      rowDirL_apply]

  have hL3 : ∀ i j k : Fin 3, leftDeriv k i (leftDeriv j k (leftDeriv i j f)) idE =
      -(D1 (mulE (stdE i j) (mulE (stdE j k) (stdE k i))) + D2 (stdE k i) (mulE (stdE i j) (stdE j k)) +
        (D2 (stdE j k) (mulE (stdE i j) (stdE k i)) + D2 (mulE (stdE j k) (stdE k i)) (stdE i j) +
          D3 (stdE k i) (stdE j k) (stdE i j))) := by
    intro i j k
    set h₂ : E33 → ℂ := fun m => (fderiv ℝ f m) (((rowDirL i j).comp (rowDirL j k)) m) +
      ((fderiv ℝ (fderiv ℝ f) m) (rowDirL j k m)) (rowDirL i j m) with hh₂
    have hEq : leftDeriv j k (leftDeriv i j f) =ᶠ[𝓝 idE] h₂ := by
      filter_upwards [isOpen_invLocus.mem_nhds idE_mem_invLocus] with m hm
      rw [hL2 j k i j hm]
      simp only [hh₂, ContinuousLinearMap.comp_apply]
    have h1 : HasFDerivAt (fun m => (fderiv ℝ f m) (((rowDirL i j).comp (rowDirL j k)) m))
        (D1.comp ((rowDirL i j).comp (rowDirL j k)) + D2.flip (((rowDirL i j).comp (rowDirL j k)) idE)) idE :=
      (hffd idE_mem_invLocus).clm_apply ((rowDirL i j).comp (rowDirL j k)).hasFDerivAt
    have h2a : HasFDerivAt (fun m => (fderiv ℝ (fderiv ℝ f) m) (rowDirL j k m))
        (D2.comp (rowDirL j k) + D3.flip (rowDirL j k idE)) idE :=
      hfffd.clm_apply (rowDirL j k).hasFDerivAt
    have h2 : HasFDerivAt (fun m => ((fderiv ℝ (fderiv ℝ f) m) (rowDirL j k m)) (rowDirL i j m))
        (((fderiv ℝ (fderiv ℝ f) idE) (rowDirL j k idE)).comp (rowDirL i j) +
          (D2.comp (rowDirL j k) + D3.flip (rowDirL j k idE)).flip (rowDirL i j idE)) idE :=
      h2a.clm_apply (rowDirL i j).hasFDerivAt
    have hg : HasFDerivAt h₂ _ idE := h1.add h2
    rw [leftDeriv_apply, hEq.fderiv_eq, hg.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      rowDirL_apply, rowDir_eq_mulE, mulE_idE_right, ← hD2]
    abel

  show ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j k (WhittakerBlock.archDeriv k i F)) x = _
  simp only [omega3T, hR3, hL3, Finset.sum_neg_distrib, neg_neg, Finset.sum_add_distrib]
  have hsymm2 : ∀ v w, D2 v w = D2 w v := fun v w => fderiv_fderiv_chart_symm hF x idE_mem_invLocus v w
  have hsymm3 : ∀ v w u, D3 v w u = D3 v u w := fun v w u => fderiv3_chart_symm₂₃ hF x v w u

  have e1 : ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D1 (mulE (mulE (stdE i j) (stdE j k)) (stdE k i)) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D1 (mulE (stdE i j) (mulE (stdE j k) (stdE k i))) := by
    simp only [mulE_assoc]

  have e2 : ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D2 (stdE i j) (mulE (stdE j k) (stdE k i)) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D2 (mulE (stdE j k) (stdE k i)) (stdE i j) := by
    simp only [hsymm2 (stdE _ _) (mulE _ _)]
  have e3 : ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D2 (mulE (stdE i j) (stdE j k)) (stdE k i) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D2 (stdE k i) (mulE (stdE i j) (stdE j k)) := by
    simp only [hsymm2 (stdE _ _) (mulE _ _)]

  have e4 : ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D3 (stdE i j) (stdE j k) (stdE k i) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D3 (stdE k i) (stdE j k) (stdE i j) := by
    conv_rhs => arg 2; ext i; rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]

    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    exact hsymm3 _ _ _
  rw [e1, e2, e3, e4]
  abel

theorem chart_eq_archChart : chart = SlabL2.archChart := rfl

end LanglandsTunnell.CubicInduction.ArchConvCalculus

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_apply_eq_kernelCasimir_archChart.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2 P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_apply_eq_kernelCasimir_archChart.LanglandsTunnell.CubicInduction.ArchConvCalculus"

theorem solution (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : WhittakerBlock.IsArchSmooth3 F) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archChart F x (fun a b => if a = b then 1 else 0) = F x ∧
      WhittakerBlock.casimir1 F x = -kernelCasimir1 (archChart F x) (fun a b => if a = b then 1 else 0) ∧
        WhittakerBlock.casimir2 F x = kernelCasimir2 (archChart F x) (fun a b => if a = b then 1 else 0) ∧
          WhittakerBlock.casimir3 F x = -kernelCasimir3T (archChart F x) (fun a b => if a = b then 1 else 0) :=
  ⟨chart_idE F x, casimir1_eq_neg_omega1_chart hF x, casimir2_eq_omega2_chart hF x, casimir3_eq_neg_omega3T_chart hF x⟩

end

end S_LanglandsTunnell_CubicInduction_SlabL2_casimir_apply_eq_kernelCasimir_archChart
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_apply_eq_kernelCasimir_archChart (solution)
