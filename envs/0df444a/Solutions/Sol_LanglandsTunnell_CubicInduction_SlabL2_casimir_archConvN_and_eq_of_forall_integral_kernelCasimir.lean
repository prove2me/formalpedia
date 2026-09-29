-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.SlabL2.casimir_archConvN_and_eq_of_forall_integral_kernelCasimir
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/4bef8ddf-3027-525a-877d-56250775aaeb

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2KernelCasimir
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_archConvN_and_eq_of_forall_integral_kernelCasimir

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm Matrix MeasureTheory Topology Filter TopologicalSpace

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.kernelEnt SlabL2.kernelLeftDeriv SlabL2.kernelCasimir1 SlabL2.kernelCasimir2 SlabL2.kernelCasimir3 SlabL2.kernelCasimir3T SlabL2.realCoordinate SlabL2.archEntries SlabL2.IsSmoothArchFactor AdelicGL archComponent3 WhittakerBlock.archDeriv WhittakerBlock.casimir1 WhittakerBlock.casimir2 WhittakerBlock.casimir3"
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

@[reducible] def ginfMeasurableSpace : MeasurableSpace (GL (Fin 3) (InfiniteAdeleRing ℚ)) :=
  AutomorphicForm.archGLBorelN (Fin 3) ℚ

attribute [local instance] ginfMeasurableSpace

theorem ginfBorelSpace : BorelSpace (GL (Fin 3) (InfiniteAdeleRing ℚ)) :=
  AutomorphicForm.borelSpace_archGLBorelN (Fin 3) ℚ

attribute [local instance] ginfBorelSpace

theorem locallyCompactSpace_ginf : LocallyCompactSpace (GL (Fin 3) (InfiniteAdeleRing ℚ)) :=
  AutomorphicForm.locallyCompactSpace_archGLN (Fin 3) ℚ

attribute [local instance] locallyCompactSpace_ginf

abbrev muInf : Measure (GL (Fin 3) (InfiniteAdeleRing ℚ)) := AutomorphicForm.archGLHaarN (Fin 3) ℚ

theorem isHaarMeasure_μ : muInf.IsHaarMeasure := AutomorphicForm.isHaarMeasure_archGLHaarN (Fin 3) ℚ

attribute [local instance] isHaarMeasure_μ

theorem archConvN_eq (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (α : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archConvN (Fin 3) ℚ Φ α g = ∫ h, Φ (g * archInclN (Fin 3) ℚ h) * α h ∂muInf := rfl

theorem archConvN_mul_archInclN (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (α : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ)
    (y : AdelicGL 3 (𝓞 ℚ) ℚ) (l : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    archConvN (Fin 3) ℚ Φ α (y * archInclN (Fin 3) ℚ l) = archConvN (Fin 3) ℚ Φ (fun h => α (l⁻¹ * h)) y := by
  rw [archConvN_eq, archConvN_eq,
    ← integral_mul_left_eq_self (fun h => Φ (y * archInclN (Fin 3) ℚ h) * α (l⁻¹ * h)) l]
  simp only [map_mul, mul_assoc, inv_mul_cancel_left]

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

def invParamDeriv (i j : Fin 3) (s : ℝ) : ℝ := if i = j then -1 / (1 + s) ^ 2 else -1

theorem invParamDeriv_zero (i j : Fin 3) : invParamDeriv i j 0 = -1 := by
  simp [invParamDeriv]

theorem hasDerivAt_invParam (i j : Fin 3) {s : ℝ} (hs : 1 + s ≠ 0) :
    HasDerivAt (invParam i j) (invParamDeriv i j s) s := by
  unfold invParam invParamDeriv
  by_cases hij : i = j
  · simp only [hij, if_true]
    have h1 : HasDerivAt (fun s : ℝ => -s) (-1) s := (hasDerivAt_id s).neg
    have h2 : HasDerivAt (fun s : ℝ => 1 + s) 1 s := (hasDerivAt_id s).const_add 1
    convert h1.div h2 hs using 1
    · rfl
    · rfl
    · rfl
    field_simp
    ring
  · simp only [hij, if_false]
    exact (hasDerivAt_id s).neg

theorem abs_invParamDeriv_le (i j : Fin 3) {s : ℝ} (hs : |s| ≤ 1 / 2) : |invParamDeriv i j s| ≤ 4 := by
  unfold invParamDeriv
  by_cases hij : i = j
  · simp only [hij, if_true]
    have h1 : 1 / 2 ≤ 1 + s := by
      have := neg_abs_le s
      linarith
    rw [abs_div, abs_neg, abs_one, abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
    nlinarith
  · simp only [hij, if_false, abs_neg, abs_one]
    norm_num

theorem abs_invParam_le (i j : Fin 3) {s : ℝ} (hs : |s| ≤ 1 / 2) : |invParam i j s| ≤ 1 := by
  unfold invParam
  by_cases hij : i = j
  · simp only [hij, if_true]
    have h1 : 1 / 2 ≤ 1 + s := by
      have := neg_abs_le s
      linarith
    rw [abs_div, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 + s), div_le_iff₀ (by positivity)]
    have := le_abs_self s
    linarith
  · simp only [hij, if_false, abs_neg]
    linarith

theorem one_add_ne_zero_of_abs_le {s : ℝ} (hs : |s| ≤ 1 / 2) : 1 + s ≠ 0 := by
  have := neg_abs_le s
  intro h
  linarith

theorem one_add_ne_zero_of_mem_ball {s : ℝ} (hs : s ∈ Metric.ball (0 : ℝ) (1 / 2)) : 1 + s ≠ 0 := by
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
  exact one_add_ne_zero_of_abs_le hs.le

theorem shear_zero (i j : Fin 3) (m : E33) : shear i j 0 m = m := by
  funext a b; simp [shear]

theorem shear_shear_invParam (i j : Fin 3) {s : ℝ} (hs : 1 + s ≠ 0) (m : E33) :
    shear i j s (shear i j (invParam i j s) m) = m := by
  rw [← of_dirE_mul, ← of_dirE_mul]
  funext a b
  change (Matrix.of (dirE i j s) * (Matrix.of (dirE i j (invParam i j s)) * Matrix.of m)) a b = m a b
  rw [← Matrix.mul_assoc, of_dirE_mul_of_dirE_invParam i j hs, Matrix.one_mul, Matrix.of_apply]

theorem det_shear (i j : Fin 3) (t : ℝ) (m : E33) :
    (Matrix.of (shear i j t m)).det = (Matrix.of (dirE i j t)).det * (Matrix.of m).det := by
  rw [← Matrix.det_mul, ← of_dirE_mul]
  rfl

theorem continuous_shear_uncurry (i j : Fin 3) : Continuous fun p : ℝ × E33 => shear i j p.1 p.2 := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [shear]
  have h1 : Continuous fun p : ℝ × E33 => p.2 a b := by fun_prop
  have h2 : Continuous fun p : ℝ × E33 => p.2 j b := by fun_prop
  refine h1.add (continuous_fst.mul ?_)
  split_ifs
  · exact h2
  · exact continuous_const

def shearBox (i j : Fin 3) (β : E33 → ℂ) : Set E33 :=
  (fun p : ℝ × E33 => shear i j p.1 p.2) '' (Metric.closedBall (0 : ℝ) (1 / 2) ×ˢ tsupport β)

theorem isCompact_shearBox (i j : Fin 3) {β : E33 → ℂ} (hβ : SlabL2.IsSmoothArchFactor β) :
    IsCompact (shearBox i j β) :=
  ((isCompact_closedBall (0 : ℝ) (1 / 2)).prod hβ.2.1).image (continuous_shear_uncurry i j)

theorem shearBox_subset (i j : Fin 3) {β : E33 → ℂ} (hβ : SlabL2.IsSmoothArchFactor β) :
    shearBox i j β ⊆ {m | (Matrix.of m).det ≠ 0} := by
  rintro _ ⟨⟨t, m⟩, ⟨ht, hm⟩, rfl⟩
  show (Matrix.of (shear i j t m)).det ≠ 0
  rw [det_shear]
  refine mul_ne_zero (det_of_dirE_ne_zero i j ?_) (hβ.2.2 hm)
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at ht
  exact one_add_ne_zero_of_abs_le ht

theorem continuous_shear (i j : Fin 3) (t : ℝ) : Continuous (shear i j t) :=
  (continuous_shear_uncurry i j).comp (continuous_const.prodMk continuous_id)

theorem enat_top_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp

theorem archConvN_mul_archRealLift3_dirE (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (β : E33 → ℂ) (i j : Fin 3)
    (y : AdelicGL 3 (𝓞 ℚ) ℚ) (s : ℝ) (hs : 1 + s ≠ 0) :
    archConvN (Fin 3) ℚ Φ (fun h => β (ent h)) (y * WhittakerBlock.archRealLift3 (dirE i j s)) =
      ∫ h, Φ (y * archInclN (Fin 3) ℚ h) * β (shear i j (invParam i j s) (ent h)) ∂muInf := by
  rw [archRealLift3_dirE i j s hs, archConvN_mul_archInclN, archConvN_eq]
  simp only [ent_lineElt_inv_mul]

theorem archDeriv_archConvN (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hΦ : Continuous Φ) {β : E33 → ℂ}
    (hβ : SlabL2.IsSmoothArchFactor β) (i j : Fin 3) :
    WhittakerBlock.archDeriv i j (archConvN (Fin 3) ℚ Φ fun h => β (ent h)) =
      archConvN (Fin 3) ℚ Φ fun h => leftDeriv i j β (ent h) := by
  funext y

  set Fk : ℝ → GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ :=
    fun s h => Φ (y * archInclN (Fin 3) ℚ h) * β (shear i j (invParam i j s) (ent h)) with hFk
  set Fk' : ℝ → GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ :=
    fun s h => Φ (y * archInclN (Fin 3) ℚ h) *
      (fderiv ℝ β (shear i j (invParam i j s) (ent h))) (invParamDeriv i j s • rowDir i j (ent h)) with hFk'
  have hΦc : Continuous fun h : GL (Fin 3) (InfiniteAdeleRing ℚ) => Φ (y * archInclN (Fin 3) ℚ h) :=
    hΦ.comp (continuous_const.mul continuous_archInclN)
  have hβd : Differentiable ℝ β := hβ.1.differentiable enat_top_ne_zero
  have hβfc : Continuous (fderiv ℝ β) := hβ.1.continuous_fderiv enat_top_ne_zero
  have hFkc : ∀ s, Continuous (Fk s) := fun s =>
    hΦc.mul (hβ.1.continuous.comp ((continuous_shear i j _).comp continuous_ent))
  have hFk'c : ∀ s, Continuous (Fk' s) := fun s =>
    hΦc.mul ((hβfc.comp ((continuous_shear i j _).comp continuous_ent)).clm_apply
      ((continuous_const (y := invParamDeriv i j s)).smul ((rowDirL i j).continuous.comp continuous_ent)))

  have hT := isCompact_shearBox i j hβ
  have hTloc := shearBox_subset i j hβ
  have hHT : IsCompact (ent ⁻¹' shearBox i j β) := isCompact_preimage_ent hT hTloc
  obtain ⟨B, hB⟩ : ∃ B, ∀ m, ‖fderiv ℝ β m‖ ≤ B := (hβ.2.1.fderiv (𝕜 := ℝ)).exists_bound_of_continuous hβfc
  obtain ⟨R, hR⟩ : ∃ R, ∀ m ∈ shearBox i j β, ‖m‖ ≤ R := hT.exists_bound_of_continuousOn continuousOn_id
  obtain ⟨M, hM⟩ : ∃ M, ∀ h ∈ ent ⁻¹' shearBox i j β, ‖Φ (y * archInclN (Fin 3) ℚ h)‖ ≤ M :=
    hHT.exists_bound_of_continuousOn hΦc.continuousOn

  have hbox : ∀ (s : ℝ), |s| ≤ 1 / 2 → ∀ h : GL (Fin 3) (InfiniteAdeleRing ℚ),
      shear i j (invParam i j s) (ent h) ∈ tsupport β → h ∈ ent ⁻¹' shearBox i j β := by
    intro s hs h hm
    refine ⟨(s, shear i j (invParam i j s) (ent h)), ⟨?_, hm⟩, ?_⟩
    · rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    · exact shear_shear_invParam i j (one_add_ne_zero_of_abs_le hs) (ent h)
  have hzero : ∀ (s : ℝ), |s| ≤ 1 / 2 → ∀ h : GL (Fin 3) (InfiniteAdeleRing ℚ),
      h ∉ ent ⁻¹' shearBox i j β → Fk' s h = 0 := by
    intro s hs h hh
    have hm : shear i j (invParam i j s) (ent h) ∉ tsupport β := fun hm => hh (hbox s hs h hm)
    simp only [hFk', fderiv_of_notMem_tsupport ℝ hm, ContinuousLinearMap.zero_apply, mul_zero]

  have hkey : HasDerivAt (fun s => ∫ h, Fk s h ∂muInf) (∫ h, Fk' 0 h ∂muInf) 0 := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := muInf) (F := Fk) (F' := Fk') (x₀ := (0 : ℝ))
      (bound := (ent ⁻¹' shearBox i j β).indicator fun _ => M * (B * (4 * R)))
      (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)) ?_ ?_ ?_ ?_ ?_ ?_).2
    · exact Filter.Eventually.of_forall fun s => (hFkc s).aestronglyMeasurable
    · have h0 : Fk 0 = fun h => Φ (y * archInclN (Fin 3) ℚ h) * β (ent h) := by
        funext h; simp only [hFk, invParam_zero, shear_zero]
      rw [h0]
      exact (hΦc.mul (hβ.1.continuous.comp continuous_ent)).integrable_of_hasCompactSupport
        ((hasCompactSupport_comp_ent hβ).mul_left)
    · exact (hFk'c 0).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun h s hs => ?_
      have hs' : |s| ≤ 1 / 2 := by
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs; exact hs.le
      by_cases hh : h ∈ ent ⁻¹' shearBox i j β
      · rw [Set.indicator_of_mem hh]
        have hM0 : ‖Φ (y * archInclN (Fin 3) ℚ h)‖ ≤ M := hM h hh
        have hMnn : 0 ≤ M := (norm_nonneg _).trans hM0
        have hRh : ‖ent h‖ ≤ R := hR _ hh
        have hBnn : 0 ≤ B := (norm_nonneg _).trans (hB 0)
        calc ‖Fk' s h‖ = ‖Φ (y * archInclN (Fin 3) ℚ h)‖ *
              ‖(fderiv ℝ β (shear i j (invParam i j s) (ent h))) (invParamDeriv i j s • rowDir i j (ent h))‖ := by
              rw [hFk', norm_mul]
          _ ≤ M * (B * (4 * R)) := by
              refine mul_le_mul hM0 ?_ (norm_nonneg _) hMnn
              refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
              refine mul_le_mul (hB _) ?_ (norm_nonneg _) hBnn
              rw [norm_smul, Real.norm_eq_abs]
              exact mul_le_mul (abs_invParamDeriv_le i j hs') ((norm_rowDir_le i j _).trans hRh) (norm_nonneg _)
                (by norm_num)
      · rw [hzero s hs' h hh, Set.indicator_of_notMem hh, norm_zero]
    · exact (integrableOn_const (hs := hHT.measure_lt_top.ne)).integrable_indicator hHT.isClosed.measurableSet
    · refine Filter.Eventually.of_forall fun h s hs => ?_
      have hs1 : 1 + s ≠ 0 := one_add_ne_zero_of_mem_ball hs
      have hc : HasDerivAt (fun s => shear i j (invParam i j s) (ent h)) (invParamDeriv i j s • rowDir i j (ent h)) s := by
        have := ((hasDerivAt_invParam i j hs1).smul_const (rowDir i j (ent h))).const_add (ent h)
        simpa only [shear_eq] using this
      exact ((hβd _).hasFDerivAt.comp_hasDerivAt s hc).const_mul _

  have hev : (fun s => archConvN (Fin 3) ℚ Φ (fun h => β (ent h)) (y * WhittakerBlock.archRealLift3 (dirE i j s)))
      =ᶠ[𝓝 0] fun s => ∫ h, Fk s h ∂muInf := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with s hs
    exact archConvN_mul_archRealLift3_dirE Φ β i j y s (one_add_ne_zero_of_mem_ball hs)
  show deriv (fun s => archConvN (Fin 3) ℚ Φ (fun h => β (ent h))
    (y * WhittakerBlock.archRealLift3 (dirE i j s))) 0 = _
  rw [hev.deriv_eq, hkey.deriv, archConvN_eq]
  congr 1
  funext h
  simp only [hFk', invParam_zero, shear_zero, invParamDeriv_zero, neg_one_smul, map_neg, leftDeriv_apply, mul_neg]

theorem integrable_mul_kernel (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hΦ : Continuous Φ) {β : E33 → ℂ}
    (hβ : SlabL2.IsSmoothArchFactor β) (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Integrable (fun h => Φ (y * archInclN (Fin 3) ℚ h) * β (ent h)) muInf :=
  ((hΦ.comp (continuous_const.mul continuous_archInclN)).mul
    (hβ.1.continuous.comp continuous_ent)).integrable_of_hasCompactSupport (hasCompactSupport_comp_ent hβ).mul_left

theorem archConvN_finset_sum_apply (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) {ι : Type*} (S : Finset ι)
    (α : ι → GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ) (y : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hα : ∀ k ∈ S, Integrable (fun h => Φ (y * archInclN (Fin 3) ℚ h) * α k h) muInf) :
    archConvN (Fin 3) ℚ Φ (fun h => ∑ k ∈ S, α k h) y = ∑ k ∈ S, archConvN (Fin 3) ℚ Φ (α k) y := by
  simp only [archConvN_eq, Finset.mul_sum]
  exact integral_finsetSum S hα

def omega1 (β : E33 → ℂ) : E33 → ℂ := fun m => ∑ i : Fin 3, leftDeriv i i β m

def omega2 (β : E33 → ℂ) : E33 → ℂ := fun m => ∑ i : Fin 3, ∑ j : Fin 3, leftDeriv i j (leftDeriv j i β) m

def omega3 (β : E33 → ℂ) : E33 → ℂ :=
  fun m => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, leftDeriv i j (leftDeriv j k (leftDeriv k i β)) m

theorem casimir1_archConvN (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hΦ : Continuous Φ) {β : E33 → ℂ}
    (hβ : SlabL2.IsSmoothArchFactor β) :
    WhittakerBlock.casimir1 (archConvN (Fin 3) ℚ Φ fun h => β (ent h)) =
      archConvN (Fin 3) ℚ Φ fun h => omega1 β (ent h) := by
  funext y
  show ∑ i : Fin 3, WhittakerBlock.archDeriv i i (archConvN (Fin 3) ℚ Φ fun h => β (ent h)) y = _
  simp only [archDeriv_archConvN Φ hΦ hβ]
  unfold omega1
  rw [archConvN_finset_sum_apply]
  exact fun k _ => integrable_mul_kernel Φ hΦ (isSmoothArchFactor_leftDeriv k k hβ) y

theorem casimir2_archConvN (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hΦ : Continuous Φ) {β : E33 → ℂ}
    (hβ : SlabL2.IsSmoothArchFactor β) :
    WhittakerBlock.casimir2 (archConvN (Fin 3) ℚ Φ fun h => β (ent h)) =
      archConvN (Fin 3) ℚ Φ fun h => omega2 β (ent h) := by
  funext y
  show ∑ i : Fin 3, ∑ j : Fin 3, WhittakerBlock.archDeriv i j
    (WhittakerBlock.archDeriv j i (archConvN (Fin 3) ℚ Φ fun h => β (ent h))) y = _
  have h1 : ∀ i j : Fin 3, WhittakerBlock.archDeriv i j
      (WhittakerBlock.archDeriv j i (archConvN (Fin 3) ℚ Φ fun h => β (ent h))) =
      archConvN (Fin 3) ℚ Φ fun h => leftDeriv i j (leftDeriv j i β) (ent h) := fun i j => by
    rw [archDeriv_archConvN Φ hΦ hβ, archDeriv_archConvN Φ hΦ (isSmoothArchFactor_leftDeriv j i hβ)]
  simp only [h1]
  unfold omega2
  rw [archConvN_finset_sum_apply]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [archConvN_finset_sum_apply]
    exact fun j _ => integrable_mul_kernel Φ hΦ
      (isSmoothArchFactor_leftDeriv i j (isSmoothArchFactor_leftDeriv j i hβ)) y
  · intro i _
    have := fun j => integrable_mul_kernel Φ hΦ
      (isSmoothArchFactor_leftDeriv i j (isSmoothArchFactor_leftDeriv j i hβ)) y
    simp only [Finset.mul_sum]
    exact integrable_finsetSum _ fun j _ => this j

theorem casimir3_archConvN (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hΦ : Continuous Φ) {β : E33 → ℂ}
    (hβ : SlabL2.IsSmoothArchFactor β) :
    WhittakerBlock.casimir3 (archConvN (Fin 3) ℚ Φ fun h => β (ent h)) =
      archConvN (Fin 3) ℚ Φ fun h => omega3 β (ent h) := by
  funext y
  show ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j k
    (WhittakerBlock.archDeriv k i (archConvN (Fin 3) ℚ Φ fun h => β (ent h)))) y = _
  have hL := fun a b {γ : E33 → ℂ} (hγ : SlabL2.IsSmoothArchFactor γ) => isSmoothArchFactor_leftDeriv a b hγ
  have h1 : ∀ i j k : Fin 3, WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j k
      (WhittakerBlock.archDeriv k i (archConvN (Fin 3) ℚ Φ fun h => β (ent h)))) =
      archConvN (Fin 3) ℚ Φ fun h => leftDeriv i j (leftDeriv j k (leftDeriv k i β)) (ent h) := fun i j k => by
    rw [archDeriv_archConvN Φ hΦ hβ, archDeriv_archConvN Φ hΦ (hL k i hβ),
      archDeriv_archConvN Φ hΦ (hL j k (hL k i hβ))]
  simp only [h1]
  have hint : ∀ i j k : Fin 3, Integrable (fun h => Φ (y * archInclN (Fin 3) ℚ h) *
      leftDeriv i j (leftDeriv j k (leftDeriv k i β)) (ent h)) muInf := fun i j k =>
    integrable_mul_kernel Φ hΦ (hL i j (hL j k (hL k i hβ))) y
  unfold omega3
  rw [archConvN_finset_sum_apply]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [archConvN_finset_sum_apply]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [archConvN_finset_sum_apply]
      exact fun k _ => hint i j k
    · intro j _
      simp only [Finset.mul_sum]
      exact integrable_finsetSum _ fun k _ => hint i j k
  · intro i _
    simp only [Finset.mul_sum]
    exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint i j k

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

theorem shear_mem_invLocus (i j : Fin 3) {t : ℝ} (ht : 1 + t ≠ 0) {m : E33} (hm : m ∈ invLocus) :
    shear i j t m ∈ invLocus := by
  show (Matrix.of (shear i j t m)).det ≠ 0
  rw [det_shear]
  exact mul_ne_zero (det_of_dirE_ne_zero i j ht) hm

theorem ent_lineElt_mul (i j : Fin 3) (s : ℝ) (hs : 1 + s ≠ 0) (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    ent (lineElt i j s hs * h) = shear i j s (ent h) := by
  unfold lineElt
  rw [ent_liftE_mul, of_dirE_mul]

theorem hasDerivAt_shear (i j : Fin 3) (m : E33) (s : ℝ) :
    HasDerivAt (fun s => shear i j s m) (rowDir i j m) s := by
  have := ((hasDerivAt_id s).smul_const (rowDir i j m)).const_add m
  simpa only [shear_eq, one_smul, id] using this

theorem integral_mul_leftDeriv (f : E33 → ℂ) (hf : ContDiffOn ℝ 1 f invLocus) {γ : E33 → ℂ}
    (hγ : SlabL2.IsSmoothArchFactor γ) (i j : Fin 3) :
    ∫ h, f (ent h) * leftDeriv i j γ (ent h) ∂muInf = -∫ h, leftDeriv i j f (ent h) * γ (ent h) ∂muInf := by

  set Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := fun g => f (SlabL2.archEntries g) with hΦ
  have hΦc : Continuous Φ := continuous_comp_archEntries hf.continuousOn
  have hΦι : ∀ h : GL (Fin 3) (InfiniteAdeleRing ℚ), Φ (1 * archInclN (Fin 3) ℚ h) = f (ent h) := fun h => by
    rw [one_mul]; rfl

  have hform2 : WhittakerBlock.archDeriv i j (archConvN (Fin 3) ℚ Φ fun h => γ (ent h)) 1 =
      ∫ h, f (ent h) * leftDeriv i j γ (ent h) ∂muInf := by
    rw [archDeriv_archConvN Φ hΦc hγ, archConvN_eq]
    simp only [hΦι]

  set G : ℝ → GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ := fun s h => f (shear i j s (ent h)) * γ (ent h) with hG
  set G' : ℝ → GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ :=
    fun s h => (fderiv ℝ f (shear i j s (ent h))) (rowDir i j (ent h)) * γ (ent h) with hG'
  have hfd : DifferentiableOn ℝ f invLocus := hf.differentiableOn (by simp)
  have hffc : ContinuousOn (fderiv ℝ f) invLocus := hf.continuousOn_fderiv_of_isOpen isOpen_invLocus le_rfl
  have hGc : ∀ s : ℝ, 1 + s ≠ 0 → Continuous (G s) := fun s hs =>
    (hf.continuousOn.comp_continuous ((continuous_shear i j s).comp continuous_ent)
      fun h => shear_mem_invLocus i j hs (ent_mem_invLocus h)).mul (hγ.1.continuous.comp continuous_ent)
  have hG'c : ∀ s : ℝ, 1 + s ≠ 0 → Continuous (G' s) := fun s hs =>
    ((hffc.comp_continuous ((continuous_shear i j s).comp continuous_ent)
      fun h => shear_mem_invLocus i j hs (ent_mem_invLocus h)).clm_apply
      ((rowDirL i j).continuous.comp continuous_ent)).mul (hγ.1.continuous.comp continuous_ent)
  have hT := isCompact_shearBox i j hγ
  have hTloc : shearBox i j γ ⊆ invLocus := shearBox_subset i j hγ
  have hHγ : IsCompact (ent ⁻¹' tsupport γ) := isCompact_preimage_ent hγ.2.1 hγ.2.2
  obtain ⟨B, hB⟩ : ∃ B, ∀ m ∈ shearBox i j γ, ‖fderiv ℝ f m‖ ≤ B := hT.exists_bound_of_continuousOn (hffc.mono hTloc)
  obtain ⟨R, hR⟩ : ∃ R, ∀ m ∈ tsupport γ, ‖m‖ ≤ R := hγ.2.1.exists_bound_of_continuousOn continuousOn_id
  obtain ⟨C, hC⟩ : ∃ C, ∀ m, ‖γ m‖ ≤ C := hγ.2.1.exists_bound_of_continuous hγ.1.continuous
  have hbox : ∀ (s : ℝ), |s| ≤ 1 / 2 → ∀ h : GL (Fin 3) (InfiniteAdeleRing ℚ), ent h ∈ tsupport γ →
      shear i j s (ent h) ∈ shearBox i j γ := fun s hs h hm =>
    ⟨(s, ent h), ⟨by rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs], hm⟩, rfl⟩
  have hzero : ∀ (s : ℝ) (h : GL (Fin 3) (InfiniteAdeleRing ℚ)), h ∉ ent ⁻¹' tsupport γ → G' s h = 0 :=
    fun s h hh => by simp only [hG', image_eq_zero_of_notMem_tsupport hh, mul_zero]
  have hkey : HasDerivAt (fun s => ∫ h, G s h ∂muInf) (∫ h, G' 0 h ∂muInf) 0 := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := muInf) (F := G) (F' := G') (x₀ := (0 : ℝ))
      (bound := (ent ⁻¹' tsupport γ).indicator fun _ => B * R * C)
      (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)) ?_ ?_ ?_ ?_ ?_ ?_).2
    · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with s hs
      exact (hGc s (one_add_ne_zero_of_mem_ball hs)).aestronglyMeasurable
    · have h0 : G 0 = fun h => f (ent h) * γ (ent h) := by funext h; simp only [hG, shear_zero]
      rw [h0]
      exact ((hf.continuousOn.comp_continuous continuous_ent ent_mem_invLocus).mul
        (hγ.1.continuous.comp continuous_ent)).integrable_of_hasCompactSupport (hasCompactSupport_comp_ent hγ).mul_left
    · exact (hG'c 0 (by norm_num)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun h s hs => ?_
      have hs' : |s| ≤ 1 / 2 := by
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs; exact hs.le
      by_cases hh : h ∈ ent ⁻¹' tsupport γ
      · rw [Set.indicator_of_mem hh]
        have hm : shear i j s (ent h) ∈ shearBox i j γ := hbox s hs' h hh
        have hBnn : 0 ≤ B := (norm_nonneg _).trans (hB _ hm)
        have hRnn : 0 ≤ R := (norm_nonneg _).trans (hR _ hh)
        calc ‖G' s h‖ = ‖(fderiv ℝ f (shear i j s (ent h))) (rowDir i j (ent h))‖ * ‖γ (ent h)‖ := by
              rw [hG', norm_mul]
          _ ≤ B * R * C := by
              refine mul_le_mul ?_ (hC _) (norm_nonneg _) (mul_nonneg hBnn hRnn)
              exact (ContinuousLinearMap.le_opNorm _ _).trans
                (mul_le_mul (hB _ hm) ((norm_rowDir_le i j _).trans (hR _ hh)) (norm_nonneg _) hBnn)
      · rw [hzero s h hh, Set.indicator_of_notMem hh, norm_zero]
    · exact (integrableOn_const (hs := hHγ.measure_lt_top.ne)).integrable_indicator hHγ.isClosed.measurableSet
    · refine Filter.Eventually.of_forall fun h s hs => ?_
      have hs1 : 1 + s ≠ 0 := one_add_ne_zero_of_mem_ball hs
      by_cases hh : h ∈ ent ⁻¹' tsupport γ
      · have hm : shear i j s (ent h) ∈ invLocus := shear_mem_invLocus i j hs1 (ent_mem_invLocus h)
        have hfd' : HasFDerivAt f (fderiv ℝ f (shear i j s (ent h))) (shear i j s (ent h)) :=
          ((hfd _ hm).differentiableAt (isOpen_invLocus.mem_nhds hm)).hasFDerivAt
        exact (hfd'.comp_hasDerivAt s (hasDerivAt_shear i j (ent h) s)).mul_const _
      · have hγ0 : γ (ent h) = 0 := image_eq_zero_of_notMem_tsupport hh
        have h1 : (fun s => G s h) = fun _ => 0 := by funext s; simp only [hG, hγ0, mul_zero]
        rw [h1, hzero s h hh]
        exact hasDerivAt_const s 0
  have hev : (fun s => archConvN (Fin 3) ℚ Φ (fun h => γ (ent h)) (1 * WhittakerBlock.archRealLift3 (dirE i j s)))
      =ᶠ[𝓝 0] fun s => ∫ h, G s h ∂muInf := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with s hs
    have hs1 := one_add_ne_zero_of_mem_ball hs
    rw [archRealLift3_dirE i j s hs1, archConvN_eq]
    congr 1
    funext h
    simp only [hG, one_mul, ← map_mul, hΦ, archEntries_archInclN, ent_lineElt_mul]
  have hform1 : WhittakerBlock.archDeriv i j (archConvN (Fin 3) ℚ Φ fun h => γ (ent h)) 1 =
      -∫ h, leftDeriv i j f (ent h) * γ (ent h) ∂muInf := by
    show deriv (fun s => archConvN (Fin 3) ℚ Φ (fun h => γ (ent h))
      (1 * WhittakerBlock.archRealLift3 (dirE i j s))) 0 = _
    rw [hev.deriv_eq, hkey.deriv, ← integral_neg]
    congr 1
    funext h
    simp only [hG', shear_zero, leftDeriv_apply, neg_mul, neg_neg]
  rw [← hform2, hform1]

theorem contDiffOn_leftDeriv {f : E33 → ℂ} {n m : WithTop ℕ∞} (hf : ContDiffOn ℝ n f invLocus) (hmn : m + 1 ≤ n)
    (i j : Fin 3) : ContDiffOn ℝ m (leftDeriv i j f) invLocus := by
  have h1 : ContDiffOn ℝ m (fderiv ℝ f) invLocus := hf.fderiv_of_isOpen isOpen_invLocus hmn
  have h2 : ContDiffOn ℝ m (fun x : E33 => rowDirL i j x) invLocus := (rowDirL i j).contDiff.contDiffOn
  exact (h1.clm_apply h2).neg

theorem integrable_ent_mul {f : E33 → ℂ} (hf : ContinuousOn f invLocus) {γ : E33 → ℂ}
    (hγ : SlabL2.IsSmoothArchFactor γ) : Integrable (fun h => f (ent h) * γ (ent h)) muInf :=
  ((hf.comp_continuous continuous_ent ent_mem_invLocus).mul
    (hγ.1.continuous.comp continuous_ent)).integrable_of_hasCompactSupport (hasCompactSupport_comp_ent hγ).mul_left

theorem integral_mul_leftDeriv₂ (f : E33 → ℂ) (hf : ContDiffOn ℝ 2 f invLocus) {γ : E33 → ℂ}
    (hγ : SlabL2.IsSmoothArchFactor γ) (i j k l : Fin 3) :
    ∫ h, f (ent h) * leftDeriv i j (leftDeriv k l γ) (ent h) ∂muInf =
      ∫ h, leftDeriv k l (leftDeriv i j f) (ent h) * γ (ent h) ∂muInf := by
  rw [integral_mul_leftDeriv f (hf.of_le (by norm_num)) (isSmoothArchFactor_leftDeriv k l hγ) i j,
    integral_mul_leftDeriv (leftDeriv i j f) (contDiffOn_leftDeriv hf (m := 1) (by norm_num) i j) hγ k l, neg_neg]

theorem integral_mul_leftDeriv₃ (f : E33 → ℂ) (hf : ContDiffOn ℝ 3 f invLocus) {γ : E33 → ℂ}
    (hγ : SlabL2.IsSmoothArchFactor γ) (i j k l m n : Fin 3) :
    ∫ h, f (ent h) * leftDeriv i j (leftDeriv k l (leftDeriv m n γ)) (ent h) ∂muInf =
      -∫ h, leftDeriv m n (leftDeriv k l (leftDeriv i j f)) (ent h) * γ (ent h) ∂muInf := by
  rw [integral_mul_leftDeriv₂ f (hf.of_le (by norm_num))
      (isSmoothArchFactor_leftDeriv m n hγ) i j k l,
    integral_mul_leftDeriv (leftDeriv k l (leftDeriv i j f))
      (contDiffOn_leftDeriv (contDiffOn_leftDeriv hf (m := 2) (by norm_num) i j) (m := 1) (by norm_num) k l) hγ m n]

def omega3T (f : E33 → ℂ) : E33 → ℂ :=
  fun m => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, leftDeriv k i (leftDeriv j k (leftDeriv i j f)) m

theorem integral_mul_omega1 (f : E33 → ℂ) (hf : ContDiffOn ℝ 1 f invLocus) {γ : E33 → ℂ}
    (hγ : SlabL2.IsSmoothArchFactor γ) :
    ∫ h, f (ent h) * omega1 γ (ent h) ∂muInf = -∫ h, omega1 f (ent h) * γ (ent h) ∂muInf := by
  simp only [omega1, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ => integrable_ent_mul hf.continuousOn (isSmoothArchFactor_leftDeriv i i hγ),
    integral_finsetSum _ fun i _ => integrable_ent_mul (contDiffOn_leftDeriv hf (m := 0) (by norm_num) i i).continuousOn hγ,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => integral_mul_leftDeriv f hf hγ i i

theorem integral_mul_omega2 (f : E33 → ℂ) (hf : ContDiffOn ℝ 2 f invLocus) {γ : E33 → ℂ}
    (hγ : SlabL2.IsSmoothArchFactor γ) :
    ∫ h, f (ent h) * omega2 γ (ent h) ∂muInf = ∫ h, omega2 f (ent h) * γ (ent h) ∂muInf := by
  have hL := fun a b {δ : E33 → ℂ} (hδ : SlabL2.IsSmoothArchFactor δ) => isSmoothArchFactor_leftDeriv a b hδ
  have hLf : ∀ a b c d, ContinuousOn (leftDeriv a b (leftDeriv c d f)) invLocus := fun a b c d =>
    (contDiffOn_leftDeriv (contDiffOn_leftDeriv hf (m := 1) (by norm_num) c d) (m := 0) (by norm_num) a b).continuousOn
  simp only [omega2, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_ent_mul hf.continuousOn (hL i j (hL j i hγ))]
  simp_rw [integral_finsetSum _ fun j _ => integrable_ent_mul hf.continuousOn (hL _ j (hL j _ hγ))]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => integrable_ent_mul (hLf i j j i) hγ]
  simp_rw [integral_finsetSum _ fun j _ => integrable_ent_mul (hLf _ j j _) hγ]
  simp_rw [integral_mul_leftDeriv₂ f hf hγ]
  exact Finset.sum_comm

theorem integral_mul_omega3 (f : E33 → ℂ) (hf : ContDiffOn ℝ 3 f invLocus) {γ : E33 → ℂ}
    (hγ : SlabL2.IsSmoothArchFactor γ) :
    ∫ h, f (ent h) * omega3 γ (ent h) ∂muInf = -∫ h, omega3T f (ent h) * γ (ent h) ∂muInf := by
  have hL := fun a b {δ : E33 → ℂ} (hδ : SlabL2.IsSmoothArchFactor δ) => isSmoothArchFactor_leftDeriv a b hδ
  have hLf : ∀ a b c d e e', ContinuousOn (leftDeriv a b (leftDeriv c d (leftDeriv e e' f))) invLocus :=
    fun a b c d e e' => (contDiffOn_leftDeriv (contDiffOn_leftDeriv (contDiffOn_leftDeriv hf (m := 2) (by norm_num) e e')
      (m := 1) (by norm_num) c d) (m := 0) (by norm_num) a b).continuousOn
  simp only [omega3, omega3T, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
    integrable_ent_mul hf.continuousOn (hL i j (hL j k (hL k i hγ)))]
  simp_rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
    integrable_ent_mul hf.continuousOn (hL _ j (hL j k (hL k _ hγ)))]
  simp_rw [integral_finsetSum _ fun k _ => integrable_ent_mul hf.continuousOn (hL _ _ (hL _ k (hL k _ hγ)))]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
    integrable_ent_mul (hLf k i j k i j) hγ]
  simp_rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => integrable_ent_mul (hLf k _ j k _ j) hγ]
  simp_rw [integral_finsetSum _ fun k _ => integrable_ent_mul (hLf k _ _ k _ _) hγ]
  simp_rw [integral_mul_leftDeriv₃ f hf hγ, Finset.sum_neg_distrib]

theorem eq_zero_of_forall_integral_mul_eq_zero (g : E33 → ℂ) (hg : ContinuousOn g invLocus)
    (h : ∀ β : E33 → ℂ, SlabL2.IsSmoothArchFactor β → ∫ x, g (ent x) * β (ent x) ∂muInf = 0) :
    ∀ m ∈ invLocus, g m = 0 := by
  intro m₀ hm₀
  by_contra hne

  set r : E33 → ℝ := fun m => (star (g m₀) * g m).re with hr
  have hrc : ContinuousOn r invLocus :=
    Complex.continuous_re.comp_continuousOn (continuousOn_const.mul hg)
  have hr0 : 0 < r m₀ := by
    simp only [hr]
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    exact Complex.normSq_pos.mpr hne
  set U : Set E33 := invLocus ∩ r ⁻¹' Set.Ioi 0 with hU
  have hUo : IsOpen U := hrc.isOpen_inter_preimage isOpen_invLocus isOpen_Ioi
  have hm₀U : m₀ ∈ U := ⟨hm₀, hr0⟩
  obtain ⟨ε, hε, hεU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hUo.mem_nhds hm₀U)

  let χ : ContDiffBump m₀ := ⟨ε / 2, ε, by positivity, by linarith⟩
  have hχsupp : tsupport (χ : E33 → ℝ) = Metric.closedBall m₀ ε := χ.tsupport_eq
  set β : E33 → ℂ := fun m => star (g m₀) * ((χ m : ℝ) : ℂ) with hβ
  have hβsupp : Function.support β ⊆ Function.support (χ : E33 → ℝ) := by
    intro m hm
    simp only [hβ, Function.mem_support, ne_eq, mul_eq_zero, not_or, Complex.ofReal_eq_zero] at hm ⊢
    exact hm.2
  have hβt : tsupport β ⊆ Metric.closedBall m₀ ε := by
    rw [← hχsupp]; exact closure_mono hβsupp
  have hβs : SlabL2.IsSmoothArchFactor β := by
    refine ⟨?_, ?_, hβt.trans (hεU.trans Set.inter_subset_left)⟩
    · exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp χ.contDiff)
    · exact HasCompactSupport.of_support_subset_isCompact χ.hasCompactSupport (hβsupp.trans subset_closure)

  have hint : Integrable (fun x => g (ent x) * β (ent x)) muInf := integrable_ent_mul hg hβs
  have hre : (∫ x, g (ent x) * β (ent x) ∂muInf).re = ∫ x, r (ent x) * χ (ent x) ∂muInf := by
    have := integral_re hint
    simp only [RCLike.re_to_complex] at this
    rw [← this]
    congr 1
    funext x
    simp only [hr, hβ]
    rw [show g (ent x) * (star (g m₀) * ((χ (ent x) : ℝ) : ℂ)) = (star (g m₀) * g (ent x)) * ((χ (ent x) : ℝ) : ℂ)
      by ring, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hnonneg : ∀ x : GL (Fin 3) (InfiniteAdeleRing ℚ), 0 ≤ r (ent x) * χ (ent x) := by
    intro x
    by_cases hx : χ (ent x) = 0
    · rw [hx, mul_zero]
    · have hxU : ent x ∈ U := hεU (by rw [← hχsupp]; exact subset_closure hx)
      exact mul_nonneg (le_of_lt hxU.2) χ.nonneg
  have hφc : Continuous fun x : GL (Fin 3) (InfiniteAdeleRing ℚ) => r (ent x) * χ (ent x) :=
    (hrc.comp_continuous continuous_ent ent_mem_invLocus).mul (χ.continuous.comp continuous_ent)
  have hφi : Integrable (fun x : GL (Fin 3) (InfiniteAdeleRing ℚ) => r (ent x) * χ (ent x)) muInf := by
    have := hint.re
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [hr, hβ, RCLike.re_to_complex]
    rw [show g (ent x) * (star (g m₀) * ((χ (ent x) : ℝ) : ℂ)) = (star (g m₀) * g (ent x)) * ((χ (ent x) : ℝ) : ℂ)
      by ring, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hpos : 0 < ∫ x, r (ent x) * χ (ent x) ∂muInf := by
    rw [integral_pos_iff_support_of_nonneg hnonneg hφi]

    have hx₀ : 0 < r (ent (liftE m₀ hm₀)) * χ (ent (liftE m₀ hm₀)) := by
      rw [ent_liftE]
      exact mul_pos hr0 (χ.pos_of_mem_ball (Metric.mem_ball_self χ.rOut_pos))
    have hopen : IsOpen ((fun x : GL (Fin 3) (InfiniteAdeleRing ℚ) => r (ent x) * χ (ent x)) ⁻¹' Set.Ioi 0) :=
      hφc.isOpen_preimage _ isOpen_Ioi
    refine lt_of_lt_of_le (hopen.measure_pos muInf ⟨liftE m₀ hm₀, hx₀⟩) (measure_mono ?_)
    intro x hx
    exact ne_of_gt hx
  have h0 := h β hβs
  rw [← Complex.re_add_im (∫ x, g (ent x) * β (ent x) ∂muInf), hre] at h0
  have := congrArg Complex.re h0
  simp at this
  linarith

theorem continuousOn_omega1 {f : E33 → ℂ} (hf : ContDiffOn ℝ 1 f invLocus) : ContinuousOn (omega1 f) invLocus :=
  continuousOn_finsetSum _ fun i _ => (contDiffOn_leftDeriv hf (m := 0) (by norm_num) i i).continuousOn

theorem continuousOn_omega2 {f : E33 → ℂ} (hf : ContDiffOn ℝ 2 f invLocus) : ContinuousOn (omega2 f) invLocus :=
  continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
    (contDiffOn_leftDeriv (contDiffOn_leftDeriv hf (m := 1) (by norm_num) j i) (m := 0) (by norm_num) i j).continuousOn

theorem continuousOn_omega3T {f : E33 → ℂ} (hf : ContDiffOn ℝ 3 f invLocus) : ContinuousOn (omega3T f) invLocus :=
  continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ =>
    (contDiffOn_leftDeriv (contDiffOn_leftDeriv (contDiffOn_leftDeriv hf (m := 2) (by norm_num) i j)
      (m := 1) (by norm_num) j k) (m := 0) (by norm_num) k i).continuousOn

theorem neg_omega1_eq_of_forall_integral (f : E33 → ℂ) (hf : ContDiffOn ℝ 1 f invLocus) (c : ℂ)
    (h : ∀ β : E33 → ℂ, SlabL2.IsSmoothArchFactor β →
      ∫ x, f (ent x) * omega1 β (ent x) ∂muInf = c * ∫ x, f (ent x) * β (ent x) ∂muInf) :
    ∀ m ∈ invLocus, -omega1 f m = c * f m := by
  have hg : ContinuousOn (fun m => -omega1 f m - c * f m) invLocus :=
    ((continuousOn_omega1 hf).neg).sub (continuousOn_const.mul hf.continuousOn)
  have := eq_zero_of_forall_integral_mul_eq_zero _ hg fun β hβ => by
    have h1 := h β hβ
    rw [integral_mul_omega1 f hf hβ] at h1
    simp only [sub_mul, neg_mul]
    have hI1 : Integrable (fun x => -(omega1 f (ent x) * β (ent x))) muInf :=
      (integrable_ent_mul (continuousOn_omega1 hf) hβ).neg
    rw [integral_sub hI1 ?_, integral_neg, h1]
    · simp only [mul_assoc]
      rw [integral_const_mul, sub_self]
    · simp only [mul_assoc]; exact (integrable_ent_mul hf.continuousOn hβ).const_mul c
  intro m hm
  exact sub_eq_zero.mp (this m hm)

theorem omega2_eq_of_forall_integral (f : E33 → ℂ) (hf : ContDiffOn ℝ 2 f invLocus) (c : ℂ)
    (h : ∀ β : E33 → ℂ, SlabL2.IsSmoothArchFactor β →
      ∫ x, f (ent x) * omega2 β (ent x) ∂muInf = c * ∫ x, f (ent x) * β (ent x) ∂muInf) :
    ∀ m ∈ invLocus, omega2 f m = c * f m := by
  have hg : ContinuousOn (fun m => omega2 f m - c * f m) invLocus :=
    (continuousOn_omega2 hf).sub (continuousOn_const.mul hf.continuousOn)
  have := eq_zero_of_forall_integral_mul_eq_zero _ hg fun β hβ => by
    have h1 := h β hβ
    rw [integral_mul_omega2 f hf hβ] at h1
    simp only [sub_mul]
    rw [integral_sub (integrable_ent_mul (continuousOn_omega2 hf) hβ) ?_, h1]
    · simp only [mul_assoc]
      rw [integral_const_mul, sub_self]
    · simp only [mul_assoc]; exact (integrable_ent_mul hf.continuousOn hβ).const_mul c
  intro m hm
  exact sub_eq_zero.mp (this m hm)

theorem neg_omega3T_eq_of_forall_integral (f : E33 → ℂ) (hf : ContDiffOn ℝ 3 f invLocus) (c : ℂ)
    (h : ∀ β : E33 → ℂ, SlabL2.IsSmoothArchFactor β →
      ∫ x, f (ent x) * omega3 β (ent x) ∂muInf = c * ∫ x, f (ent x) * β (ent x) ∂muInf) :
    ∀ m ∈ invLocus, -omega3T f m = c * f m := by
  have hg : ContinuousOn (fun m => -omega3T f m - c * f m) invLocus :=
    ((continuousOn_omega3T hf).neg).sub (continuousOn_const.mul hf.continuousOn)
  have := eq_zero_of_forall_integral_mul_eq_zero _ hg fun β hβ => by
    have h1 := h β hβ
    rw [integral_mul_omega3 f hf hβ] at h1
    simp only [sub_mul, neg_mul]
    have hI1 : Integrable (fun x => -(omega3T f (ent x) * β (ent x))) muInf :=
      (integrable_ent_mul (continuousOn_omega3T hf) hβ).neg
    rw [integral_sub hI1 ?_, integral_neg, h1]
    · simp only [mul_assoc]
      rw [integral_const_mul, sub_self]
    · simp only [mul_assoc]; exact (integrable_ent_mul hf.continuousOn hβ).const_mul c
  intro m hm
  exact sub_eq_zero.mp (this m hm)

theorem ent_eq_kernelEnt : ent = SlabL2.kernelEnt := rfl

theorem leftDeriv_eq_kernelLeftDeriv : leftDeriv = SlabL2.kernelLeftDeriv := rfl

theorem omega1_eq : omega1 = SlabL2.kernelCasimir1 := rfl
theorem omega2_eq : omega2 = SlabL2.kernelCasimir2 := rfl
theorem omega3_eq : omega3 = SlabL2.kernelCasimir3 := rfl
theorem omega3T_eq : omega3T = SlabL2.kernelCasimir3T := rfl

theorem isSmoothArchFactor_of_support_subset {β δ : E33 → ℂ} (hβ : SlabL2.IsSmoothArchFactor β)
    (hδ : ContDiff ℝ (⊤ : ℕ∞) δ) (hsupp : Function.support δ ⊆ tsupport β) : SlabL2.IsSmoothArchFactor δ :=
  ⟨hδ, HasCompactSupport.of_support_subset_isCompact hβ.2.1 hsupp,
    (closure_minimal hsupp (isClosed_tsupport β)).trans hβ.2.2⟩

theorem leftDeriv_eq_zero_of_notMem {i j : Fin 3} {γ β : E33 → ℂ} (hγ : Function.support γ ⊆ tsupport β) {m : E33}
    (hm : m ∉ tsupport β) : leftDeriv i j γ m = 0 := by
  have h1 : tsupport γ ⊆ tsupport β := closure_minimal hγ (isClosed_tsupport β)
  by_contra h
  exact hm (h1 (support_leftDeriv_subset i j γ (Function.mem_support.mpr h)))

theorem support_leftDeriv_subset' {i j : Fin 3} {γ β : E33 → ℂ} (hγ : Function.support γ ⊆ tsupport β) :
    Function.support (leftDeriv i j γ) ⊆ tsupport β := fun m hm => by
  by_contra h
  exact hm (leftDeriv_eq_zero_of_notMem hγ h)

theorem isSmoothArchFactor_omega1 {β : E33 → ℂ} (hβ : SlabL2.IsSmoothArchFactor β) :
    SlabL2.IsSmoothArchFactor (omega1 β) := by
  refine isSmoothArchFactor_of_support_subset hβ (ContDiff.sum fun i _ => (isSmoothArchFactor_leftDeriv i i hβ).1) ?_
  intro m hm
  by_contra h
  apply hm
  show ∑ i : Fin 3, leftDeriv i i β m = 0
  exact Finset.sum_eq_zero fun i _ => leftDeriv_eq_zero_of_notMem subset_closure h

theorem isSmoothArchFactor_omega2 {β : E33 → ℂ} (hβ : SlabL2.IsSmoothArchFactor β) :
    SlabL2.IsSmoothArchFactor (omega2 β) := by
  have hL := fun a b {γ : E33 → ℂ} (hγ : SlabL2.IsSmoothArchFactor γ) => isSmoothArchFactor_leftDeriv a b hγ
  refine isSmoothArchFactor_of_support_subset hβ
    (ContDiff.sum fun i _ => ContDiff.sum fun j _ => (hL i j (hL j i hβ)).1) ?_
  intro m hm
  by_contra h
  apply hm
  show ∑ i : Fin 3, ∑ j : Fin 3, leftDeriv i j (leftDeriv j i β) m = 0
  exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
    leftDeriv_eq_zero_of_notMem (support_leftDeriv_subset' subset_closure) h

theorem isSmoothArchFactor_omega3 {β : E33 → ℂ} (hβ : SlabL2.IsSmoothArchFactor β) :
    SlabL2.IsSmoothArchFactor (omega3 β) := by
  have hL := fun a b {γ : E33 → ℂ} (hγ : SlabL2.IsSmoothArchFactor γ) => isSmoothArchFactor_leftDeriv a b hγ
  refine isSmoothArchFactor_of_support_subset hβ
    (ContDiff.sum fun i _ => ContDiff.sum fun j _ => ContDiff.sum fun k _ => (hL i j (hL j k (hL k i hβ))).1) ?_
  intro m hm
  by_contra h
  apply hm
  show ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, leftDeriv i j (leftDeriv j k (leftDeriv k i β)) m = 0
  exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ =>
    leftDeriv_eq_zero_of_notMem (support_leftDeriv_subset' (support_leftDeriv_subset' subset_closure)) h

end LanglandsTunnell.CubicInduction.ArchConvCalculus

p2m_open "IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_archConvN_and_eq_of_forall_integral_kernelCasimir.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2 P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_archConvN_and_eq_of_forall_integral_kernelCasimir.LanglandsTunnell.CubicInduction.ArchConvCalculus"

theorem solution :
    (∀ (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), Continuous Φ → ∀ (β : (Fin 3 → Fin 3 → ℝ) → ℂ), IsSmoothArchFactor β →
      (IsSmoothArchFactor (kernelCasimir1 β) ∧ IsSmoothArchFactor (kernelCasimir2 β) ∧
          IsSmoothArchFactor (kernelCasimir3 β)) ∧
        WhittakerBlock.casimir1 (archConvN (Fin 3) ℚ Φ fun h => β (kernelEnt h)) =
            archConvN (Fin 3) ℚ Φ (fun h => kernelCasimir1 β (kernelEnt h)) ∧
          WhittakerBlock.casimir2 (archConvN (Fin 3) ℚ Φ fun h => β (kernelEnt h)) =
              archConvN (Fin 3) ℚ Φ (fun h => kernelCasimir2 β (kernelEnt h)) ∧
            WhittakerBlock.casimir3 (archConvN (Fin 3) ℚ Φ fun h => β (kernelEnt h)) =
              archConvN (Fin 3) ℚ Φ (fun h => kernelCasimir3 β (kernelEnt h))) ∧
      ∀ (f : (Fin 3 → Fin 3 → ℝ) → ℂ) (c : ℂ),
        (ContDiffOn ℝ 1 f {m | (Matrix.of m).det ≠ 0} →
          (∀ β : (Fin 3 → Fin 3 → ℝ) → ℂ, IsSmoothArchFactor β →
            (letI := archGLBorelN (Fin 3) ℚ
             ∫ h, f (kernelEnt h) * kernelCasimir1 β (kernelEnt h) ∂archGLHaarN (Fin 3) ℚ) =
              c * (letI := archGLBorelN (Fin 3) ℚ
                   ∫ h, f (kernelEnt h) * β (kernelEnt h) ∂archGLHaarN (Fin 3) ℚ)) →
            ∀ m : Fin 3 → Fin 3 → ℝ, (Matrix.of m).det ≠ 0 → -kernelCasimir1 f m = c * f m) ∧
        (ContDiffOn ℝ 2 f {m | (Matrix.of m).det ≠ 0} →
          (∀ β : (Fin 3 → Fin 3 → ℝ) → ℂ, IsSmoothArchFactor β →
            (letI := archGLBorelN (Fin 3) ℚ
             ∫ h, f (kernelEnt h) * kernelCasimir2 β (kernelEnt h) ∂archGLHaarN (Fin 3) ℚ) =
              c * (letI := archGLBorelN (Fin 3) ℚ
                   ∫ h, f (kernelEnt h) * β (kernelEnt h) ∂archGLHaarN (Fin 3) ℚ)) →
            ∀ m : Fin 3 → Fin 3 → ℝ, (Matrix.of m).det ≠ 0 → kernelCasimir2 f m = c * f m) ∧
        (ContDiffOn ℝ 3 f {m | (Matrix.of m).det ≠ 0} →
          (∀ β : (Fin 3 → Fin 3 → ℝ) → ℂ, IsSmoothArchFactor β →
            (letI := archGLBorelN (Fin 3) ℚ
             ∫ h, f (kernelEnt h) * kernelCasimir3 β (kernelEnt h) ∂archGLHaarN (Fin 3) ℚ) =
              c * (letI := archGLBorelN (Fin 3) ℚ
                   ∫ h, f (kernelEnt h) * β (kernelEnt h) ∂archGLHaarN (Fin 3) ℚ)) →
            ∀ m : Fin 3 → Fin 3 → ℝ, (Matrix.of m).det ≠ 0 → -kernelCasimir3T f m = c * f m) := by
  refine ⟨fun Φ hΦ β hβ => ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, fun f c => ⟨fun hf h => ?_, fun hf h => ?_, fun hf h => ?_⟩⟩
  · exact isSmoothArchFactor_omega1 hβ
  · exact isSmoothArchFactor_omega2 hβ
  · exact isSmoothArchFactor_omega3 hβ
  · exact casimir1_archConvN Φ hΦ hβ
  · exact casimir2_archConvN Φ hΦ hβ
  · exact casimir3_archConvN Φ hΦ hβ
  · exact neg_omega1_eq_of_forall_integral f hf c h
  · exact omega2_eq_of_forall_integral f hf c h
  · exact neg_omega3T_eq_of_forall_integral f hf c h

end

end S_LanglandsTunnell_CubicInduction_SlabL2_casimir_archConvN_and_eq_of_forall_integral_kernelCasimir
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_archConvN_and_eq_of_forall_integral_kernelCasimir (solution)
