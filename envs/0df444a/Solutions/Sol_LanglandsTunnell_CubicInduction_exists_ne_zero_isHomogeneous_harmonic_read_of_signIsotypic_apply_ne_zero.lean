-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_ne_zero_isHomogeneous_harmonic_read_of_signIsotypic_apply_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/97f8721f-db32-5388-8f02-0a01e7db284a

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_hasDerivAt_comp_archRealLift3_rotation_of_isArchSmooth3
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_of_signIsotypic_apply_ne_zero

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

namespace WsE
namespace FNT

noncomputable section

private def _root_.WsE.FNT.ofRealHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v : InfinitePlace ℚ =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.toRingHom

p2m_export "WsE.FNT" "ofRealHom"
theorem ofRealHom_apply (r : ℝ) : ofRealHom r = StandardKernel.ofReal r := rfl

def realM (e : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) := e.map ofRealHom

theorem archRealMat3_eq (e : Fin 3 → Fin 3 → ℝ) :
    WhittakerBlock.archRealMat3 e = archMatrixInclN (Fin 3) ℚ (realM e) := rfl

theorem realM_mul (e f : Matrix (Fin 3) (Fin 3) ℝ) : realM (e * f) = realM e * realM f :=
  Matrix.map_mul

theorem isUnit_of_det_ne_zero (e : Matrix (Fin 3) (Fin 3) ℝ) (h : e.det ≠ 0) : IsUnit e :=
  (Matrix.isUnit_iff_isUnit_det e).mpr (isUnit_iff_ne_zero.mpr h)

theorem isUnit_archRealMat3 (e : Fin 3 → Fin 3 → ℝ) (h : (Matrix.of e).det ≠ 0) :
    IsUnit (WhittakerBlock.archRealMat3 e) := by
  rw [archRealMat3_eq]
  have h1 : IsUnit (realM e) := (isUnit_of_det_ne_zero (Matrix.of e) h).map (RingHom.mapMatrix ofRealHom)
  exact h1.map (archMatrixInclHomN (Fin 3) ℚ)

theorem val_lift (e : Fin 3 → Fin 3 → ℝ) (h : (Matrix.of e).det ≠ 0) :
    ((WhittakerBlock.archRealLift3 e : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      WhittakerBlock.archRealMat3 e := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_pos (isUnit_archRealMat3 e h)]
  exact IsUnit.unit_spec _

def unitInf (e : Matrix (Fin 3) (Fin 3) ℝ) (h : e.det ≠ 0) : GL (Fin 3) (InfiniteAdeleRing ℚ) :=
  Matrix.GeneralLinearGroup.map ofRealHom (e.nonsingInvUnit (isUnit_iff_ne_zero.mpr h))

theorem val_unitInf (e : Matrix (Fin 3) (Fin 3) ℝ) (h : e.det ≠ 0) :
    ((unitInf e h : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) = realM e :=
  rfl

theorem lift_eq_archInclN (e : Fin 3 → Fin 3 → ℝ) (h : (Matrix.of e).det ≠ 0) :
    WhittakerBlock.archRealLift3 e = archInclN (Fin 3) ℚ (unitInf (Matrix.of e) h) := by
  refine Units.ext ?_
  rw [val_lift e h]
  rfl

theorem lift_mul (e f : Matrix (Fin 3) (Fin 3) ℝ) (he : e.det ≠ 0) (hf : f.det ≠ 0) :
    WhittakerBlock.archRealLift3 (e * f) = WhittakerBlock.archRealLift3 e * WhittakerBlock.archRealLift3 f := by
  have hef : (Matrix.of (e * f)).det ≠ 0 := by
    change (e * f).det ≠ 0
    rw [Matrix.det_mul]; exact mul_ne_zero he hf
  refine Units.ext ?_
  rw [Units.val_mul, val_lift _ hef, val_lift _ he, val_lift _ hf, archRealMat3_eq, archRealMat3_eq,
    archRealMat3_eq, ← archMatrixInclN_mul, ← realM_mul]

theorem componentAt3_lift (f : Matrix (Fin 3) (Fin 3) ℝ) (h : f.det ≠ 0) (q : HeightOneSpectrum (𝓞 ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ q (WhittakerBlock.archRealLift3 f) = 1 := by
  rw [lift_eq_archInclN f h]
  exact componentAtN_archInclN (Fin 3) ℚ q _

theorem archComponent3_lift_mem_orth3 (f : Matrix (Fin 3) (Fin 3) ℝ) (h : f.det ≠ 0) (horth : f.transpose * f = 1) :
    archComponent3 (𝓞 ℚ) ℚ (WhittakerBlock.archRealLift3 f) ∈ orth3 := by
  rw [lift_eq_archInclN f h]
  change archComponentN (Fin 3) (𝓞 ℚ) ℚ (archInclN (Fin 3) ℚ (unitInf (Matrix.of f) h)) ∈ orth3
  rw [archComponentN_archInclN]
  change (realM f).transpose * realM f = 1
  rw [realM, ← Matrix.transpose_map, ← Matrix.map_mul, horth,
    Matrix.map_one ofRealHom (map_zero _) (map_one _)]

theorem lift_mul_comm_of_archComponent3_eq_one (f : Matrix (Fin 3) (Fin 3) ℝ) (h : f.det ≠ 0)
    (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ) (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1) :
    WhittakerBlock.archRealLift3 f * k₁ = k₁ * WhittakerBlock.archRealLift3 f := by
  have hK : ∀ l j : Fin 3, AdelicLevel.adeleArch (𝓞 ℚ) ℚ ((k₁ : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) l j) =
      (1 : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) l j := fun l j =>
    congrArg (fun u : GL (Fin 3) (InfiniteAdeleRing ℚ) => (u : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) l j) hk₁
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, val_lift f h, archRealMat3_eq]
  ext i j
  refine Prod.ext ?_ ?_
  · change AdelicLevel.adeleArch (𝓞 ℚ) ℚ ((archMatrixInclN (Fin 3) ℚ (realM f) * (k₁ : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) i j) =
      AdelicLevel.adeleArch (𝓞 ℚ) ℚ (((k₁ : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) * archMatrixInclN (Fin 3) ℚ (realM f)) i j)
    simp only [Matrix.mul_apply, map_sum, map_mul, adeleArch_archMatrixInclN, hK]
    rw [← Matrix.mul_apply, ← Matrix.mul_apply, Matrix.mul_one, Matrix.one_mul]
  · change AdelicLevel.adeleFin (𝓞 ℚ) ℚ ((archMatrixInclN (Fin 3) ℚ (realM f) * (k₁ : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) i j) =
      AdelicLevel.adeleFin (𝓞 ℚ) ℚ (((k₁ : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) * archMatrixInclN (Fin 3) ℚ (realM f)) i j)
    simp only [Matrix.mul_apply, map_sum, map_mul, adeleFin_archMatrixInclN]
    simp [Matrix.one_apply]

end

end WsE.FNT

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

namespace WsE
namespace FNT

noncomputable section

open MvPolynomial

theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> decide

def ColOrth (o : Fin 3 → Fin 3 → ℝ) : Prop :=
  ∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0

theorem colOrth_iff (o : Matrix (Fin 3) (Fin 3) ℝ) : ColOrth o ↔ o.transpose * o = 1 := by
  constructor
  · intro h
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [Matrix.transpose_apply] using h i j
  · intro h i j
    have := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) h
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using this

theorem det_ne_zero_of_colOrth (o : Matrix (Fin 3) (Fin 3) ℝ) (h : ColOrth o) : o.det ≠ 0 := by
  have h1 := congrArg Matrix.det ((colOrth_iff o).mp h)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
  intro h0
  rw [h0, mul_zero] at h1
  exact zero_ne_one h1

theorem colOrth_mul (o H : Matrix (Fin 3) (Fin 3) ℝ) (ho : ColOrth o) (hH : ColOrth H) : ColOrth (o * H) := by
  rw [colOrth_iff] at ho hH ⊢
  calc (o * H).transpose * (o * H) = H.transpose * (o.transpose * o) * H := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [ho, Matrix.mul_one, hH]

def ej (j : Fin 3) : Fin 3 → ℝ := fun t => if t = j then 1 else 0

def refl (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun r s => (if r = s then 1 else 0) - 2 * v r * v s / (∑ t : Fin 3, v t ^ 2)

theorem refl_colOrth (v : Fin 3 → ℝ) (hv : (∑ t : Fin 3, v t ^ 2) ≠ 0) : ColOrth (refl v) := by
  have hv' : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 ≠ 0 := by simpa [Fin.sum_univ_three] using hv
  intro i j
  rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl <;>
    (simp [refl, Fin.sum_univ_three]; field_simp; ring)

def HH (j : Fin 3) (w : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  if w = ej j then 1 else refl (fun t => ej j t - w t)

theorem colOrth_one : ColOrth (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [colOrth_iff, Matrix.transpose_one, Matrix.one_mul]

theorem sum_sq_sub (j : Fin 3) (w : Fin 3 → ℝ) (hw : (∑ t : Fin 3, w t ^ 2) = 1) :
    (∑ t : Fin 3, (ej j t - w t) ^ 2) = 2 * (1 - w j) := by
  simp only [Fin.sum_univ_three] at hw
  rcases fin3_cases j with rfl | rfl | rfl <;>
    (simp [Fin.sum_univ_three, ej]; linear_combination hw)

theorem ne_ej_aux (j : Fin 3) (w : Fin 3 → ℝ) (hw : (∑ t : Fin 3, w t ^ 2) = 1) (hne : w ≠ ej j) :
    w j ≠ 1 := by
  intro h1
  apply hne
  have hs := sum_sq_sub j w hw
  rw [h1, sub_self, mul_zero] at hs
  have h0 : ∀ t, (ej j t - w t) ^ 2 = 0 := fun t =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => sq_nonneg (ej j t - w t))).mp hs t (Finset.mem_univ t)
  funext t
  have := h0 t
  rw [sq_eq_zero_iff, sub_eq_zero] at this
  exact this.symm

theorem HH_colOrth (j : Fin 3) (w : Fin 3 → ℝ) (hw : (∑ t : Fin 3, w t ^ 2) = 1) : ColOrth (HH j w) := by
  unfold HH
  split_ifs with h
  · exact colOrth_one
  · apply refl_colOrth
    rw [sum_sq_sub j w hw]
    exact mul_ne_zero two_ne_zero (sub_ne_zero.mpr (ne_ej_aux j w hw h).symm)

theorem HH_col (j : Fin 3) (w : Fin 3 → ℝ) (hw : (∑ t : Fin 3, w t ^ 2) = 1) (r : Fin 3) :
    HH j w r j = w r := by
  unfold HH
  split_ifs with h
  · rw [h]; simp [ej, Matrix.one_apply]
  · have hj : (1 : ℝ) - w j ≠ 0 := sub_ne_zero.mpr (ne_ej_aux j w hw h).symm
    show (if r = j then 1 else 0) - 2 * (ej j r - w r) * (ej j j - w j) / (∑ t : Fin 3, (ej j t - w t) ^ 2) = w r
    rw [sum_sq_sub j w hw]
    have hjj : ej j j = 1 := by simp [ej]
    rw [hjj]
    by_cases hr : r = j
    · subst hr
      rw [if_pos rfl, hjj]
      field_simp
      ring
    · rw [if_neg hr]
      have : ej j r = 0 := by simp [ej, hr]
      rw [this]
      field_simp
      ring

theorem HH_det_ne_zero (j : Fin 3) (w : Fin 3 → ℝ) (hw : (∑ t : Fin 3, w t ^ 2) = 1) : (HH j w).det ≠ 0 :=
  det_ne_zero_of_colOrth _ (HH_colOrth j w hw)

end

end WsE.FNT

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction
open scoped Topology

namespace WsE
namespace FNT

noncomputable section

abbrev Fn := AdelicGL 3 (𝓞 ℚ) ℚ → ℂ

def IsArchOrth (k : AdelicGL 3 (𝓞 ℚ) ℚ) : Prop :=
  (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) ∧ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3

theorem one_mem_orth3 : (1 : GL (Fin 3) (InfiniteAdeleRing ℚ)) ∈ orth3 := by
  show ((1 : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).transpose *
    ((1 : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) = 1
  simp

theorem mul_mem_orth3 {a b : GL (Fin 3) (InfiniteAdeleRing ℚ)} (ha : a ∈ orth3) (hb : b ∈ orth3) :
    a * b ∈ orth3 := by
  change (a : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).transpose * a = 1 at ha
  change (b : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).transpose * b = 1 at hb
  show ((a * b : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).transpose *
    ((a * b : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) = 1
  rw [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ (a : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)), ha, Matrix.one_mul, hb]

theorem isArchOrth_one : IsArchOrth 1 :=
  ⟨fun p => map_one _, by rw [map_one]; exact one_mem_orth3⟩

theorem IsArchOrth.mul {a b : AdelicGL 3 (𝓞 ℚ) ℚ} (ha : IsArchOrth a) (hb : IsArchOrth b) : IsArchOrth (a * b) :=
  ⟨fun p => by rw [map_mul, ha.1 p, hb.1 p, one_mul], by rw [map_mul]; exact mul_mem_orth3 ha.2 hb.2⟩

theorem isArchOrth_lift (o : Matrix (Fin 3) (Fin 3) ℝ) (ho : ColOrth o) :
    IsArchOrth (WhittakerBlock.archRealLift3 o) :=
  ⟨componentAt3_lift o (det_ne_zero_of_colOrth o ho),
    archComponent3_lift_mem_orth3 o (det_ne_zero_of_colOrth o ho) ((colOrth_iff o).1 ho)⟩

def transl (k : AdelicGL 3 (𝓞 ℚ) ℚ) : Fn →ₗ[ℂ] Fn :=
  LinearMap.funLeft ℂ ℂ (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => g * k)

theorem transl_apply (k : AdelicGL 3 (𝓞 ℚ) ℚ) (φ : Fn) : transl k φ = fun g => φ (g * k) := rfl

section W

variable (G₀ : Fn)

def W : Submodule ℂ Fn :=
  Submodule.span ℂ {φ : Fn | ∃ k : AdelicGL 3 (𝓞 ℚ) ℚ, IsArchOrth k ∧ φ = fun g => G₀ (g * k)}

theorem transl_mem_W_gen {k : AdelicGL 3 (𝓞 ℚ) ℚ} (hk : IsArchOrth k) : (fun g => G₀ (g * k)) ∈ W G₀ :=
  Submodule.subset_span ⟨k, hk, rfl⟩

theorem self_mem_W : G₀ ∈ W G₀ := by
  have := transl_mem_W_gen G₀ isArchOrth_one
  simpa using this

theorem transl_mem_W {φ : Fn} (hφ : φ ∈ W G₀) {k : AdelicGL 3 (𝓞 ℚ) ℚ} (hk : IsArchOrth k) :
    (fun g => φ (g * k)) ∈ W G₀ := by
  have hmap : (W G₀).map (transl k) ≤ W G₀ := by
    rw [W, Submodule.map_span_le]
    rintro _ ⟨k', hk', rfl⟩
    rw [transl_apply]
    have : (fun g => (fun g => G₀ (g * k')) (g * k)) = fun g => G₀ (g * (k * k')) := by
      funext g; simp [mul_assoc]
    rw [this]
    exact transl_mem_W_gen G₀ (hk.mul hk')
  exact hmap ⟨φ, hφ, rfl⟩

variable {G₀}
variable {Vε : Submodule ℂ Fn}

theorem W_le (hG₀ : G₀ ∈ Vε)
    (h4 : ∀ G ∈ Vε, ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) →
        archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 → (fun g => G (g * k')) ∈ Vε) :
    W G₀ ≤ Vε := by
  rw [W, Submodule.span_le]
  rintro _ ⟨k, hk, rfl⟩
  exact h4 G₀ hG₀ k hk.1 hk.2

theorem W_fd
    (h5 : ∃ s : Finset Fn, ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) → archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 →
          (fun g => G₀ (g * k')) ∈ Submodule.span ℂ (s : Set Fn)) :
    FiniteDimensional ℂ (W G₀) := by
  obtain ⟨s, hs⟩ := h5
  have hle : W G₀ ≤ Submodule.span ℂ (s : Set Fn) := by
    rw [W, Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    exact hs k hk.1 hk.2
  exact Submodule.finiteDimensional_of_le hle

end W

def rotArr (c₁ c₂ : Fin 3) (s : ℝ) : Fin 3 → Fin 3 → ℝ := fun i j =>
  if i = c₁ ∧ j = c₁ then Real.cos s else if i = c₂ ∧ j = c₂ then Real.cos s else
  if i = c₁ ∧ j = c₂ then - Real.sin s else if i = c₂ ∧ j = c₁ then Real.sin s else
  if i = j then 1 else 0

theorem colOrth_rotArr01 (s : ℝ) : ColOrth (rotArr 0 1 s) := by
  have hsc := Real.sin_sq_add_cos_sq s
  intro i j
  rcases fin3_cases i with h3 | h3 | h3 <;> rcases fin3_cases j with h4 | h4 | h4 <;> subst h3 h4 <;>
    simp [rotArr, Fin.sum_univ_three] <;> first | linear_combination hsc | linear_combination

theorem colOrth_rotArr02 (s : ℝ) : ColOrth (rotArr 0 2 s) := by
  have hsc := Real.sin_sq_add_cos_sq s
  intro i j
  rcases fin3_cases i with h3 | h3 | h3 <;> rcases fin3_cases j with h4 | h4 | h4 <;> subst h3 h4 <;>
    simp [rotArr, Fin.sum_univ_three] <;> first | linear_combination hsc | linear_combination

theorem colOrth_rotArr12 (s : ℝ) : ColOrth (rotArr 1 2 s) := by
  have hsc := Real.sin_sq_add_cos_sq s
  intro i j
  rcases fin3_cases i with h3 | h3 | h3 <;> rcases fin3_cases j with h4 | h4 | h4 <;> subst h3 h4 <;>
    simp [rotArr, Fin.sum_univ_three] <;> first | linear_combination hsc | linear_combination

def rotD (c₁ c₂ : Fin 3) (G : Fn) : Fn := fun g =>
  WhittakerBlock.archDeriv c₂ c₁ G g - WhittakerBlock.archDeriv c₁ c₂ G g

theorem rotD_mem_W {G₀ : Fn} [FiniteDimensional ℂ (W G₀)] {G : Fn} (hG : G ∈ W G₀)
    (hsm : WhittakerBlock.IsArchSmooth3 G) {c₁ c₂ : Fin 3} (hc : ∀ s, ColOrth (rotArr c₁ c₂ s)) :
    rotD c₁ c₂ G ∈ W G₀ := by
  have hclosed : IsClosed ((W G₀ : Submodule ℂ Fn) : Set Fn) := (W G₀).closed_of_finiteDimensional

  let F : ℝ → Fn := fun t g =>
    (t - 0)⁻¹ • (G (g * WhittakerBlock.archRealLift3 (rotArr c₁ c₂ t)) -
      G (g * WhittakerBlock.archRealLift3 (rotArr c₁ c₂ 0)))
  have hmem : ∀ t, F t ∈ W G₀ := by
    intro t
    have h1 := transl_mem_W G₀ hG (isArchOrth_lift (Matrix.of (rotArr c₁ c₂ t)) (hc t))
    have h2 := transl_mem_W G₀ hG (isArchOrth_lift (Matrix.of (rotArr c₁ c₂ 0)) (hc 0))
    have h3 := (W G₀).smul_mem (((t - 0)⁻¹ : ℝ) : ℂ) ((W G₀).sub_mem h1 h2)
    have : F t = (((t - 0)⁻¹ : ℝ) : ℂ) • ((fun g => G (g * WhittakerBlock.archRealLift3 (Matrix.of (rotArr c₁ c₂ t)))) -
        fun g => G (g * WhittakerBlock.archRealLift3 (Matrix.of (rotArr c₁ c₂ 0)))) := by
      funext g
      simp only [F, Pi.smul_apply, Pi.sub_apply, Complex.real_smul, smul_eq_mul]
      rfl
    rw [this]
    exact h3
  have hlim : Filter.Tendsto F (𝓝[≠] 0) (𝓝 (rotD c₁ c₂ G)) := by
    rw [tendsto_pi_nhds]
    intro g
    have hd := WhittakerBlock.hasDerivAt_comp_archRealLift3_rotation_of_isArchSmooth3 G hsm c₁ c₂ g
    rw [hasDerivAt_iff_tendsto_slope] at hd
    exact hd
  exact hclosed.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)

end

end WsE.FNT

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction
open scoped Topology

namespace WsE
namespace FNT

noncomputable section

open scoped Classical

abbrev MFn := Matrix (Fin 3) (Fin 3) ℝ → ℂ

theorem mem_O3_iff (m : Matrix (Fin 3) (Fin 3) ℝ) : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ ↔ ColOrth m := by
  rw [Matrix.mem_orthogonalGroup_iff', colOrth_iff]

theorem det_ne_zero_of_mem_O3 {m : Matrix (Fin 3) (Fin 3) ℝ} (hm : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    m.det ≠ 0 :=
  det_ne_zero_of_colOrth m ((mem_O3_iff m).1 hm)

theorem mul_mem_O3_iff {r r₀ : Matrix (Fin 3) (Fin 3) ℝ} (hr₀ : r₀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    r * r₀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ ↔ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  constructor
  · intro h
    have : r = r * r₀ * star r₀ := by
      rw [Matrix.mul_assoc, Unitary.mul_star_self_of_mem hr₀, Matrix.mul_one]
    rw [this]
    exact Submonoid.mul_mem _ h (Unitary.star_mem hr₀)
  · intro h
    exact Submonoid.mul_mem _ h hr₀

section Read

variable (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ)

def readL : Fn →ₗ[ℂ] MFn where
  toFun G := fun m => if m ∈ Matrix.orthogonalGroup (Fin 3) ℝ then G (WhittakerBlock.archRealLift3 m * k₁) else 0
  map_add' G G' := by
    funext m
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c G := by
    funext m
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem readL_apply_of_mem (G : Fn) {m : Matrix (Fin 3) (Fin 3) ℝ} (hm : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    readL k₁ G m = G (WhittakerBlock.archRealLift3 m * k₁) :=
  if_pos hm

theorem readL_apply_of_not_mem (G : Fn) {m : Matrix (Fin 3) (Fin 3) ℝ}
    (hm : m ∉ Matrix.orthogonalGroup (Fin 3) ℝ) : readL k₁ G m = 0 :=
  if_neg hm

variable {k₁}
variable (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1)
include hk₁

theorem readL_mul (G : Fn) {r r₀ : Matrix (Fin 3) (Fin 3) ℝ} (hr : r ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (hr₀ : r₀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    readL k₁ G (r * r₀) =
      G (WhittakerBlock.archRealLift3 r * k₁ * WhittakerBlock.archRealLift3 r₀) := by
  rw [readL_apply_of_mem k₁ G ((mul_mem_O3_iff hr₀).2 hr), lift_mul r r₀ (det_ne_zero_of_mem_O3 hr)
    (det_ne_zero_of_mem_O3 hr₀), mul_assoc, lift_mul_comm_of_archComponent3_eq_one r₀ (det_ne_zero_of_mem_O3 hr₀)
    k₁ hk₁, ← mul_assoc]

theorem readL_transl (G : Fn) {r₀ : Matrix (Fin 3) (Fin 3) ℝ} (hr₀ : r₀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    (fun r => readL k₁ G (r * r₀)) = readL k₁ (fun g => G (g * WhittakerBlock.archRealLift3 r₀)) := by
  funext r
  by_cases hr : r ∈ Matrix.orthogonalGroup (Fin 3) ℝ
  · rw [readL_mul hk₁ G hr hr₀, readL_apply_of_mem k₁ _ hr]
  · rw [readL_apply_of_not_mem k₁ _ ((mul_mem_O3_iff hr₀).not.2 hr), readL_apply_of_not_mem k₁ _ hr]

end Read

def pl : Fin 3 → Fin 3 × Fin 3 := ![(0, 1), (0, 2), (1, 2)]

theorem colOrth_rotArr_pl (c : Fin 3) (s : ℝ) : ColOrth (rotArr (pl c).1 (pl c).2 s) := by
  rcases fin3_cases c with h | h | h <;> subst h
  · exact colOrth_rotArr01 s
  · exact colOrth_rotArr02 s
  · exact colOrth_rotArr12 s

def rotM (c : Fin 3) (s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of (rotArr (pl c).1 (pl c).2 s)

theorem rotM_mem (c : Fin 3) (s : ℝ) : rotM c s ∈ Matrix.orthogonalGroup (Fin 3) ℝ :=
  (mem_O3_iff _).2 (colOrth_rotArr_pl c s)

def rotDc (c : Fin 3) (G : Fn) : Fn := rotD (pl c).1 (pl c).2 G

section Ops

variable {k₁ : AdelicGL 3 (𝓞 ℚ) ℚ} (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1)

def Lfun (c : Fin 3) (F : MFn) : MFn := fun m =>
  if m ∈ Matrix.orthogonalGroup (Fin 3) ℝ then deriv (fun s : ℝ => F (m * rotM c s)) 0 else 0

include hk₁

theorem readL_rot (G : Fn) {m : Matrix (Fin 3) (Fin 3) ℝ} (hm : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (c : Fin 3) :
    (fun s : ℝ => readL k₁ G (m * rotM c s)) = fun s : ℝ =>
      G (WhittakerBlock.archRealLift3 m * k₁ * WhittakerBlock.archRealLift3 (rotArr (pl c).1 (pl c).2 s)) := by
  funext s
  rw [readL_mul hk₁ G hm (rotM_mem c s)]
  rfl

theorem hasDerivAt_readL_rot {G : Fn} (hsm : WhittakerBlock.IsArchSmooth3 G) {m : Matrix (Fin 3) (Fin 3) ℝ}
    (hm : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (c : Fin 3) :
    HasDerivAt (fun s : ℝ => readL k₁ G (m * rotM c s))
      (rotDc c G (WhittakerBlock.archRealLift3 m * k₁)) 0 := by
  rw [readL_rot hk₁ G hm c]
  exact WhittakerBlock.hasDerivAt_comp_archRealLift3_rotation_of_isArchSmooth3 G hsm (pl c).1 (pl c).2 _

theorem Lfun_readL {G : Fn} (hsm : WhittakerBlock.IsArchSmooth3 G) (c : Fin 3) :
    Lfun c (readL k₁ G) = readL k₁ (rotDc c G) := by
  funext m
  by_cases hm : m ∈ Matrix.orthogonalGroup (Fin 3) ℝ
  · rw [Lfun, if_pos hm, readL_apply_of_mem k₁ _ hm]
    exact (hasDerivAt_readL_rot hk₁ hsm hm c).deriv
  · rw [Lfun, if_neg hm, readL_apply_of_not_mem k₁ _ hm]

end Ops

end

end WsE.FNT

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction
open scoped Topology

namespace WsE
namespace FNT

noncomputable section

open scoped Classical

theorem isArchSmooth3_smul (c : ℂ) {ψ : Fn} (hψ : WhittakerBlock.IsArchSmooth3 ψ) :
    WhittakerBlock.IsArchSmooth3 (c • ψ) := fun g => (hψ g).const_smul c

theorem archDeriv_sub {φ ψ : Fn} (hφ : WhittakerBlock.IsArchSmooth3 φ) (hψ : WhittakerBlock.IsArchSmooth3 ψ)
    (i j : Fin 3) :
    WhittakerBlock.archDeriv i j (φ - ψ) = WhittakerBlock.archDeriv i j φ - WhittakerBlock.archDeriv i j ψ := by
  have hA := WhittakerBlock.isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate
  have h1 : φ - ψ = φ + (-1 : ℂ) • ψ := by rw [neg_one_smul, sub_eq_add_neg]
  rw [h1, hA.2.1 φ ((-1 : ℂ) • ψ) hφ (isArchSmooth3_smul (-1) hψ) i j, hA.2.2.1 (-1 : ℂ) ψ i j, neg_one_smul,
    sub_eq_add_neg]

theorem rotD_eq (a b : Fin 3) (G : Fn) :
    rotD a b G = WhittakerBlock.archDeriv b a G - WhittakerBlock.archDeriv a b G := rfl

theorem isArchSmooth3_rotD {G : Fn} (hG : WhittakerBlock.IsArchSmooth3 G) (a b : Fin 3) :
    WhittakerBlock.IsArchSmooth3 (rotD a b G) := by
  have hA := WhittakerBlock.isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate
  intro g
  exact ((hA.1 G hG b a) g).sub ((hA.1 G hG a b) g)

theorem rotD_add {G G' : Fn} (hG : WhittakerBlock.IsArchSmooth3 G) (hG' : WhittakerBlock.IsArchSmooth3 G')
    (a b : Fin 3) : rotD a b (G + G') = rotD a b G + rotD a b G' := by
  have hA := WhittakerBlock.isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate
  rw [rotD_eq, rotD_eq, rotD_eq, hA.2.1 G G' hG hG' b a, hA.2.1 G G' hG hG' a b]
  funext g
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

theorem rotD_smul (c : ℂ) (G : Fn) (a b : Fin 3) : rotD a b (c • G) = c • rotD a b G := by
  have hA := WhittakerBlock.isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate
  rw [rotD_eq, rotD_eq, hA.2.2.1 c G b a, hA.2.2.1 c G a b, smul_sub]

theorem f01 : ((0 : Fin 3) = 1) = False := eq_false (by decide)
theorem f02 : ((0 : Fin 3) = 2) = False := eq_false (by decide)
theorem f10 : ((1 : Fin 3) = 0) = False := eq_false (by decide)
theorem f12 : ((1 : Fin 3) = 2) = False := eq_false (by decide)
theorem f20 : ((2 : Fin 3) = 0) = False := eq_false (by decide)
theorem f21 : ((2 : Fin 3) = 1) = False := eq_false (by decide)

theorem rotD_bracket {G : Fn} (hG : WhittakerBlock.IsArchSmooth3 G) (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (rotD 0 1 (rotD 0 2 G) x - rotD 0 2 (rotD 0 1 G) x = rotD 1 2 G x) ∧
    (rotD 0 1 (rotD 1 2 G) x - rotD 1 2 (rotD 0 1 G) x = - rotD 0 2 G x) ∧
    (rotD 0 2 (rotD 1 2 G) x - rotD 1 2 (rotD 0 2 G) x = rotD 0 1 G x) := by
  have hA := WhittakerBlock.isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate
  have hs := hA.1 G hG
  have hbr := hA.2.2.2.1 G hG

  simp only [rotD_eq, Pi.sub_apply, archDeriv_sub (hs _ _) (hs _ _)]

  have b := fun i j k l => congrFun (hbr i j k l) x
  simp only [Pi.sub_apply] at b
  refine ⟨?_, ?_, ?_⟩
  · have h1 := b 1 0 2 0; have h2 := b 1 0 0 2; have h3 := b 0 1 2 0; have h4 := b 0 1 0 2
    simp only [f01, f02, f10, f12, f20, f21, if_true, if_false, Pi.zero_apply] at h1 h2 h3 h4
    linear_combination h1 - h2 - h3 + h4
  · have h1 := b 1 0 2 1; have h2 := b 1 0 1 2; have h3 := b 0 1 2 1; have h4 := b 0 1 1 2
    simp only [f01, f02, f10, f12, f20, f21, if_true, if_false, Pi.zero_apply] at h1 h2 h3 h4
    linear_combination h1 - h2 - h3 + h4
  · have h1 := b 2 0 2 1; have h2 := b 2 0 1 2; have h3 := b 0 2 2 1; have h4 := b 0 2 1 2
    simp only [f01, f02, f10, f12, f20, f21, if_true, if_false, Pi.zero_apply] at h1 h2 h3 h4
    linear_combination h1 - h2 - h3 + h4

section Esp

variable (G₀ : Fn) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ)

def Esp : Submodule ℂ MFn := (W G₀).map (readL k₁)

variable {G₀ k₁}
variable {Vε : Submodule ℂ Fn} (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1)
  (h2 : ∀ G ∈ Vε, WhittakerBlock.IsArchSmooth3 G) (hWV : W G₀ ≤ Vε) [FiniteDimensional ℂ (W G₀)]

omit [FiniteDimensional ℂ ↥(W G₀)] in
include h2 hWV in
theorem smooth_of_mem_W {G : Fn} (hG : G ∈ W G₀) : WhittakerBlock.IsArchSmooth3 G := h2 G (hWV hG)

include h2 hWV in
theorem rotDc_mem_W {G : Fn} (hG : G ∈ W G₀) (c : Fin 3) : rotDc c G ∈ W G₀ :=
  rotD_mem_W hG (smooth_of_mem_W h2 hWV hG) (colOrth_rotArr_pl c)

include hk₁ h2 hWV in

def LE (c : Fin 3) : Esp G₀ k₁ →ₗ[ℂ] Esp G₀ k₁ where
  toFun F := ⟨Lfun c (F : MFn), by
    obtain ⟨G, hG, hGF⟩ := Submodule.mem_map.1 F.2
    rw [← hGF, Lfun_readL hk₁ (smooth_of_mem_W h2 hWV hG) c]
    exact Submodule.mem_map_of_mem (rotDc_mem_W h2 hWV hG c)⟩
  map_add' F F' := by
    obtain ⟨G, hG, hGF⟩ := Submodule.mem_map.1 F.2
    obtain ⟨G', hG', hGF'⟩ := Submodule.mem_map.1 F'.2
    apply Subtype.ext
    show Lfun c ((F : MFn) + F') = Lfun c F + Lfun c F'
    rw [← hGF, ← hGF', ← map_add, Lfun_readL hk₁ (smooth_of_mem_W h2 hWV ((W G₀).add_mem hG hG')) c,
      Lfun_readL hk₁ (smooth_of_mem_W h2 hWV hG) c, Lfun_readL hk₁ (smooth_of_mem_W h2 hWV hG') c, rotDc, rotDc,
      rotDc, rotD_add (smooth_of_mem_W h2 hWV hG) (smooth_of_mem_W h2 hWV hG'), map_add]
  map_smul' a F := by
    obtain ⟨G, hG, hGF⟩ := Submodule.mem_map.1 F.2
    apply Subtype.ext
    show Lfun c (a • (F : MFn)) = a • Lfun c F
    rw [← hGF, ← map_smul, Lfun_readL hk₁ (smooth_of_mem_W h2 hWV ((W G₀).smul_mem a hG)) c,
      Lfun_readL hk₁ (smooth_of_mem_W h2 hWV hG) c, rotDc, rotDc, rotD_smul, map_smul]

theorem LE_coe (c : Fin 3) (F : Esp G₀ k₁) : ((LE hk₁ h2 hWV c F : Esp G₀ k₁) : MFn) = Lfun c (F : MFn) := rfl

theorem LE_coe_of_eq (c : Fin 3) (F : Esp G₀ k₁) {G : Fn} (hG : G ∈ W G₀) (hGF : readL k₁ G = (F : MFn)) :
    ((LE hk₁ h2 hWV c F : Esp G₀ k₁) : MFn) = readL k₁ (rotDc c G) := by
  rw [LE_coe, ← hGF, Lfun_readL hk₁ (smooth_of_mem_W h2 hWV hG) c]

theorem LE_tie (F : Esp G₀ k₁) (c : Fin 3) {r : Matrix (Fin 3) (Fin 3) ℝ}
    (hr : r ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    HasDerivAt (fun s : ℝ => (F : MFn) (r * rotM c s)) (((LE hk₁ h2 hWV c F : Esp G₀ k₁) : MFn) r) 0 := by
  obtain ⟨G, hG, hGF⟩ := Submodule.mem_map.1 F.2
  rw [LE_coe, Lfun, if_pos hr, ← hGF]
  exact (hasDerivAt_readL_rot hk₁ (smooth_of_mem_W h2 hWV hG) hr c).differentiableAt.hasDerivAt

theorem LE_comm (F : Esp G₀ k₁) {r : Matrix (Fin 3) (Fin 3) ℝ} (hr : r ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    ((LE hk₁ h2 hWV 0 (LE hk₁ h2 hWV 1 F) : Esp G₀ k₁) : MFn) r -
        ((LE hk₁ h2 hWV 1 (LE hk₁ h2 hWV 0 F) : Esp G₀ k₁) : MFn) r =
      ((LE hk₁ h2 hWV 2 F : Esp G₀ k₁) : MFn) r ∧
    ((LE hk₁ h2 hWV 0 (LE hk₁ h2 hWV 2 F) : Esp G₀ k₁) : MFn) r -
        ((LE hk₁ h2 hWV 2 (LE hk₁ h2 hWV 0 F) : Esp G₀ k₁) : MFn) r =
      - ((LE hk₁ h2 hWV 1 F : Esp G₀ k₁) : MFn) r ∧
    ((LE hk₁ h2 hWV 1 (LE hk₁ h2 hWV 2 F) : Esp G₀ k₁) : MFn) r -
        ((LE hk₁ h2 hWV 2 (LE hk₁ h2 hWV 1 F) : Esp G₀ k₁) : MFn) r =
      ((LE hk₁ h2 hWV 0 F : Esp G₀ k₁) : MFn) r := by
  obtain ⟨G, hG, hGF⟩ := Submodule.mem_map.1 F.2
  have e1 : ∀ c, ((LE hk₁ h2 hWV c F : Esp G₀ k₁) : MFn) = readL k₁ (rotDc c G) :=
    fun c => LE_coe_of_eq hk₁ h2 hWV c F hG hGF
  have e2 : ∀ c c', ((LE hk₁ h2 hWV c (LE hk₁ h2 hWV c' F) : Esp G₀ k₁) : MFn) =
      readL k₁ (rotDc c (rotDc c' G)) :=
    fun c c' => LE_coe_of_eq hk₁ h2 hWV c _ (rotDc_mem_W h2 hWV hG c') (e1 c').symm
  simp only [e1, e2, readL_apply_of_mem k₁ _ hr]
  exact rotD_bracket (smooth_of_mem_W h2 hWV hG) _

end Esp

end

end WsE.FNT

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

namespace WsE
namespace FNT

noncomputable section

open scoped Classical
open MvPolynomial

theorem eval_smul_of_isHomogeneous {σ : Type*} {p : MvPolynomial σ ℂ} {ℓ : ℕ} (hp : p.IsHomogeneous ℓ)
    (c : ℂ) (x : σ → ℂ) :
    eval (fun i => c * x i) p = c ^ ℓ * eval x p := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : ∑ i ∈ d.support, d i = ℓ := by
    have h := hp (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  rw [Finset.prod_congr rfl fun i _ => mul_pow c (x i) (d i), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hw]
  ring

theorem exists_real_eval_ne_zero {p : MvPolynomial (Fin 3) ℂ} (hp : p ≠ 0) :
    ∃ x : Fin 3 → ℝ, eval (fun a => ((x a : ℝ) : ℂ)) p ≠ 0 := by
  by_contra h
  push Not at h
  apply hp
  refine MvPolynomial.funext_set (fun _ : Fin 3 => Set.range ((↑) : ℝ → ℂ))
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective) fun z hz => ?_
  rw [map_zero]
  have hz' : ∀ a : Fin 3, ∃ r : ℝ, (r : ℂ) = z a := fun a => hz a (Set.mem_univ a)
  choose x hx using hz'
  have : z = fun a => ((x a : ℝ) : ℂ) := funext fun a => (hx a).symm
  rw [this]
  exact h x

theorem exists_unit_eval_ne_zero {p : MvPolynomial (Fin 3) ℂ} {ℓ : ℕ} (hp : p ≠ 0) (hhom : p.IsHomogeneous ℓ) :
    ∃ w : Fin 3 → ℝ, (∑ t : Fin 3, w t ^ 2) = 1 ∧ eval (fun a => ((w a : ℝ) : ℂ)) p ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_real_eval_ne_zero hp
  have hs0 : 0 ≤ ∑ t : Fin 3, x t ^ 2 := Finset.sum_nonneg fun t _ => sq_nonneg (x t)
  set n : ℝ := Real.sqrt (∑ t : Fin 3, x t ^ 2) with hn
  have hn2 : n ^ 2 = ∑ t : Fin 3, x t ^ 2 := Real.sq_sqrt hs0
  by_cases h0 : n = 0
  · have hx0 : ∀ t, x t = 0 := by
      have hsum : ∑ t : Fin 3, x t ^ 2 = 0 := by rw [← hn2, h0]; ring
      intro t
      exact pow_eq_zero_iff two_ne_zero |>.1
        ((Finset.sum_eq_zero_iff_of_nonneg fun t _ => sq_nonneg (x t)).1 hsum t (Finset.mem_univ t))
    refine ⟨ej 0, by simp [ej], fun hw => hx ?_⟩
    have : (fun a : Fin 3 => ((x a : ℝ) : ℂ)) = fun a => (0 : ℂ) * ((ej 0 a : ℝ) : ℂ) := by
      funext a; rw [hx0 a]; simp
    rw [this, eval_smul_of_isHomogeneous hhom, hw, mul_zero]
  · refine ⟨fun t => n⁻¹ * x t, ?_, fun hw => hx ?_⟩
    · calc ∑ t : Fin 3, (n⁻¹ * x t) ^ 2 = n⁻¹ ^ 2 * ∑ t : Fin 3, x t ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun t _ => mul_pow _ _ _
        _ = 1 := by rw [← hn2]; field_simp
    · have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast h0
      have : (fun a : Fin 3 => ((x a : ℝ) : ℂ)) = fun a => (n : ℂ) * (((n⁻¹ * x a : ℝ)) : ℂ) := by
        funext a; push_cast; rw [← mul_assoc, mul_inv_cancel₀ hn', one_mul]
      rw [this, eval_smul_of_isHomogeneous hhom, hw, mul_zero]

theorem detC_eq (o : Matrix (Fin 3) (Fin 3) ℝ) :
    (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det = ((o.det : ℝ) : ℂ) := by
  have : (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)) = (Complex.ofRealHom : ℝ →+* ℂ).mapMatrix o := rfl
  rw [this, ← RingHom.map_det]
  rfl

theorem eval_realise_col (o : Fin 3 → Fin 3 → ℝ) (j : Fin 3) (q : MvPolynomial (Fin 3) ℂ) :
    eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
      (aeval (fun a : Fin 3 => (X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) q) =
    eval (fun i : Fin 3 => ((o i j : ℝ) : ℂ)) q := by
  rw [← show rename (fun a : Fin 3 => (a, j)) q =
      aeval (fun a : Fin 3 => (X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) q from by
    rw [rename_eq_aeval]; rfl, eval_rename]
  rfl

theorem neg_mem_O3 {r : Matrix (Fin 3) (Fin 3) ℝ} (hr : r ∈ Matrix.orthogonalGroup (Fin 3) ℝ) :
    -r ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff'] at hr ⊢
  rw [Matrix.transpose_neg, neg_mul_neg, hr]

theorem mod_two_eq_of_neg_one_pow_eq {m n : ℕ} (h : (-1 : ℂ) ^ m = (-1 : ℂ) ^ n) : m % 2 = n % 2 := by
  rw [neg_one_pow_eq_pow_mod_two m, neg_one_pow_eq_pow_mod_two n] at h
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;> rcases Nat.mod_two_eq_zero_or_one n with hn' | hn' <;>
    rw [hm, hn'] at h ⊢
  all_goals norm_num at h

end

end WsE.FNT

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem solution
    (ν : Fin 3 → ℂ) (lam₁ lam₂ lam₃ : ℂ) (ε : Fin 3 → Fin 2) (V Vε : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1)
    (hVε : (∀ G ∈ Vε, Continuous G) ∧
      (∀ G ∈ Vε, WhittakerBlock.IsArchSmooth3 G ∧ WhittakerBlock.casimir1 G = lam₁ • G ∧
        WhittakerBlock.casimir2 G = lam₂ • G ∧ WhittakerBlock.casimir3 G = lam₃ • G) ∧
      (∀ G ∈ Vε, ∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, G (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * G g) ∧
      (∀ G ∈ Vε, ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) →
        archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 → (fun g => G (g * k')) ∈ Vε) ∧
      (∀ G ∈ Vε, ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) → archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 →
          (fun g => G (g * k')) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) ∧
      (∀ G ∈ Vε, ∀ c₀ d₀ : Fin 3, ∃ G' ∈ Vε, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        HasDerivAt (fun s : ℝ => G (g * WhittakerBlock.archRealLift3 fun a b =>
          (if a = b then (1 : ℝ) else 0) + if a = c₀ ∧ b = d₀ then s else 0)) (G' g) 0) ∧
      (∀ G ∈ Vε, ∀ σ : Fin 3 → Fin 2, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        G (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (σ a : ℕ) else 0) * g) =
          (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (σ a : ℕ)) * G g) ∧
      (∀ G ∈ Vε, ∃ F ∈ V, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        G g = (1 / 8 : ℂ) * ∑ σ : Fin 3 → Fin 2, (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (σ a : ℕ)) *
          F (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (σ a : ℕ) else 0) * g)))
    (hne : (∃ G ∈ Vε, ∃ o : Fin 3 → Fin 3 → ℝ,
        (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) ∧ G (WhittakerBlock.archRealLift3 o * k₁) ≠ 0)) :
    ∃ (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ), p ≠ 0 ∧ p.IsHomogeneous ℓ ∧
      (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0 ∧
      ∃ G' ∈ Vε, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
          (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p) =
        G' (WhittakerBlock.archRealLift3 o * k₁) := by
  classical
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := hVε
  obtain ⟨G₀, hG₀V, o₀, ho₀, hG₀ne⟩ := hne
  have h2 : ∀ G ∈ Vε, WhittakerBlock.IsArchSmooth3 G := fun G hG => (hc2 G hG).1
  have hWV : WsE.FNT.W G₀ ≤ Vε := WsE.FNT.W_le hG₀V hc4
  haveI hfd : FiniteDimensional ℂ (WsE.FNT.W G₀) := WsE.FNT.W_fd (hc5 G₀ hG₀V)
  haveI : FiniteDimensional ℂ (WsE.FNT.Esp G₀ k₁) := by unfold WsE.FNT.Esp; infer_instance

  have ho₀' : Matrix.of o₀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ := (WsE.FNT.mem_O3_iff _).2 ho₀
  have hneE : ∃ F ∈ WsE.FNT.Esp G₀ k₁, ∃ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ, F r ≠ 0 := by
    refine ⟨WsE.FNT.readL k₁ G₀, Submodule.mem_map_of_mem (WsE.FNT.self_mem_W G₀), Matrix.of o₀, ho₀', ?_⟩
    rw [WsE.FNT.readL_apply_of_mem k₁ _ ho₀']
    exact hG₀ne
  have hstabE : ∀ F ∈ WsE.FNT.Esp G₀ k₁, ∀ r₀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
      (fun r => F (r * r₀)) ∈ WsE.FNT.Esp G₀ k₁ := by
    rintro F hF r₀ hr₀
    obtain ⟨G, hG, rfl⟩ := Submodule.mem_map.1 hF
    rw [WsE.FNT.readL_transl hk₁ G hr₀]
    exact Submodule.mem_map_of_mem
      (WsE.FNT.transl_mem_W G₀ hG (WsE.FNT.isArchOrth_lift r₀ ((WsE.FNT.mem_O3_iff r₀).1 hr₀)))
  have hEX := exists_det_pow_mul_columnRealisation_mem_of_finiteDimensional_of_orthogonalRightStable 0
    (WsE.FNT.Esp G₀ k₁) hneE hstabE (WsE.FNT.LE hk₁ h2 hWV)
    (fun F c r hr => WsE.FNT.LE_tie hk₁ h2 hWV F c hr) (fun F r hr => WsE.FNT.LE_comm hk₁ h2 hWV F hr)
  obtain ⟨α, ℓ, p, hp0, hhom, hharm, F, hFE, hread⟩ := hEX
  obtain ⟨G', hG'W, hG'F⟩ := Submodule.mem_map.1 hFE

  have hFG : ∀ r ∈ Matrix.orthogonalGroup (Fin 3) ℝ, F r = G' (WhittakerBlock.archRealLift3 r * k₁) := by
    intro r hr
    rw [← hG'F, WsE.FNT.readL_apply_of_mem k₁ _ hr]

  have hα : (α : ℕ) = (ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2 := by
    obtain ⟨w, hw1, hwne⟩ := WsE.FNT.exists_unit_eval_ne_zero hp0 hhom
    set r₀ : Matrix (Fin 3) (Fin 3) ℝ := WsE.FNT.HH 0 w with hr₀def
    have hr₀ : r₀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ := (WsE.FNT.mem_O3_iff _).2 (WsE.FNT.HH_colOrth 0 w hw1)
    have hnr₀ : -r₀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ := WsE.FNT.neg_mem_O3 hr₀
    have hdet : r₀.det ≠ 0 := WsE.FNT.det_ne_zero_of_mem_O3 hr₀
    have hcol : (fun a : Fin 3 => ((r₀ a 0 : ℝ) : ℂ)) = fun a => ((w a : ℝ) : ℂ) :=
      funext fun a => by
        show ((WsE.FNT.HH 0 w a 0 : ℝ) : ℂ) = _
        rw [WsE.FNT.HH_col 0 w hw1 a]
    have hcoln : (fun a : Fin 3 => (((-r₀) a 0 : ℝ) : ℂ)) = fun a => (-1 : ℂ) * ((w a : ℝ) : ℂ) :=
      funext fun a => by
        show (((-WsE.FNT.HH 0 w) a 0 : ℝ) : ℂ) = _
        rw [Matrix.neg_apply, WsE.FNT.HH_col 0 w hw1 a]
        push_cast
        ring

    have hiso := hc7 G' (hWV hG'W) (fun _ => 1) (WhittakerBlock.archRealLift3 r₀ * k₁)
    have hD : (fun a b : Fin 3 => if a = b then (-1 : ℝ) ^ (((fun _ : Fin 3 => (1 : Fin 2)) a : Fin 2) : ℕ) else 0) =
        ((-1 : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → Fin 3 → ℝ) := by
      funext a b
      rw [Matrix.neg_apply, Matrix.one_apply]
      split_ifs <;> simp
    have hDdet : (-1 : Matrix (Fin 3) (Fin 3) ℝ).det ≠ 0 := by
      rw [Matrix.det_neg, Matrix.det_one, Fintype.card_fin]; norm_num
    have hlift : WhittakerBlock.archRealLift3
          (fun a b : Fin 3 => if a = b then (-1 : ℝ) ^ (((fun _ : Fin 3 => (1 : Fin 2)) a : Fin 2) : ℕ) else 0) *
        WhittakerBlock.archRealLift3 r₀ = WhittakerBlock.archRealLift3 (-r₀) := by
      rw [hD, ← WsE.FNT.lift_mul (-1) r₀ hDdet hdet, neg_one_mul]
    rw [← mul_assoc, hlift] at hiso
    have key : F (-r₀) = (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ)) * F r₀ := by
      rw [hFG _ hnr₀, hFG _ hr₀, hiso]
      simp
    rw [hread r₀ hr₀, hread (-r₀) hnr₀, WsE.FNT.eval_realise_col, WsE.FNT.eval_realise_col, hcoln, hcol,
      WsE.FNT.eval_smul_of_isHomogeneous hhom, Matrix.det_neg, Fintype.card_fin] at key
    push_cast at key
    have hX : ((r₀.det : ℝ) : ℂ) ^ (α : ℕ) * MvPolynomial.eval (fun a => ((w a : ℝ) : ℂ)) p ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hdet)) hwne
    have hsign : (-1 : ℂ) ^ ((α : ℕ) + ℓ) = (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ)) := by
      apply mul_right_cancel₀ hX
      rw [← key]
      ring
    have hpar := WsE.FNT.mod_two_eq_of_neg_one_pow_eq hsign
    have hα2 : (α : ℕ) < 2 := α.isLt
    omega
  refine ⟨ℓ, p, hp0, hhom, hharm, G', hWV hG'W, fun o ho => ?_⟩
  have hoO : Matrix.of o ∈ Matrix.orthogonalGroup (Fin 3) ℝ := (WsE.FNT.mem_O3_iff _).2 ho
  have hr := hread (Matrix.of o) hoO
  rw [hFG _ hoO] at hr
  rw [← hα, WsE.FNT.detC_eq]
  exact hr.symm

end S_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_of_signIsotypic_apply_ne_zero
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_isHomogeneous_harmonic_read_of_signIsotypic_apply_ne_zero (solution)
