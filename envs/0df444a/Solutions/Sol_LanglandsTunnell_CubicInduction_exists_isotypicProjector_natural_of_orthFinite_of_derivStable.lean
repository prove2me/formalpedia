-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_isotypicProjector_natural_of_orthFinite_of_derivStable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/4faf5034-d055-5af8-ae75-e9aeb15c595b

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_hasDerivAt_comp_archRealLift3_rotation_of_isArchSmooth3
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_isotypicProjector_natural_of_orthFinite_of_derivStable

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction
open scoped Topology

namespace WsE
namespace IP

noncomputable section

private def _root_.WsE.IP.ofRealHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v : InfinitePlace ℚ =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.toRingHom

p2m_export "WsE.IP" "ofRealHom"
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

noncomputable section

abbrev Fn := AdelicGL 3 (𝓞 ℚ) ℚ → ℂ

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

def rotArr (c₁ c₂ : Fin 3) (s : ℝ) : Fin 3 → Fin 3 → ℝ := fun i j =>
  if i = c₁ ∧ j = c₁ then Real.cos s else if i = c₂ ∧ j = c₂ then Real.cos s else
  if i = c₁ ∧ j = c₂ then - Real.sin s else if i = c₂ ∧ j = c₁ then Real.sin s else
  if i = j then 1 else 0

theorem colOrth_rotArr {c₁ c₂ : Fin 3} (hne : c₁ ≠ c₂) (s : ℝ) : ColOrth (rotArr c₁ c₂ s) := by
  have hsc := Real.sin_sq_add_cos_sq s
  intro i j
  rcases fin3_cases c₁ with h1 | h1 | h1 <;> rcases fin3_cases c₂ with h2 | h2 | h2 <;> subst h1 h2 <;>
    first
    | exact absurd rfl hne
    | (rcases fin3_cases i with h3 | h3 | h3 <;> rcases fin3_cases j with h4 | h4 | h4 <;> subst h3 h4 <;>
        simp [rotArr, Fin.sum_univ_three] <;> first | linear_combination hsc | linear_combination)

section R1

variable {X : Submodule ℂ Fn}
  (hK : ∀ w ∈ X, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
    (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
      (fun g => w (g * k)) ∈ X)
  (hfin : ∀ w ∈ X, ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
    (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
      (fun g => w (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
  (hsm : ∀ w ∈ X, WhittakerBlock.IsArchSmooth3 w)

def Vspan (u : Fn) : Submodule ℂ Fn :=
  Submodule.span ℂ {w : Fn | ∃ k : AdelicGL 3 (𝓞 ℚ) ℚ,
    (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) ∧ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
      w = fun g => u (g * k)}

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

theorem transl_mem_Vspan_gen (u : Fn) {k : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hk1 : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) (hk2 : archComponent3 (𝓞 ℚ) ℚ k ∈ orth3) :
    (fun g => u (g * k)) ∈ Vspan u :=
  Submodule.subset_span ⟨k, hk1, hk2, rfl⟩

theorem self_mem_Vspan (u : Fn) : u ∈ Vspan u := by
  have := transl_mem_Vspan_gen u (k := 1) (fun p => map_one _) (by rw [map_one]; exact one_mem_orth3)
  simpa using this

theorem transl_mem_Vspan (u : Fn) {v : Fn} (hv : v ∈ Vspan u) {k : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hk1 : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) (hk2 : archComponent3 (𝓞 ℚ) ℚ k ∈ orth3) :
    (fun g => v (g * k)) ∈ Vspan u := by
  have hmap : (Vspan u).map (LinearMap.funLeft ℂ ℂ (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => g * k)) ≤ Vspan u := by
    rw [Vspan, Submodule.map_span_le]
    rintro _ ⟨k', hk'1, hk'2, rfl⟩
    have : (LinearMap.funLeft ℂ ℂ (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => g * k)) (fun g => u (g * k')) =
        fun g => u (g * (k * k')) := by
      funext g; simp [LinearMap.funLeft_apply, mul_assoc]
    rw [this]
    exact transl_mem_Vspan_gen u (fun p => by rw [map_mul, hk1 p, hk'1 p, one_mul])
      (by rw [map_mul]; exact mul_mem_orth3 hk2 hk'2)
  exact hmap ⟨v, hv, rfl⟩

include hK in
theorem Vspan_le {u : Fn} (hu : u ∈ X) : Vspan u ≤ X := by
  rw [Vspan, Submodule.span_le]
  rintro _ ⟨k, hk1, hk2, rfl⟩
  exact hK u hu k hk1 hk2

include hfin in
theorem Vspan_fd {u : Fn} (hu : u ∈ X) : FiniteDimensional ℂ (Vspan u) := by
  obtain ⟨s, hs⟩ := hfin u hu
  have hle : Vspan u ≤ Submodule.span ℂ (s : Set Fn) := by
    rw [Vspan, Submodule.span_le]
    rintro _ ⟨k, hk1, hk2, rfl⟩
    exact hs k hk1 hk2
  exact Submodule.finiteDimensional_of_le hle

theorem lift_archOrth (o : Matrix (Fin 3) (Fin 3) ℝ) (ho : ColOrth o) :
    (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p (WhittakerBlock.archRealLift3 o) = 1) ∧
    archComponent3 (𝓞 ℚ) ℚ (WhittakerBlock.archRealLift3 o) ∈ orth3 :=
  ⟨componentAt3_lift o (det_ne_zero_of_colOrth o ho),
    archComponent3_lift_mem_orth3 o (det_ne_zero_of_colOrth o ho) ((colOrth_iff o).1 ho)⟩

include hK hfin hsm in

theorem rot_mem_Vspan {u : Fn} (hu : u ∈ X) {v : Fn} (hv : v ∈ Vspan u) (i j : Fin 3) :
    WhittakerBlock.archDeriv i j v - WhittakerBlock.archDeriv j i v ∈ Vspan u := by
  by_cases hij : i = j
  · subst hij; rw [sub_self]; exact (Vspan u).zero_mem
  haveI := Vspan_fd hfin hu
  have hvs : WhittakerBlock.IsArchSmooth3 v := hsm v (Vspan_le hK hu hv)
  have hclosed : IsClosed ((Vspan u : Submodule ℂ Fn) : Set Fn) := (Vspan u).closed_of_finiteDimensional

  let F : ℝ → Fn := fun t g =>
    (t - 0)⁻¹ • (v (g * WhittakerBlock.archRealLift3 (rotArr j i t)) - v (g * WhittakerBlock.archRealLift3 (rotArr j i 0)))
  have hmem : ∀ t, F t ∈ Vspan u := by
    intro t
    have h1 := transl_mem_Vspan u hv (lift_archOrth (Matrix.of (rotArr j i t)) (colOrth_rotArr (Ne.symm hij) t)).1
      (lift_archOrth (Matrix.of (rotArr j i t)) (colOrth_rotArr (Ne.symm hij) t)).2
    have h2 := transl_mem_Vspan u hv (lift_archOrth (Matrix.of (rotArr j i 0)) (colOrth_rotArr (Ne.symm hij) 0)).1
      (lift_archOrth (Matrix.of (rotArr j i 0)) (colOrth_rotArr (Ne.symm hij) 0)).2
    have h3 := (Vspan u).smul_mem (((t - 0)⁻¹ : ℝ) : ℂ) ((Vspan u).sub_mem h1 h2)
    have : F t = (((t - 0)⁻¹ : ℝ) : ℂ) • ((fun g => v (g * WhittakerBlock.archRealLift3 (Matrix.of (rotArr j i t)))) -
        fun g => v (g * WhittakerBlock.archRealLift3 (Matrix.of (rotArr j i 0)))) := by
      funext g
      simp only [F, Pi.smul_apply, Pi.sub_apply, Complex.real_smul, smul_eq_mul]
      rfl
    rw [this]
    exact h3
  have hlim : Filter.Tendsto F (𝓝[≠] 0)
      (𝓝 (fun g => WhittakerBlock.archDeriv i j v g - WhittakerBlock.archDeriv j i v g)) := by
    rw [tendsto_pi_nhds]
    intro g
    have hd := WhittakerBlock.hasDerivAt_comp_archRealLift3_rotation_of_isArchSmooth3 v hvs j i g
    rw [hasDerivAt_iff_tendsto_slope] at hd
    exact hd
  exact hclosed.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)

end R1

def negId : Fin 3 → Fin 3 → ℝ := fun a b => if a = b then (-1 : ℝ) else 0

theorem negId_eq : (Matrix.of negId : Matrix (Fin 3) (Fin 3) ℝ) = -1 := by
  ext a b
  simp only [Matrix.of_apply, negId, Matrix.neg_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem det_negId : (Matrix.of negId).det ≠ 0 := by
  rw [negId_eq, Matrix.det_neg, Matrix.det_one, Fintype.card_fin]; norm_num

theorem lift_one : WhittakerBlock.archRealLift3 (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  refine Units.ext ?_
  have hdet : (Matrix.of (1 : Matrix (Fin 3) (Fin 3) ℝ)).det ≠ 0 := by
    rw [show Matrix.of (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 from rfl, Matrix.det_one]; exact one_ne_zero
  rw [val_lift _ hdet, archRealMat3_eq, Units.val_one]
  have : realM (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
    rw [realM, Matrix.map_one ofRealHom (map_zero _) (map_one _)]
  exact (congrArg (archMatrixInclN (Fin 3) ℚ) this).trans (archMatrixInclN_one (Fin 3) ℚ)

theorem negId_lift_mul_self :
    WhittakerBlock.archRealLift3 negId * WhittakerBlock.archRealLift3 negId = 1 := by
  have hln : WhittakerBlock.archRealLift3 negId = WhittakerBlock.archRealLift3 (Matrix.of negId) := rfl
  rw [hln, ← lift_mul (Matrix.of negId) (Matrix.of negId) det_negId det_negId, negId_eq, neg_mul_neg, one_mul,
    lift_one]

theorem transl_negId_transl_negId (w : Fn) :
    (fun g => (fun g' => w (g' * WhittakerBlock.archRealLift3 negId)) (g * WhittakerBlock.archRealLift3 negId)) = w := by
  funext g
  simp only [mul_assoc, negId_lift_mul_self, mul_one]

theorem archDeriv_transl_negId (w : Fn) (i j : Fin 3) :
    WhittakerBlock.archDeriv i j (fun g => w (g * WhittakerBlock.archRealLift3 negId)) =
      fun g => WhittakerBlock.archDeriv i j w (g * WhittakerBlock.archRealLift3 negId) := by
  funext g
  simp only [WhittakerBlock.archDeriv]
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with s hs
  set Fl : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.of (fun a b : Fin 3 => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) with hFl
  have hlf : WhittakerBlock.archRealLift3 (fun a b : Fin 3 => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) =
      WhittakerBlock.archRealLift3 Fl := rfl
  have hdf : Fl.det ≠ 0 := by
    have : Fl.det = if i = j then 1 + s else 1 := by
      rcases fin3_cases i with h1 | h1 | h1 <;> rcases fin3_cases j with h2 | h2 | h2 <;> subst h1 h2 <;>
        simp [hFl, Matrix.det_fin_three] <;> ring
    rw [this]; split_ifs
    · have : (-1 : ℝ) < s := hs; linarith
    · exact one_ne_zero
  have hln : WhittakerBlock.archRealLift3 negId = WhittakerBlock.archRealLift3 (Matrix.of negId) := rfl
  show w (g * WhittakerBlock.archRealLift3 _ * WhittakerBlock.archRealLift3 negId) =
    w (g * WhittakerBlock.archRealLift3 negId * WhittakerBlock.archRealLift3 _)
  rw [hlf, hln, mul_assoc, mul_assoc, ← lift_mul Fl (Matrix.of negId) hdf det_negId,
    ← lift_mul (Matrix.of negId) Fl det_negId hdf, negId_eq, mul_neg_one, neg_one_mul]

def Om (f : Fn) : Fn :=
  (WhittakerBlock.archDeriv 0 1 (WhittakerBlock.archDeriv 0 1 f - WhittakerBlock.archDeriv 1 0 f) -
      WhittakerBlock.archDeriv 1 0 (WhittakerBlock.archDeriv 0 1 f - WhittakerBlock.archDeriv 1 0 f)) +
    (WhittakerBlock.archDeriv 0 2 (WhittakerBlock.archDeriv 0 2 f - WhittakerBlock.archDeriv 2 0 f) -
      WhittakerBlock.archDeriv 2 0 (WhittakerBlock.archDeriv 0 2 f - WhittakerBlock.archDeriv 2 0 f)) +
    (WhittakerBlock.archDeriv 1 2 (WhittakerBlock.archDeriv 1 2 f - WhittakerBlock.archDeriv 2 1 f) -
      WhittakerBlock.archDeriv 2 1 (WhittakerBlock.archDeriv 1 2 f - WhittakerBlock.archDeriv 2 1 f))

section R3

variable {X : Submodule ℂ Fn}
  (hD : ∀ w ∈ X, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ X)
  (B : Fn → Fn → ℂ)
  (hB1 : ∀ w ∈ X, ∀ w' ∈ X, B w' w = (starRingEnd ℂ) (B w w'))
  (hB2 : ∀ (z : ℂ), ∀ w₁ ∈ X, ∀ w₂ ∈ X, ∀ w' ∈ X, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
  (hB4 : ∀ w ∈ X, ∀ w' ∈ X, ∀ i j : Fin 3,
    B (WhittakerBlock.archDeriv i j w) w' = - B w (WhittakerBlock.archDeriv i j w'))

include hB2 in
theorem B_sub_left {w₁ w₂ w' : Fn} (h₁ : w₁ ∈ X) (h₂ : w₂ ∈ X) (h' : w' ∈ X) :
    B (w₁ - w₂) w' = B w₁ w' - B w₂ w' := by
  have h := hB2 (-1) w₂ h₂ w₁ h₁ w' h'
  rw [neg_one_smul, neg_add_eq_sub] at h
  rw [h]; ring

include hB2 in
theorem B_add_left {w₁ w₂ w' : Fn} (h₁ : w₁ ∈ X) (h₂ : w₂ ∈ X) (h' : w' ∈ X) :
    B (w₁ + w₂) w' = B w₁ w' + B w₂ w' := by
  have h := hB2 1 w₁ h₁ w₂ h₂ w' h'
  rw [one_smul, one_mul] at h
  exact h

include hB1 hB2 in
theorem B_sub_right {w w₁ w₂ : Fn} (h : w ∈ X) (h₁ : w₁ ∈ X) (h₂ : w₂ ∈ X) :
    B w (w₁ - w₂) = B w w₁ - B w w₂ := by
  rw [hB1 (w₁ - w₂) (X.sub_mem h₁ h₂) w h, hB1 w₁ h₁ w h, hB1 w₂ h₂ w h, B_sub_left B hB2 h₁ h₂ h, map_sub]

include hB1 hB2 in
theorem B_add_right {w w₁ w₂ : Fn} (h : w ∈ X) (h₁ : w₁ ∈ X) (h₂ : w₂ ∈ X) :
    B w (w₁ + w₂) = B w w₁ + B w w₂ := by
  rw [hB1 (w₁ + w₂) (X.add_mem h₁ h₂) w h, hB1 w₁ h₁ w h, hB1 w₂ h₂ w h, B_add_left B hB2 h₁ h₂ h, map_add]

include hD in
theorem L_mem {w : Fn} (hw : w ∈ X) (i j : Fin 3) :
    WhittakerBlock.archDeriv i j w - WhittakerBlock.archDeriv j i w ∈ X :=
  X.sub_mem (hD w hw i j) (hD w hw j i)

include hD hB1 hB2 hB4 in

theorem B_L_skew {w w' : Fn} (hw : w ∈ X) (hw' : w' ∈ X) (i j : Fin 3) :
    B (WhittakerBlock.archDeriv i j w - WhittakerBlock.archDeriv j i w) w' =
      - B w (WhittakerBlock.archDeriv i j w' - WhittakerBlock.archDeriv j i w') := by
  rw [B_sub_left B hB2 (hD w hw i j) (hD w hw j i) hw', hB4 w hw w' hw' i j, hB4 w hw w' hw' j i,
    B_sub_right B hB1 hB2 hw (hD w' hw' i j) (hD w' hw' j i)]
  ring

include hD hB1 hB2 hB4 in

theorem B_LL_symm {w w' : Fn} (hw : w ∈ X) (hw' : w' ∈ X) (i j : Fin 3) :
    B (WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv i j w - WhittakerBlock.archDeriv j i w) -
        WhittakerBlock.archDeriv j i (WhittakerBlock.archDeriv i j w - WhittakerBlock.archDeriv j i w)) w' =
      B w (WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv i j w' - WhittakerBlock.archDeriv j i w') -
        WhittakerBlock.archDeriv j i (WhittakerBlock.archDeriv i j w' - WhittakerBlock.archDeriv j i w')) := by
  rw [B_L_skew hD B hB1 hB2 hB4 (L_mem hD hw i j) hw' i j,
    ← neg_neg (B w _), ← B_L_skew hD B hB1 hB2 hB4 hw (L_mem hD hw' i j) i j]

include hD in
theorem LL_mem {w : Fn} (hw : w ∈ X) (i j : Fin 3) :
    WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv i j w - WhittakerBlock.archDeriv j i w) -
      WhittakerBlock.archDeriv j i (WhittakerBlock.archDeriv i j w - WhittakerBlock.archDeriv j i w) ∈ X :=
  L_mem hD (L_mem hD hw i j) i j

include hD in
theorem Om_mem {w : Fn} (hw : w ∈ X) : Om w ∈ X :=
  X.add_mem (X.add_mem (LL_mem hD hw 0 1) (LL_mem hD hw 0 2)) (LL_mem hD hw 1 2)

include hD hB1 hB2 hB4 in

theorem B_Om_symm {w w' : Fn} (hw : w ∈ X) (hw' : w' ∈ X) : B (Om w) w' = B w (Om w') := by
  simp only [Om]
  rw [B_add_left B hB2 (X.add_mem (LL_mem hD hw 0 1) (LL_mem hD hw 0 2)) (LL_mem hD hw 1 2) hw',
    B_add_left B hB2 (LL_mem hD hw 0 1) (LL_mem hD hw 0 2) hw',
    B_add_right B hB1 hB2 hw (X.add_mem (LL_mem hD hw' 0 1) (LL_mem hD hw' 0 2)) (LL_mem hD hw' 1 2),
    B_add_right B hB1 hB2 hw (LL_mem hD hw' 0 1) (LL_mem hD hw' 0 2),
    B_LL_symm hD B hB1 hB2 hB4 hw hw' 0 1, B_LL_symm hD B hB1 hB2 hB4 hw hw' 0 2,
    B_LL_symm hD B hB1 hB2 hB4 hw hw' 1 2]

end R3

end

end WsE.IP

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction
open scoped Topology

namespace WsE
namespace IP

noncomputable section

def mulArr (o r : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ := fun i j => ∑ k : Fin 3, o i k * r k j

theorem mulArr_eq (o r : Fin 3 → Fin 3 → ℝ) : mulArr o r = fun i j => (Matrix.of o * Matrix.of r) i j := by
  funext i j; simp [mulArr, Matrix.mul_apply]

theorem colOrth_mul' (o H : Matrix (Fin 3) (Fin 3) ℝ) (ho : ColOrth o) (hH : ColOrth H) : ColOrth (o * H) := by
  rw [colOrth_iff] at ho hH ⊢
  calc (o * H).transpose * (o * H) = H.transpose * (o.transpose * o) * H := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [ho, Matrix.mul_one, hH]

theorem colOrth_mulArr {o r : Fin 3 → Fin 3 → ℝ} (ho : ColOrth o) (hr : ColOrth r) : ColOrth (mulArr o r) := by
  rw [mulArr_eq]; exact colOrth_mul' (Matrix.of o) (Matrix.of r) ho hr

theorem rotArr_zero (c₁ c₂ : Fin 3) (hne : c₁ ≠ c₂) : rotArr c₁ c₂ 0 = fun i j => if i = j then (1 : ℝ) else 0 := by
  funext i j
  simp only [rotArr, Real.cos_zero, Real.sin_zero, neg_zero]
  by_cases hij : i = j
  · subst hij
    by_cases h1 : i = c₁
    · subst h1; simp [hne]
    · by_cases h2 : i = c₂
      · subst h2; simp [h1]
      · simp [h1, h2]
  · simp only [if_neg hij]
    split_ifs with h1 h2 h3 h4
    · exact absurd (h1.1.trans h1.2.symm) hij
    · exact absurd (h2.1.trans h2.2.symm) hij
    · rfl
    · rfl
    · rfl

theorem mulArr_one (o : Fin 3 → Fin 3 → ℝ) : mulArr o (fun i j => if i = j then (1 : ℝ) else 0) = o := by
  funext i j
  simp [mulArr, Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem rotArr_add_01 (s t : ℝ) :
    rotArr 0 1 (s + t) = mulArr (rotArr 0 1 s) (rotArr 0 1 t) := by
  funext i j
  rcases fin3_cases i with hi | hi | hi <;> rcases fin3_cases j with hj | hj | hj <;> subst hi hj <;>
    simp [rotArr, mulArr, Fin.sum_univ_three, Real.cos_add, Real.sin_add] <;> ring

theorem rotArr_add_02 (s t : ℝ) :
    rotArr 0 2 (s + t) = mulArr (rotArr 0 2 s) (rotArr 0 2 t) := by
  funext i j
  rcases fin3_cases i with hi | hi | hi <;> rcases fin3_cases j with hj | hj | hj <;> subst hi hj <;>
    simp [rotArr, mulArr, Fin.sum_univ_three, Real.cos_add, Real.sin_add] <;> ring

theorem rotArr_add_12 (s t : ℝ) :
    rotArr 1 2 (s + t) = mulArr (rotArr 1 2 s) (rotArr 1 2 t) := by
  funext i j
  rcases fin3_cases i with hi | hi | hi <;> rcases fin3_cases j with hj | hj | hj <;> subst hi hj <;>
    simp [rotArr, mulArr, Fin.sum_univ_three, Real.cos_add, Real.sin_add] <;> ring

def IsPlane (c₁ c₂ : Fin 3) : Prop := (c₁ = 0 ∧ c₂ = 1) ∨ (c₁ = 0 ∧ c₂ = 2) ∨ (c₁ = 1 ∧ c₂ = 2)

theorem IsPlane.ne {c₁ c₂ : Fin 3} (h : IsPlane c₁ c₂) : c₁ ≠ c₂ := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem rotArr_add {c₁ c₂ : Fin 3} (h : IsPlane c₁ c₂) (s t : ℝ) :
    rotArr c₁ c₂ (s + t) = mulArr (rotArr c₁ c₂ s) (rotArr c₁ c₂ t) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact rotArr_add_01 s t
  · exact rotArr_add_02 s t
  · exact rotArr_add_12 s t

theorem lift_one' : WhittakerBlock.archRealLift3 (fun i j : Fin 3 => if i = j then (1 : ℝ) else 0) = 1 := by
  have : (fun i j : Fin 3 => if i = j then (1 : ℝ) else 0) = ((1 : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → Fin 3 → ℝ) := by
    funext i j; rw [Matrix.one_apply]
  rw [this]; exact lift_one

theorem lift_rotArr_add {c₁ c₂ : Fin 3} (h : IsPlane c₁ c₂) (s t : ℝ) :
    WhittakerBlock.archRealLift3 (rotArr c₁ c₂ (s + t)) =
      WhittakerBlock.archRealLift3 (rotArr c₁ c₂ s) * WhittakerBlock.archRealLift3 (rotArr c₁ c₂ t) := by
  rw [rotArr_add h, mulArr_eq]
  exact lift_mul (Matrix.of (rotArr c₁ c₂ s)) (Matrix.of (rotArr c₁ c₂ t))
    (det_ne_zero_of_colOrth _ (colOrth_rotArr h.ne s)) (det_ne_zero_of_colOrth _ (colOrth_rotArr h.ne t))

section Transport

variable {X : Submodule ℂ Fn}
  (hD : ∀ w ∈ X, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ X)
  (hK : ∀ w ∈ X, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
    (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
      (fun g => w (g * k)) ∈ X)
  (hfin : ∀ w ∈ X, ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
    (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
      (fun g => w (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
  (hsm : ∀ w ∈ X, WhittakerBlock.IsArchSmooth3 w)
  (Φ : ↥X →ₗ[ℂ] ((Fin 3 → Fin 3 → ℝ) → ℂ))
  (hΦ : ∀ (u : ↥X) (r : Fin 3 → Fin 3 → ℝ) (hr : (∀ i j : Fin 3, ∑ a : Fin 3, r a i * r a j = if i = j then 1 else 0))
      (k : AdelicGL 3 (𝓞 ℚ) ℚ) (hk₁ : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1)
      (hk₂ : archComponent3 (𝓞 ℚ) ℚ k ∈ orth3),
      k = WhittakerBlock.archRealLift3 r →
      ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        Φ ⟨fun g => (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g * k), hK u u.2 k hk₁ hk₂⟩ o =
          Φ u (fun i j => ∑ k : Fin 3, o i k * r k j))

def Rx (c₁ c₂ : Fin 3) (hne : c₁ ≠ c₂) (s : ℝ) (v : ↥X) : ↥X :=
  ⟨fun g => (v : Fn) (g * WhittakerBlock.archRealLift3 (rotArr c₁ c₂ s)),
    hK v v.2 _ (lift_archOrth (Matrix.of (rotArr c₁ c₂ s)) (colOrth_rotArr hne s)).1
      (lift_archOrth (Matrix.of (rotArr c₁ c₂ s)) (colOrth_rotArr hne s)).2⟩

def Lx (c₁ c₂ : Fin 3) (v : ↥X) : ↥X :=
  ⟨fun g => WhittakerBlock.archDeriv c₂ c₁ (v : Fn) g - WhittakerBlock.archDeriv c₁ c₂ (v : Fn) g,
    X.sub_mem (hD _ v.2 c₂ c₁) (hD _ v.2 c₁ c₂)⟩

def phi (c₁ c₂ : Fin 3) (hne : c₁ ≠ c₂) (v : ↥X) (o : Fin 3 → Fin 3 → ℝ) (s : ℝ) : ℂ :=
  Φ (Rx hK c₁ c₂ hne s v) o

include hΦ in
theorem phi_eq (c₁ c₂ : Fin 3) (hne : c₁ ≠ c₂) (v : ↥X) {o : Fin 3 → Fin 3 → ℝ} (ho : ColOrth o) (s : ℝ) :
    phi hK Φ c₁ c₂ hne v o s = Φ v (mulArr o (rotArr c₁ c₂ s)) :=
  hΦ v (rotArr c₁ c₂ s) (colOrth_rotArr hne s) _
    (lift_archOrth (Matrix.of (rotArr c₁ c₂ s)) (colOrth_rotArr hne s)).1
    (lift_archOrth (Matrix.of (rotArr c₁ c₂ s)) (colOrth_rotArr hne s)).2 rfl o ho

include hfin hsm in

theorem hasDerivAt_phi_zero (c₁ c₂ : Fin 3) (hne : c₁ ≠ c₂) (v : ↥X) (o : Fin 3 → Fin 3 → ℝ) :
    HasDerivAt (phi hK Φ c₁ c₂ hne v o) (Φ (Lx hD c₁ c₂ v) o) 0 := by
  haveI := Vspan_fd hfin v.2

  let lam : ↥(Vspan (v : Fn)) →ₗ[ℂ] ℂ :=
    { toFun := fun w => Φ ⟨(w : Fn), Vspan_le hK v.2 w.2⟩ o
      map_add' := fun w w' => by
        have : (⟨((w + w' : ↥(Vspan (v : Fn))) : Fn), Vspan_le hK v.2 (w + w').2⟩ : ↥X) =
            ⟨(w : Fn), Vspan_le hK v.2 w.2⟩ + ⟨(w' : Fn), Vspan_le hK v.2 w'.2⟩ := rfl
        rw [this, map_add]; rfl
      map_smul' := fun c w => by
        have : (⟨((c • w : ↥(Vspan (v : Fn))) : Fn), Vspan_le hK v.2 (c • w).2⟩ : ↥X) =
            c • ⟨(w : Fn), Vspan_le hK v.2 w.2⟩ := rfl
        rw [this, map_smul]; rfl }
  have hlam : Continuous lam := LinearMap.continuous_of_finiteDimensional lam

  let F : ℝ → Fn := fun t g =>
    (t - 0)⁻¹ • ((v : Fn) (g * WhittakerBlock.archRealLift3 (rotArr c₁ c₂ t)) -
      (v : Fn) (g * WhittakerBlock.archRealLift3 (rotArr c₁ c₂ 0)))
  have hR : ∀ t, (fun g => (v : Fn) (g * WhittakerBlock.archRealLift3 (rotArr c₁ c₂ t))) ∈ Vspan (v : Fn) :=
    fun t => transl_mem_Vspan (v : Fn) (self_mem_Vspan _)
      (lift_archOrth (Matrix.of (rotArr c₁ c₂ t)) (colOrth_rotArr hne t)).1
      (lift_archOrth (Matrix.of (rotArr c₁ c₂ t)) (colOrth_rotArr hne t)).2
  have hFeq : ∀ t, F t = (((t - 0)⁻¹ : ℝ) : ℂ) •
      ((fun g => (v : Fn) (g * WhittakerBlock.archRealLift3 (rotArr c₁ c₂ t))) -
        fun g => (v : Fn) (g * WhittakerBlock.archRealLift3 (rotArr c₁ c₂ 0))) := by
    intro t; funext g
    simp only [F, Pi.smul_apply, Pi.sub_apply, Complex.real_smul, smul_eq_mul]
  have hmem : ∀ t, F t ∈ Vspan (v : Fn) := by
    intro t; rw [hFeq]; exact (Vspan _).smul_mem _ ((Vspan _).sub_mem (hR t) (hR 0))
  have hL : (Lx hD c₁ c₂ v : Fn) ∈ Vspan (v : Fn) := rot_mem_Vspan hK hfin hsm v.2 (self_mem_Vspan _) c₂ c₁
  have hlim : Filter.Tendsto F (𝓝[≠] 0) (𝓝 (Lx hD c₁ c₂ v : Fn)) := by
    rw [tendsto_pi_nhds]
    intro g
    have hd := WhittakerBlock.hasDerivAt_comp_archRealLift3_rotation_of_isArchSmooth3 (v : Fn) (hsm _ v.2) c₁ c₂ g
    rw [hasDerivAt_iff_tendsto_slope] at hd
    exact hd
  have hlimV : Filter.Tendsto (fun t => (⟨F t, hmem t⟩ : ↥(Vspan (v : Fn)))) (𝓝[≠] 0)
      (𝓝 ⟨(Lx hD c₁ c₂ v : Fn), hL⟩) := by
    rw [tendsto_subtype_rng]; exact hlim
  have hcomp := (hlam.tendsto _).comp hlimV

  rw [hasDerivAt_iff_tendsto_slope]
  have hslope : slope (phi hK Φ c₁ c₂ hne v o) 0 = fun t => lam ⟨F t, hmem t⟩ := by
    funext t
    rw [slope_def_module]
    show (t - 0)⁻¹ • (phi hK Φ c₁ c₂ hne v o t - phi hK Φ c₁ c₂ hne v o 0) =
      Φ ⟨F t, Vspan_le hK v.2 (hmem t)⟩ o
    have : (⟨F t, Vspan_le hK v.2 (hmem t)⟩ : ↥X) =
        (((t - 0)⁻¹ : ℝ) : ℂ) • (Rx hK c₁ c₂ hne t v - Rx hK c₁ c₂ hne 0 v) := by
      apply Subtype.ext
      show F t = _
      rw [hFeq]; rfl
    rw [this, map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.real_smul]
    rfl
  rw [hslope]
  exact hcomp

end Transport

end

end WsE.IP

set_option autoImplicit false

noncomputable section

namespace RotCas

open WsE.IP

def mulA (o r : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ := fun i j => ∑ k : Fin 3, o i k * r k j

def d2 (G : (Fin 3 → Fin 3 → ℝ) → ℂ) (c₁ c₂ : Fin 3) (o : Fin 3 → Fin 3 → ℝ) : ℂ :=
  deriv (deriv (fun s : ℝ => G (mulA o (rotArr c₁ c₂ s)))) 0

def rotCas (G : (Fin 3 → Fin 3 → ℝ) → ℂ) (o : Fin 3 → Fin 3 → ℝ) : ℂ :=
  d2 G 0 1 o + d2 G 0 2 o + d2 G 1 2 o

theorem d2_congr {G G' : (Fin 3 → Fin 3 → ℝ) → ℂ} {c₁ c₂ : Fin 3} {o : Fin 3 → Fin 3 → ℝ}
    (h : ∀ s : ℝ, G (mulA o (rotArr c₁ c₂ s)) = G' (mulA o (rotArr c₁ c₂ s))) : d2 G c₁ c₂ o = d2 G' c₁ c₂ o := by
  simp only [d2, funext h]

theorem rotCas_congr {G G' : (Fin 3 → Fin 3 → ℝ) → ℂ} {o : Fin 3 → Fin 3 → ℝ}
    (h : ∀ (c₁ c₂ : Fin 3), c₁ ≠ c₂ → ∀ (s : ℝ), G (mulA o (rotArr c₁ c₂ s)) = G' (mulA o (rotArr c₁ c₂ s))) :
    rotCas G o = rotCas G' o := by
  simp only [rotCas, d2_congr (h 0 1 (by decide)), d2_congr (h 0 2 (by decide)), d2_congr (h 1 2 (by decide))]

theorem d2_const_mul (c : ℂ) (G : (Fin 3 → Fin 3 → ℝ) → ℂ) (c₁ c₂ : Fin 3) (o : Fin 3 → Fin 3 → ℝ) :
    d2 (fun o' => c * G o') c₁ c₂ o = c * d2 G c₁ c₂ o := by
  simp only [d2]
  have h1 : deriv (fun s : ℝ => c * G (mulA o (rotArr c₁ c₂ s))) = fun s => c * deriv (fun s : ℝ => G (mulA o (rotArr c₁ c₂ s))) s := by
    funext s; exact deriv_const_mul_field c
  rw [h1, deriv_const_mul_field]

theorem rotCas_const_mul (c : ℂ) (G : (Fin 3 → Fin 3 → ℝ) → ℂ) (o : Fin 3 → Fin 3 → ℝ) :
    rotCas (fun o' => c * G o') o = c * rotCas G o := by
  simp only [rotCas, d2_const_mul]; ring

theorem colOrth_mulA {o r : Fin 3 → Fin 3 → ℝ} (ho : ColOrth o) (hr : ColOrth r) : ColOrth (mulA o r) := by
  rw [colOrth_iff] at ho hr ⊢
  have hm : (mulA o r : Matrix (Fin 3) (Fin 3) ℝ) = Matrix.of o * Matrix.of r := by
    ext i j; simp [mulA, Matrix.mul_apply]
  have ho' : (Matrix.of o).transpose * Matrix.of o = 1 := ho
  have hr' : (Matrix.of r).transpose * Matrix.of r = 1 := hr
  have goal : (Matrix.of o * Matrix.of r).transpose * (Matrix.of o * Matrix.of r) = 1 := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.of o).transpose, ho', Matrix.one_mul, hr']
  rw [hm]; exact goal

theorem det_rotArr {c₁ c₂ : Fin 3} (hne : c₁ ≠ c₂) (s : ℝ) : (Matrix.of (rotArr c₁ c₂ s)).det = 1 := by
  have hsc := Real.sin_sq_add_cos_sq s
  rcases fin3_cases c₁ with rfl | rfl | rfl <;> rcases fin3_cases c₂ with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hne
    | (simp [Matrix.det_fin_three, rotArr]; nlinarith [hsc])

theorem det_mulA (o r : Fin 3 → Fin 3 → ℝ) :
    (Matrix.of (mulA o r)).det = (Matrix.of o).det * (Matrix.of r).det := by
  have : (Matrix.of (mulA o r) : Matrix (Fin 3) (Fin 3) ℝ) = Matrix.of o * Matrix.of r := by
    ext i j; simp [mulA, Matrix.mul_apply]
  rw [this, Matrix.det_mul]

theorem det_coe (o : Fin 3 → Fin 3 → ℝ) :
    (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det = (((Matrix.of o).det : ℝ) : ℂ) := by
  have : (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)) = (Matrix.of o).map (Complex.ofRealHom : ℝ →+* ℂ) := by
    ext i j; rfl
  rw [this]
  have h := RingHom.map_det Complex.ofRealHom (Matrix.of o)
  rw [RingHom.mapMatrix_apply] at h
  exact h.symm

theorem deriv2_trig (α β γ : ℂ) :
    deriv (deriv (fun s : ℝ => α + β * (Real.cos s : ℂ) + γ * (Real.sin s : ℂ))) 0 = -β := by
  have h1 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => α + β * (Real.cos s : ℂ) + γ * (Real.sin s : ℂ))
      (β * (-(Real.sin s) : ℝ) + γ * (Real.cos s : ℝ)) s := by
    intro s
    have hc := (Real.hasDerivAt_cos s).ofReal_comp
    have hs := (Real.hasDerivAt_sin s).ofReal_comp
    have h__af := ((hc.const_mul β).const_add α).add (hs.const_mul γ)
    simp at h__af ⊢
    exact h__af
  have hd : deriv (fun s : ℝ => α + β * (Real.cos s : ℂ) + γ * (Real.sin s : ℂ)) =
      fun s : ℝ => β * ((-(Real.sin s) : ℝ) : ℂ) + γ * (Real.cos s : ℂ) := funext fun s => (h1 s).deriv
  rw [hd]
  have h2 : HasDerivAt (fun s : ℝ => β * ((-(Real.sin s) : ℝ) : ℂ) + γ * (Real.cos s : ℂ))
      (β * ((-(Real.cos 0) : ℝ) : ℂ) + γ * ((-(Real.sin 0)) : ℝ)) 0 := by
    have hc := (Real.hasDerivAt_cos 0).ofReal_comp
    have hs := ((Real.hasDerivAt_sin 0).neg).ofReal_comp
    have := (hs.const_mul β).add (hc.const_mul γ)
    simp at this ⊢
    exact this
  rw [h2.deriv]; simp

theorem rotCas_eq_zero_of_detType (a : ℕ) (G : (Fin 3 → Fin 3 → ℝ) → ℂ)
    (hG : ∀ o r : Fin 3 → Fin 3 → ℝ, ColOrth o → ColOrth r →
      G (mulA o r) = (Matrix.of fun i j : Fin 3 => ((r i j : ℝ) : ℂ)).det ^ a * G o)
    (o : Fin 3 → Fin 3 → ℝ) (ho : ColOrth o) : rotCas G o = 0 := by
  have key : ∀ c₁ c₂ : Fin 3, c₁ ≠ c₂ → d2 G c₁ c₂ o = 0 := by
    intro c₁ c₂ hne
    have hfun : (fun s : ℝ => G (mulA o (rotArr c₁ c₂ s))) = fun _ => G o := by
      funext s
      rw [hG o _ ho (colOrth_rotArr hne s), det_coe, det_rotArr hne]; simp
    simp only [d2, hfun, deriv_const']
  simp only [rotCas, key 0 1 (by decide), key 0 2 (by decide), key 1 2 (by decide), add_zero]

theorem along_rot_eq (a : ℕ) (c : Fin 3 → Fin 3 → ℂ) (G : (Fin 3 → Fin 3 → ℝ) → ℂ)
    (hG : ∀ o : Fin 3 → Fin 3 → ℝ, ColOrth o →
      G o = (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ a * ∑ i : Fin 3, ∑ j : Fin 3, c i j * ((o i j : ℝ) : ℂ))
    (o : Fin 3 → Fin 3 → ℝ) (ho : ColOrth o) (p q r : Fin 3) (hpqr : (p = 0 ∧ q = 1 ∧ r = 2) ∨ (p = 0 ∧ q = 2 ∧ r = 1) ∨ (p = 1 ∧ q = 2 ∧ r = 0)) :
    (fun s : ℝ => G (mulA o (rotArr p q s))) = fun s : ℝ =>
      (((Matrix.of o).det : ℝ) : ℂ) ^ a * (∑ i : Fin 3, c i r * ((o i r : ℝ) : ℂ)) +
      ((((Matrix.of o).det : ℝ) : ℂ) ^ a * ∑ i : Fin 3, (c i p * ((o i p : ℝ) : ℂ) + c i q * ((o i q : ℝ) : ℂ))) * (Real.cos s : ℂ) +
      ((((Matrix.of o).det : ℝ) : ℂ) ^ a * ∑ i : Fin 3, (c i p * ((o i q : ℝ) : ℂ) - c i q * ((o i p : ℝ) : ℂ))) * (Real.sin s : ℂ) := by
  have hpq : p ≠ q := by rcases hpqr with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide
  funext s
  rw [hG _ (colOrth_mulA ho (colOrth_rotArr hpq s)), det_coe, det_mulA, det_rotArr hpq, mul_one]
  rcases hpqr with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  · simp only [mulA, rotArr, Fin.sum_univ_three, Fin.isValue, Fin.reduceEq, and_true, and_false, true_and, false_and,
      if_true, if_false, and_self]
    push_cast
    ring

theorem d2_eq (a : ℕ) (c : Fin 3 → Fin 3 → ℂ) (G : (Fin 3 → Fin 3 → ℝ) → ℂ)
    (hG : ∀ o : Fin 3 → Fin 3 → ℝ, ColOrth o →
      G o = (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ a * ∑ i : Fin 3, ∑ j : Fin 3, c i j * ((o i j : ℝ) : ℂ))
    (o : Fin 3 → Fin 3 → ℝ) (ho : ColOrth o) (p q r : Fin 3) (hpqr : (p = 0 ∧ q = 1 ∧ r = 2) ∨ (p = 0 ∧ q = 2 ∧ r = 1) ∨ (p = 1 ∧ q = 2 ∧ r = 0)) :
    d2 G p q o = -((((Matrix.of o).det : ℝ) : ℂ) ^ a * ∑ i : Fin 3, (c i p * ((o i p : ℝ) : ℂ) + c i q * ((o i q : ℝ) : ℂ))) := by
  rw [d2, along_rot_eq a c G hG o ho p q r hpqr, deriv2_trig]

theorem rotCas_eq_neg_two_mul_of_stdType (a : ℕ) (c : Fin 3 → Fin 3 → ℂ) (G : (Fin 3 → Fin 3 → ℝ) → ℂ)
    (hG : ∀ o : Fin 3 → Fin 3 → ℝ, ColOrth o →
      G o = (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ a * ∑ i : Fin 3, ∑ j : Fin 3, c i j * ((o i j : ℝ) : ℂ))
    (o : Fin 3 → Fin 3 → ℝ) (ho : ColOrth o) : rotCas G o = -2 * G o := by
  rw [rotCas, d2_eq a c G hG o ho 0 1 2 (Or.inl ⟨rfl, rfl, rfl⟩), d2_eq a c G hG o ho 0 2 1 (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)),
    d2_eq a c G hG o ho 1 2 0 (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)), hG o ho, det_coe]
  simp only [Fin.sum_univ_three]
  ring

end RotCas

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction
open scoped Topology

namespace WsA

noncomputable section

open WsE.IP RotCas

section Transport

variable {X : Submodule ℂ Fn}
  (hD : ∀ w ∈ X, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ X)
  (hK : ∀ w ∈ X, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
    (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
      (fun g => w (g * k)) ∈ X)
  (hfin : ∀ w ∈ X, ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
    (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
      (fun g => w (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
  (hsm : ∀ w ∈ X, WhittakerBlock.IsArchSmooth3 w)
  (Φ : ↥X →ₗ[ℂ] ((Fin 3 → Fin 3 → ℝ) → ℂ))
  (hΦ : ∀ (u : ↥X) (r : Fin 3 → Fin 3 → ℝ) (hr : (∀ i j : Fin 3, ∑ a : Fin 3, r a i * r a j = if i = j then 1 else 0))
      (k : AdelicGL 3 (𝓞 ℚ) ℚ) (hk₁ : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1)
      (hk₂ : archComponent3 (𝓞 ℚ) ℚ k ∈ orth3),
      k = WhittakerBlock.archRealLift3 r →
      ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        Φ ⟨fun g => (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g * k), hK u u.2 k hk₁ hk₂⟩ o =
          Φ u (fun i j => ∑ k : Fin 3, o i k * r k j))

theorem mulArr_assoc (o a b : Fin 3 → Fin 3 → ℝ) : mulArr (mulArr o a) b = mulArr o (mulArr a b) := by
  funext i j
  simp only [mulArr, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

include hΦ in

theorem phi_add {c₁ c₂ : Fin 3} (h : IsPlane c₁ c₂) (v : ↥X) {o : Fin 3 → Fin 3 → ℝ} (ho : ColOrth o) (s t : ℝ) :
    phi hK Φ c₁ c₂ h.ne v o (s + t) = phi hK Φ c₁ c₂ h.ne v (mulArr o (rotArr c₁ c₂ s)) t := by
  rw [phi_eq hK Φ hΦ c₁ c₂ h.ne v ho, phi_eq hK Φ hΦ c₁ c₂ h.ne v (colOrth_mulArr ho (colOrth_rotArr h.ne s)),
    rotArr_add h, mulArr_assoc]

include hfin hsm hΦ in

theorem hasDerivAt_phi {c₁ c₂ : Fin 3} (h : IsPlane c₁ c₂) (v : ↥X) {o : Fin 3 → Fin 3 → ℝ} (ho : ColOrth o) (s : ℝ) :
    HasDerivAt (phi hK Φ c₁ c₂ h.ne v o) (phi hK Φ c₁ c₂ h.ne (Lx hD c₁ c₂ v) o s) s := by
  have h0 := hasDerivAt_phi_zero hD hK hfin hsm Φ c₁ c₂ h.ne v (mulArr o (rotArr c₁ c₂ s))

  have hshift : (fun t => phi hK Φ c₁ c₂ h.ne v o (s + t)) = phi hK Φ c₁ c₂ h.ne v (mulArr o (rotArr c₁ c₂ s)) := by
    funext t; exact phi_add hK Φ hΦ h v ho s t
  rw [← hshift] at h0
  have hg : HasDerivAt (fun t => phi hK Φ c₁ c₂ h.ne v o (s + t)) (Φ (Lx hD c₁ c₂ v) (mulArr o (rotArr c₁ c₂ s)))
      (-s + s) := by rw [neg_add_cancel]; exact h0
  have h1 := hg.comp_const_add (-s) s
  have hfun : (fun x => phi hK Φ c₁ c₂ h.ne v o (s + (-s + x))) = phi hK Φ c₁ c₂ h.ne v o := by
    funext x; congr 1; ring
  rw [hfun] at h1
  rw [phi_eq hK Φ hΦ c₁ c₂ h.ne (Lx hD c₁ c₂ v) ho s]
  exact h1

include hfin hsm hΦ in

theorem d2_eq {c₁ c₂ : Fin 3} (h : IsPlane c₁ c₂) (x : ↥X) {o : Fin 3 → Fin 3 → ℝ} (ho : ColOrth o) :
    d2 (Φ x) c₁ c₂ o = Φ (Lx hD c₁ c₂ (Lx hD c₁ c₂ x)) o := by
  have hderiv : ∀ v : ↥X, deriv (phi hK Φ c₁ c₂ h.ne v o) = phi hK Φ c₁ c₂ h.ne (Lx hD c₁ c₂ v) o := fun v => by
    funext s; exact (hasDerivAt_phi hD hK hfin hsm Φ hΦ h v ho s).deriv
  have hfun : (fun s : ℝ => Φ x (mulA o (rotArr c₁ c₂ s))) = phi hK Φ c₁ c₂ h.ne x o := by
    funext s; exact (phi_eq hK Φ hΦ c₁ c₂ h.ne x ho s).symm
  show deriv (deriv (fun s : ℝ => Φ x (mulA o (rotArr c₁ c₂ s)))) 0 = _
  rw [hfun, hderiv x, hderiv (Lx hD c₁ c₂ x)]

  show Φ (Rx hK c₁ c₂ h.ne 0 (Lx hD c₁ c₂ (Lx hD c₁ c₂ x))) o = _
  have hR0 : Rx hK c₁ c₂ h.ne 0 (Lx hD c₁ c₂ (Lx hD c₁ c₂ x)) = Lx hD c₁ c₂ (Lx hD c₁ c₂ x) := by
    apply Subtype.ext
    funext g
    show ((Lx hD c₁ c₂ (Lx hD c₁ c₂ x)) : Fn) (g * WhittakerBlock.archRealLift3 (rotArr c₁ c₂ 0)) = _
    rw [rotArr_zero c₁ c₂ h.ne, lift_one', mul_one]
  rw [hR0]

theorem Lx_Lx_eq (c₁ c₂ : Fin 3) (x : ↥X) :
    ((Lx hD c₁ c₂ (Lx hD c₁ c₂ x)) : Fn) =
      WhittakerBlock.archDeriv c₁ c₂ (WhittakerBlock.archDeriv c₁ c₂ (x : Fn) - WhittakerBlock.archDeriv c₂ c₁ (x : Fn)) -
        WhittakerBlock.archDeriv c₂ c₁ (WhittakerBlock.archDeriv c₁ c₂ (x : Fn) - WhittakerBlock.archDeriv c₂ c₁ (x : Fn)) := by
  have hL : ((Lx hD c₁ c₂ x) : Fn) =
      (-1 : ℂ) • (WhittakerBlock.archDeriv c₁ c₂ (x : Fn) - WhittakerBlock.archDeriv c₂ c₁ (x : Fn)) := by
    funext g
    show WhittakerBlock.archDeriv c₂ c₁ (x : Fn) g - WhittakerBlock.archDeriv c₁ c₂ (x : Fn) g = _
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  have hsmul := (WhittakerBlock.isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate).2.2.1
  funext g
  show WhittakerBlock.archDeriv c₂ c₁ ((Lx hD c₁ c₂ x) : Fn) g - WhittakerBlock.archDeriv c₁ c₂ ((Lx hD c₁ c₂ x) : Fn) g = _
  rw [hL, hsmul, hsmul]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

end Transport

theorem transport
    {X : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)}
    (hD : ∀ w ∈ X, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ X)
    (hK : ∀ w ∈ X, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ X)
    (hfin : ∀ w ∈ X, ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (hcont : ∀ w ∈ X, Continuous w) (hsm : ∀ w ∈ X, WhittakerBlock.IsArchSmooth3 w)
    (Φ : ↥X →ₗ[ℂ] ((Fin 3 → Fin 3 → ℝ) → ℂ))
    (hΦ : ∀ (u : ↥X) (r : Fin 3 → Fin 3 → ℝ) (hr : (∀ i j : Fin 3, ∑ a : Fin 3, r a i * r a j = if i = j then 1 else 0))
            (k : AdelicGL 3 (𝓞 ℚ) ℚ) (hk₁ : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1)
            (hk₂ : archComponent3 (𝓞 ℚ) ℚ k ∈ orth3),
            k = WhittakerBlock.archRealLift3 r →
            ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
              Φ ⟨fun g => (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g * k), hK u u.2 k hk₁ hk₂⟩ o =
                Φ u (fun i j => ∑ k : Fin 3, o i k * r k j))
    (x : ↥X) (o : Fin 3 → Fin 3 → ℝ) (ho : ∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) :
    Φ ⟨WsE.IP.Om (x : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), WsE.IP.Om_mem hD x.2⟩ o = RotCas.rotCas (Φ x) o := by
  have h01 : IsPlane 0 1 := Or.inl ⟨rfl, rfl⟩
  have h02 : IsPlane 0 2 := Or.inr (Or.inl ⟨rfl, rfl⟩)
  have h12 : IsPlane 1 2 := Or.inr (Or.inr ⟨rfl, rfl⟩)
  have hOm : (⟨WsE.IP.Om (x : Fn), WsE.IP.Om_mem hD x.2⟩ : ↥X) =
      Lx hD 0 1 (Lx hD 0 1 x) + Lx hD 0 2 (Lx hD 0 2 x) + Lx hD 1 2 (Lx hD 1 2 x) := by
    apply Subtype.ext
    show WsE.IP.Om (x : Fn) = ((Lx hD 0 1 (Lx hD 0 1 x)) : Fn) + ((Lx hD 0 2 (Lx hD 0 2 x)) : Fn) +
      ((Lx hD 1 2 (Lx hD 1 2 x)) : Fn)
    rw [Lx_Lx_eq, Lx_Lx_eq, Lx_Lx_eq]
    rfl
  rw [hOm, map_add, map_add, Pi.add_apply, Pi.add_apply]
  show _ = d2 (Φ x) 0 1 o + d2 (Φ x) 0 2 o + d2 (Φ x) 1 2 o
  rw [d2_eq hD hK hfin hsm Φ hΦ h01 x ho, d2_eq hD hK hfin hsm Φ hΦ h02 x ho, d2_eq hD hK hfin hsm Φ hΦ h12 x ho]

end

end WsA

set_option autoImplicit false

noncomputable section
p2m_open "Module Module.End"

namespace EigenProj

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem isInternal_eigenspace (T : V →ₗ[ℂ] V) (h : ⨆ μ : ℂ, Module.End.eigenspace T μ = ⊤) :
    DirectSum.IsInternal (fun μ : ℂ => Module.End.eigenspace T μ) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2 ⟨Module.End.eigenspaces_iSupIndep T, h⟩

private def _root_.EigenProj.proj (T : V →ₗ[ℂ] V) (h : ⨆ μ : ℂ, Module.End.eigenspace T μ = ⊤) (μ : ℂ) : V →ₗ[ℂ] V := by
  classical
  exact (Module.End.eigenspace T μ).subtype ∘ₗ
    (DirectSum.component ℂ ℂ (fun ν : ℂ => ↥(Module.End.eigenspace T ν)) μ) ∘ₗ
      ((LinearEquiv.ofBijective (DirectSum.coeLinearMap fun ν : ℂ => Module.End.eigenspace T ν)
        (isInternal_eigenspace T h)).symm : V →ₗ[ℂ] _)

p2m_export "EigenProj" "proj"
private theorem _root_.EigenProj.proj_mem (T : V →ₗ[ℂ] V) (h : ⨆ μ : ℂ, Module.End.eigenspace T μ = ⊤) (μ : ℂ) (v : V) :
    proj T h μ v ∈ Module.End.eigenspace T μ := by
  classical
  unfold proj
  simp only [LinearMap.coe_comp, Function.comp_apply]
  exact Submodule.coe_mem _

p2m_export "EigenProj" "proj_mem"
private theorem _root_.EigenProj.proj_apply_of_mem (T : V →ₗ[ℂ] V) (h : ⨆ μ : ℂ, Module.End.eigenspace T μ = ⊤) (μ ν : ℂ) (v : V)
    (hv : v ∈ Module.End.eigenspace T ν) :
    proj T h μ v = if μ = ν then v else 0 := by
  classical
  unfold proj
  set e := LinearEquiv.ofBijective (DirectSum.coeLinearMap fun ν : ℂ => Module.End.eigenspace T ν)
        (isInternal_eigenspace T h) with he
  have hsymm : e.symm v = DirectSum.lof ℂ ℂ (fun ν : ℂ => ↥(Module.End.eigenspace T ν)) ν ⟨v, hv⟩ := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    show v = DirectSum.coeLinearMap (fun ν : ℂ => Module.End.eigenspace T ν) (DirectSum.lof ℂ ℂ _ ν ⟨v, hv⟩)
    rw [DirectSum.lof_eq_of, DirectSum.coeLinearMap_of]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [hsymm, DirectSum.component.of]
  by_cases hμν : μ = ν
  · subst hμν
    simp
  · rw [if_neg hμν, dif_neg (Ne.symm hμν)]
    simp

p2m_export "EigenProj" "proj_apply_of_mem"
theorem proj_apply_self (T : V →ₗ[ℂ] V) (h : ⨆ μ : ℂ, Module.End.eigenspace T μ = ⊤) (μ : ℂ) (v : V)
    (hv : v ∈ Module.End.eigenspace T μ) : proj T h μ v = v := by
  rw [proj_apply_of_mem T h μ μ v hv, if_pos rfl]

theorem proj_apply_other (T : V →ₗ[ℂ] V) (h : ⨆ μ : ℂ, Module.End.eigenspace T μ = ⊤) {μ ν : ℂ} (hne : μ ≠ ν)
    (v : V) (hv : v ∈ Module.End.eigenspace T ν) : proj T h μ v = 0 := by
  rw [proj_apply_of_mem T h μ ν v hv, if_neg hne]

private theorem _root_.EigenProj.proj_idem (T : V →ₗ[ℂ] V) (h : ⨆ μ : ℂ, Module.End.eigenspace T μ = ⊤) (μ : ℂ) (v : V) :
    proj T h μ (proj T h μ v) = proj T h μ v :=
  proj_apply_self T h μ _ (proj_mem T h μ v)

p2m_export "EigenProj" "proj_idem"
private theorem _root_.EigenProj.apply_proj (T : V →ₗ[ℂ] V) (h : ⨆ μ : ℂ, Module.End.eigenspace T μ = ⊤) (μ : ℂ) (v : V) :
    T (proj T h μ v) = μ • proj T h μ v :=
  Module.End.mem_eigenspace_iff.1 (proj_mem T h μ v)

p2m_export "EigenProj" "apply_proj"

private theorem _root_.EigenProj.proj_mem_of_mem (T : V →ₗ[ℂ] V) (h : ⨆ μ : ℂ, Module.End.eigenspace T μ = ⊤) (μ : ℂ)
    (W : Submodule ℂ V) (hW : ∀ w ∈ W, w ∈ ⨆ ν : ℂ, (W ⊓ Module.End.eigenspace T ν)) (v : V) (hv : v ∈ W) :
    proj T h μ v ∈ W := by
  classical
  have hv' := hW v hv
  rw [Submodule.mem_iSup_iff_exists_finsupp] at hv'
  obtain ⟨f, hf, rfl⟩ := hv'
  show proj T h μ (∑ ν ∈ f.support, f ν) ∈ W
  rw [map_sum]
  refine Submodule.sum_mem _ (fun ν _ => ?_)
  obtain ⟨hW', hE⟩ := Submodule.mem_inf.1 (hf ν)
  rw [proj_apply_of_mem T h μ ν _ hE]
  split_ifs
  · exact hW'
  · exact W.zero_mem

p2m_export "EigenProj" "proj_mem_of_mem"
end EigenProj

set_option autoImplicit false

noncomputable section
p2m_open "Module Module.End"
open scoped ComplexConjugate

namespace SymmDiag

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem mem_iSup_inf_eigenspace (T : V →ₗ[ℂ] V) (W : Submodule ℂ V) [FiniteDimensional ℂ W]
    (hT : ∀ w ∈ W, T w ∈ W)
    (B : V → V → ℂ)
    (hBlin : ∀ (z : ℂ) (w₁ w₂ w' : V), w₁ ∈ W → w₂ ∈ W → w' ∈ W → B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hBsymm : ∀ w ∈ W, ∀ w' ∈ W, B w' w = conj (B w w'))
    (hBpos : ∀ w ∈ W, w ≠ 0 → 0 < (B w w).re)
    (hTsymm : ∀ w ∈ W, ∀ w' ∈ W, B (T w) w' = B w (T w')) :
    ∀ w ∈ W, w ∈ ⨆ μ : ℂ, (W ⊓ Module.End.eigenspace T μ) := by
  classical

  have hBadd : ∀ w₁ w₂ w' : V, w₁ ∈ W → w₂ ∈ W → w' ∈ W → B (w₁ + w₂) w' = B w₁ w' + B w₂ w' := by
    intro w₁ w₂ w' h₁ h₂ h'
    have := hBlin 1 w₁ w₂ w' h₁ h₂ h'
    rwa [one_smul, one_mul] at this
  have hBsmul : ∀ (z : ℂ) (w w' : V), w ∈ W → w' ∈ W → B (z • w) w' = z * B w w' := by
    intro z w w' h h'
    have := hBlin z w 0 w' h W.zero_mem h'
    have h0 : B 0 w' = 0 := by
      have := hBlin 1 0 0 w' W.zero_mem W.zero_mem h'
      rw [one_smul, add_zero, one_mul] at this
      linear_combination -this
    rwa [add_zero, h0, add_zero] at this

  let core : InnerProductSpace.Core ℂ W :=
    { inner := fun x y => B (y : V) (x : V)
      conj_inner_symm := fun x y => (hBsymm _ x.2 _ y.2).symm
      re_inner_nonneg := fun x => by
        by_cases hx : (x : V) = 0
        · show 0 ≤ (B (x : V) (x : V)).re
          rw [hx]
          have := hBsmul 0 0 0 W.zero_mem W.zero_mem
          rw [zero_smul, zero_mul] at this
          rw [this]; simp
        · exact (hBpos _ x.2 hx).le
      add_left := fun x y z => by
        show B (z : V) ((x : V) + y) = B z x + B z y
        rw [hBsymm _ (W.add_mem x.2 y.2) _ z.2, hBadd _ _ _ x.2 y.2 z.2, map_add, ← hBsymm _ x.2 _ z.2,
          ← hBsymm _ y.2 _ z.2]
      smul_left := fun x y r => by
        show B (y : V) (r • (x : V)) = conj r * B y x
        rw [hBsymm _ (W.smul_mem r x.2) _ y.2, hBsmul r _ _ x.2 y.2, map_mul, ← hBsymm _ x.2 _ y.2]
      definite := fun x hx => by
        by_contra hne
        have hne' : (x : V) ≠ 0 := fun h => hne (Subtype.ext h)
        have := hBpos _ x.2 hne'
        change B (x : V) (x : V) = 0 at hx
        rw [hx] at this; simp at this }
  letI : NormedAddCommGroup W := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ W := InnerProductSpace.ofCore core.toCore

  let T' : W →ₗ[ℂ] W := T.restrict (p := W) (q := W) (fun w hw => hT w hw)
  have hT' : T'.IsSymmetric := by
    intro x y
    show B ((y : V)) (T (x : V)) = B (T (y : V)) (x : V)
    rw [hBsymm _ (hT _ x.2) _ y.2, hBsymm _ x.2 _ (hT _ y.2), hTsymm _ x.2 _ y.2]
  have htop : ⨆ μ : ℂ, Module.End.eigenspace T' μ = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff]
    exact hT'.orthogonalComplement_iSup_eigenspaces_eq_bot

  intro w hw
  have hmem : (⟨w, hw⟩ : W) ∈ ⨆ μ : ℂ, Module.End.eigenspace T' μ := by rw [htop]; exact Submodule.mem_top
  have hmap : Submodule.map W.subtype (⨆ μ : ℂ, Module.End.eigenspace T' μ) ≤ ⨆ μ : ℂ, (W ⊓ Module.End.eigenspace T μ) := by
    rw [Submodule.map_iSup]
    refine iSup_mono fun μ => ?_
    rintro v ⟨x, hx, rfl⟩
    refine Submodule.mem_inf.2 ⟨x.2, ?_⟩
    have hx' : T' x = μ • x := Module.End.mem_eigenspace_iff.1 hx
    apply Module.End.mem_eigenspace_iff.2
    have := congrArg (fun y : W => (y : V)) hx'
    simpa [T'] using this
  exact hmap ⟨⟨w, hw⟩, hmem, rfl⟩

end SymmDiag

set_option autoImplicit false

noncomputable section
p2m_open "Module Module.End"
open scoped ComplexConjugate

namespace AbsIso

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

structure Setup (T : V →ₗ[ℂ] V) (B : V → V → ℂ) : Prop where
  lin : ∀ (z : ℂ) (w₁ w₂ w' : V), B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w'
  symm : ∀ w w' : V, B w' w = conj (B w w')
  pos : ∀ w : V, w ≠ 0 → 0 < (B w w).re
  tsymm : ∀ w w' : V, B (T w) w' = B w (T w')
  locfin : ∀ v : V, ∃ W : Submodule ℂ V, v ∈ W ∧ FiniteDimensional ℂ W ∧ ∀ w ∈ W, T w ∈ W

variable {T : V →ₗ[ℂ] V} {B : V → V → ℂ}

theorem Setup.mem_iSup_inf (h : Setup T B) (W : Submodule ℂ V) [FiniteDimensional ℂ W] (hW : ∀ w ∈ W, T w ∈ W) :
    ∀ w ∈ W, w ∈ ⨆ μ : ℂ, (W ⊓ eigenspace T μ) :=
  SymmDiag.mem_iSup_inf_eigenspace T W hW B (fun z w₁ w₂ w' _ _ _ => h.lin z w₁ w₂ w')
    (fun w _ w' _ => h.symm w w') (fun w _ hw => h.pos w hw) (fun w _ w' _ => h.tsymm w w')

theorem Setup.iSup_eq_top (h : Setup T B) : ⨆ μ : ℂ, eigenspace T μ = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨W, hv, hfd, hW⟩ := h.locfin v
  haveI := hfd
  have hmem := h.mem_iSup_inf W hW v hv
  exact (iSup_mono (fun μ => (inf_le_right : W ⊓ eigenspace T μ ≤ eigenspace T μ))) hmem

def Setup.proj (h : Setup T B) (μ : ℂ) : V →ₗ[ℂ] V := EigenProj.proj T h.iSup_eq_top μ

theorem Setup.proj_idem (h : Setup T B) (μ : ℂ) (v : V) : h.proj μ (h.proj μ v) = h.proj μ v :=
  EigenProj.proj_idem T _ μ v

theorem Setup.apply_proj (h : Setup T B) (μ : ℂ) (v : V) : T (h.proj μ v) = μ • h.proj μ v :=
  EigenProj.apply_proj T _ μ v

theorem Setup.proj_mem (h : Setup T B) (μ : ℂ) (v : V) : h.proj μ v ∈ eigenspace T μ :=
  EigenProj.proj_mem T _ μ v

theorem Setup.proj_apply_of_mem (h : Setup T B) (μ ν : ℂ) (v : V) (hv : v ∈ eigenspace T ν) :
    h.proj μ v = if μ = ν then v else 0 :=
  EigenProj.proj_apply_of_mem T _ μ ν v hv

theorem Setup.proj_mem_of_mem (h : Setup T B) (μ : ℂ) (W : Submodule ℂ V) [FiniteDimensional ℂ W]
    (hW : ∀ w ∈ W, T w ∈ W) (v : V) (hv : v ∈ W) : h.proj μ v ∈ W :=
  EigenProj.proj_mem_of_mem T _ μ W (h.mem_iSup_inf W hW) v hv

theorem Setup.add_right (h : Setup T B) (w w₁ w₂ : V) : B w (w₁ + w₂) = B w w₁ + B w w₂ := by
  have := h.lin 1 w₁ w₂ w
  rw [one_smul, one_mul] at this
  rw [h.symm (w₁ + w₂) w, this, map_add, ← h.symm, ← h.symm]

theorem Setup.zero_left (h : Setup T B) (w : V) : B 0 w = 0 := by
  have := h.lin 1 0 0 w
  rw [one_smul, add_zero, one_mul] at this
  linear_combination -this

theorem Setup.zero_right (h : Setup T B) (w : V) : B w 0 = 0 := by
  rw [h.symm, h.zero_left, map_zero]

theorem Setup.smul_left (h : Setup T B) (z : ℂ) (w w' : V) : B (z • w) w' = z * B w w' := by
  have := h.lin z w 0 w'
  rwa [add_zero, h.zero_left, add_zero] at this

theorem Setup.smul_right (h : Setup T B) (z : ℂ) (w w' : V) : B w (z • w') = conj z * B w w' := by
  rw [h.symm, h.smul_left, map_mul, ← h.symm]

theorem Setup.add_left (h : Setup T B) (w₁ w₂ w : V) : B (w₁ + w₂) w = B w₁ w + B w₂ w := by
  have := h.lin 1 w₁ w₂ w
  rwa [one_smul, one_mul] at this

theorem Setup.sum_left (h : Setup T B) {ι : Type*} (s : Finset ι) (f : ι → V) (w : V) :
    B (∑ i ∈ s, f i) w = ∑ i ∈ s, B (f i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h.zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.add_left, ih]

theorem Setup.sum_right (h : Setup T B) {ι : Type*} (s : Finset ι) (f : ι → V) (w : V) :
    B w (∑ i ∈ s, f i) = ∑ i ∈ s, B w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h.zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.add_right, ih]

theorem Setup.conj_eq_of_mem (h : Setup T B) {μ : ℂ} {v : V} (hv : v ∈ eigenspace T μ) (hv0 : v ≠ 0) :
    conj μ = μ := by
  have h1 : B (T v) v = μ * B v v := by rw [mem_eigenspace_iff.1 hv, h.smul_left]
  have h2 : B v (T v) = conj μ * B v v := by rw [mem_eigenspace_iff.1 hv, h.smul_right]
  have hne : B v v ≠ 0 := by
    intro h0; have := h.pos v hv0; rw [h0] at this; simp at this
  have := h.tsymm v v
  rw [h1, h2] at this
  exact (mul_right_cancel₀ hne this).symm

theorem Setup.orth (h : Setup T B) {μ ν : ℂ} (hne : μ ≠ ν) {v w : V} (hv : v ∈ eigenspace T μ)
    (hw : w ∈ eigenspace T ν) : B v w = 0 := by
  by_cases hv0 : v = 0
  · rw [hv0, h.zero_left]
  by_cases hw0 : w = 0
  · rw [hw0, h.zero_right]
  have h1 : B (T v) w = μ * B v w := by rw [mem_eigenspace_iff.1 hv, h.smul_left]
  have h2 : B v (T w) = ν * B v w := by rw [mem_eigenspace_iff.1 hw, h.smul_right, h.conj_eq_of_mem hw hw0]
  have := h.tsymm v w
  rw [h1, h2] at this
  by_contra hb
  exact hne (mul_right_cancel₀ hb this)

theorem Setup.exists_decomp (h : Setup T B) (W : Submodule ℂ V) [FiniteDimensional ℂ W]
    (hW : ∀ w ∈ W, T w ∈ W) (v : V) (hv : v ∈ W) :
    ∃ f : ℂ →₀ V, (∀ ν, f ν ∈ W ⊓ eigenspace T ν) ∧ (f.sum fun _ x => x) = v ∧
      ∀ μ, h.proj μ v = f μ := by
  classical
  have := h.mem_iSup_inf W hW v hv
  rw [Submodule.mem_iSup_iff_exists_finsupp] at this
  obtain ⟨f, hf, hsum⟩ := this
  refine ⟨f, hf, hsum, fun μ => ?_⟩
  rw [← hsum]
  show h.proj μ (∑ ν ∈ f.support, f ν) = f μ
  rw [map_sum]
  have hterm : ∀ ν, h.proj μ (f ν) = if μ = ν then f ν else 0 := fun ν =>
    h.proj_apply_of_mem μ ν (f ν) (Submodule.mem_inf.1 (hf ν)).2
  simp_rw [hterm]
  by_cases hμ : μ ∈ f.support
  · rw [Finset.sum_eq_single_of_mem μ hμ (fun ν _ hν => by rw [if_neg (Ne.symm hν)])]
    simp
  · rw [Finset.sum_eq_zero (fun ν hν => by
      rw [if_neg]
      rintro rfl
      exact hμ hν)]
    exact (Finsupp.notMem_support_iff.1 hμ).symm

theorem Setup.exists_common (h : Setup T B) (v w : V) :
    ∃ W : Submodule ℂ V, v ∈ W ∧ w ∈ W ∧ FiniteDimensional ℂ W ∧ ∀ x ∈ W, T x ∈ W := by
  obtain ⟨W₁, hv, hfd₁, hW₁⟩ := h.locfin v
  obtain ⟨W₂, hw, hfd₂, hW₂⟩ := h.locfin w
  haveI := hfd₁; haveI := hfd₂
  refine ⟨W₁ ⊔ W₂, Submodule.mem_sup_left hv, Submodule.mem_sup_right hw, inferInstance, ?_⟩
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (hW₁ y hy)) (Submodule.mem_sup_right (hW₂ z hz))

theorem Setup.proj_selfadjoint (h : Setup T B) (μ : ℂ) (v w : V) :
    B (h.proj μ v) w = B v (h.proj μ w) := by
  classical
  obtain ⟨W, hv, hw, hfd, hW⟩ := h.exists_common v w
  haveI := hfd
  obtain ⟨f, hf, hfs, hfp⟩ := h.exists_decomp W hW v hv
  obtain ⟨g, hg, hgs, hgp⟩ := h.exists_decomp W hW w hw
  have hv' : v = ∑ ν ∈ f.support, f ν := hfs.symm
  have hw' : w = ∑ ν ∈ g.support, g ν := hgs.symm
  rw [hfp, hgp]
  conv_lhs => rw [hw', h.sum_right]
  conv_rhs => rw [hv', h.sum_left]
  have hL : ∀ ν ∈ g.support, B (f μ) (g ν) = if ν = μ then B (f μ) (g μ) else 0 := by
    intro ν _
    by_cases hν : ν = μ
    · subst hν; simp
    · rw [if_neg hν]
      exact h.orth (Ne.symm hν) (Submodule.mem_inf.1 (hf μ)).2 (Submodule.mem_inf.1 (hg ν)).2
  have hR : ∀ ν ∈ f.support, B (f ν) (g μ) = if ν = μ then B (f μ) (g μ) else 0 := by
    intro ν _
    by_cases hν : ν = μ
    · subst hν; simp
    · rw [if_neg hν]
      exact h.orth hν (Submodule.mem_inf.1 (hf ν)).2 (Submodule.mem_inf.1 (hg μ)).2
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR, Finset.sum_ite_eq', Finset.sum_ite_eq']
  by_cases hgμ : μ ∈ g.support <;> by_cases hfμ : μ ∈ f.support <;> simp only [hgμ, hfμ, if_true, if_false]
  · rw [Finsupp.notMem_support_iff.1 hfμ, h.zero_left]
  · rw [Finsupp.notMem_support_iff.1 hgμ, h.zero_right]

end AbsIso

set_option autoImplicit false

namespace Vand

open Polynomial

theorem eq_zero_of_powersum {S : Finset ℂ} (a : ℂ → ℂ) (μ₀ : ℂ)
    (h : ∀ n : ℕ, ∑ ν ∈ S, ν ^ n * a ν = μ₀ ^ n * ∑ ν ∈ S, a ν) :
    ∀ ν ∈ S, ν ≠ μ₀ → a ν = 0 := by
  classical
  intro ν₀ hν₀ hne

  let p : ℂ[X] := (X - C μ₀) * ∏ ν ∈ S.erase ν₀, (X - C ν)

  have key : ∀ x : ℂ, p.eval x = ∑ n ∈ Finset.range (p.natDegree + 1), p.coeff n * x ^ n := fun x =>
    Polynomial.eval_eq_sum_range x
  have hsum : ∑ ν ∈ S, p.eval ν * a ν = p.eval μ₀ * ∑ ν ∈ S, a ν := by
    simp_rw [key]
    rw [Finset.sum_mul]
    have : ∀ ν ∈ S, (∑ n ∈ Finset.range (p.natDegree + 1), p.coeff n * ν ^ n) * a ν =
        ∑ n ∈ Finset.range (p.natDegree + 1), p.coeff n * (ν ^ n * a ν) := by
      intro ν _; rw [Finset.sum_mul]; simp_rw [mul_assoc]
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.mul_sum, h n, mul_assoc]
  have hμ : p.eval μ₀ = 0 := by simp [p]
  rw [hμ, zero_mul] at hsum

  have hvan : ∀ ν ∈ S, ν ≠ ν₀ → p.eval ν = 0 := by
    intro ν hν hνne
    simp only [p, eval_mul, eval_prod, eval_sub, eval_X, eval_C]
    apply mul_eq_zero_of_right
    exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hνne, hν⟩) (sub_self ν)
  rw [Finset.sum_eq_single_of_mem ν₀ hν₀ (fun ν hν hνne => by rw [hvan ν hν hνne, zero_mul])] at hsum
  have hp0 : p.eval ν₀ ≠ 0 := by
    simp only [p, eval_mul, eval_prod, eval_sub, eval_X, eval_C]
    refine mul_ne_zero (sub_ne_zero.2 hne) ?_
    rw [Finset.prod_ne_zero_iff]
    intro ν hν
    exact sub_ne_zero.2 (Ne.symm (Finset.mem_erase.1 hν).1)
  exact (mul_eq_zero.1 hsum).resolve_left hp0

end Vand

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

noncomputable section

namespace IsoMain

p2m_open "P2MW.S_LanglandsTunnell_CubicInduction_exists_isotypicProjector_natural_of_orthFinite_of_derivStable.WsE.IP Module Module.End"

section
variable {X : Submodule ℂ Fn}
  (hD : ∀ w ∈ X, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ X)
  (hsm : ∀ w ∈ X, WhittakerBlock.IsArchSmooth3 w)

def Dl (i j : Fin 3) : ↥X →ₗ[ℂ] ↥X where
  toFun v := ⟨WhittakerBlock.archDeriv i j v, hD v v.2 i j⟩
  map_add' v w := Subtype.ext
    (LanglandsTunnell.CubicInduction.WhittakerBlock.isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.2.1
      _ _ (hsm v v.2) (hsm w w.2) i j)
  map_smul' c v := Subtype.ext
    (LanglandsTunnell.CubicInduction.WhittakerBlock.isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.2.2.1
      c _ i j)

@[scoped simp] theorem coe_Dl (i j : Fin 3) (v : ↥X) : ((Dl hD hsm i j v : ↥X) : Fn) = WhittakerBlock.archDeriv i j v := rfl

def Oml : ↥X →ₗ[ℂ] ↥X :=
  ((Dl hD hsm 0 1).comp (Dl hD hsm 0 1 - Dl hD hsm 1 0) - (Dl hD hsm 1 0).comp (Dl hD hsm 0 1 - Dl hD hsm 1 0)) +
  ((Dl hD hsm 0 2).comp (Dl hD hsm 0 2 - Dl hD hsm 2 0) - (Dl hD hsm 2 0).comp (Dl hD hsm 0 2 - Dl hD hsm 2 0)) +
  ((Dl hD hsm 1 2).comp (Dl hD hsm 1 2 - Dl hD hsm 2 1) - (Dl hD hsm 2 1).comp (Dl hD hsm 1 2 - Dl hD hsm 2 1))

theorem coe_Oml (v : ↥X) : ((Oml hD hsm v : ↥X) : Fn) = Om (v : Fn) := rfl

end

end IsoMain
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_isotypicProjector_natural_of_orthFinite_of_derivStable.IsoMain"

open IsoMain WsE.IP Module _root_.Module.End in
theorem solution
    (X : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))
    (hD : (∀ w ∈ X, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ X))
    (hK : (∀ w ∈ X, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ X))
    (hfin : ∀ w ∈ X, ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (hcont : ∀ w ∈ X, Continuous w) (hsm : ∀ w ∈ X, WhittakerBlock.IsArchSmooth3 w)
    (B : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ℂ)
    (hB : (∀ w ∈ X, ∀ w' ∈ X, B w' w = (starRingEnd ℂ) (B w w')) ∧
        (∀ (z : ℂ), ∀ w₁ ∈ X, ∀ w₂ ∈ X, ∀ w' ∈ X, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w') ∧
        (∀ w ∈ X, w ≠ 0 → 0 < (B w w).re) ∧
        (∀ w ∈ X, ∀ w' ∈ X, ∀ i j : Fin 3,
          B (WhittakerBlock.archDeriv i j w) w' = - B w (WhittakerBlock.archDeriv i j w')) ∧
        ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            ∀ w ∈ X, ∀ w' ∈ X, B (fun g => w (g * k)) (fun g => w' (g * k)) = B w w')
    (a : ℕ) (ha : a = 0 ∨ a = 1) (ℓ : ℕ) (hℓ : ℓ = 0 ∨ ℓ = 1) :
    ∃ P : ↥X →ₗ[ℂ] ↥X,
      (∀ u : ↥X, ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∈
        Submodule.span ℂ {w | ∃ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) ∧ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
            w = fun g => (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g * k)}) ∧
      (∀ u : ↥X, P (P u) = P u) ∧
      (∀ u w : ↥X, B (P u) w = B u (P w)) ∧
      (∀ (Φ : ↥X →ₗ[ℂ] ((Fin 3 → Fin 3 → ℝ) → ℂ)),
        (∀ (u : ↥X) (r : Fin 3 → Fin 3 → ℝ) (hr : (∀ i j : Fin 3, ∑ a : Fin 3, r a i * r a j = if i = j then 1 else 0))
            (k : AdelicGL 3 (𝓞 ℚ) ℚ) (hk₁ : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1)
            (hk₂ : archComponent3 (𝓞 ℚ) ℚ k ∈ orth3),
            k = WhittakerBlock.archRealLift3 r →
            ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
              Φ ⟨fun g => (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g * k), hK u u.2 k hk₁ hk₂⟩ o =
                Φ u (fun i j => ∑ k : Fin 3, o i k * r k j)) →
        (∀ u : ↥X,
          ((ℓ = 0 ∧ (∀ o r : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → (∀ i j : Fin 3, ∑ a : Fin 3, r a i * r a j = if i = j then 1 else 0) →
            Φ u (fun i j => ∑ k : Fin 3, o i k * r k j) = (Matrix.of fun i j : Fin 3 => ((r i j : ℝ) : ℂ)).det ^ a * Φ u o)) ∨
           (ℓ = 1 ∧ (∃ c : Fin 3 → Fin 3 → ℂ, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
            Φ u o = (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ a * ∑ i : Fin 3, ∑ j : Fin 3, c i j * ((o i j : ℝ) : ℂ)))) →
          ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → Φ (P u) o = Φ u o)) ∧
      (∀ u : ↥X, ((ℓ = 0 ∧ ∀ i j : Fin 3, WhittakerBlock.archDeriv i j ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) - WhittakerBlock.archDeriv j i ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = 0) ∨
           (ℓ = 1 ∧ (WhittakerBlock.archDeriv 0 1 (WhittakerBlock.archDeriv 0 1 ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) - WhittakerBlock.archDeriv 1 0 ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) - WhittakerBlock.archDeriv 1 0 (WhittakerBlock.archDeriv 0 1 ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) - WhittakerBlock.archDeriv 1 0 ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) +
            (WhittakerBlock.archDeriv 0 2 (WhittakerBlock.archDeriv 0 2 ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) - WhittakerBlock.archDeriv 2 0 ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) - WhittakerBlock.archDeriv 2 0 (WhittakerBlock.archDeriv 0 2 ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) - WhittakerBlock.archDeriv 2 0 ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) +
            (WhittakerBlock.archDeriv 1 2 (WhittakerBlock.archDeriv 1 2 ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) - WhittakerBlock.archDeriv 2 1 ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) - WhittakerBlock.archDeriv 2 1 (WhittakerBlock.archDeriv 1 2 ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) - WhittakerBlock.archDeriv 2 1 ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) + (2 : ℂ) • ((P u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = 0))) := by
  classical
  obtain ⟨hB1, hB2, hB3, hB4, hB5⟩ := hB

  let T : ↥X →ₗ[ℂ] ↥X := Oml hD hsm
  let Bv : ↥X → ↥X → ℂ := fun v w => B v w
  have hset : AbsIso.Setup T Bv :=
    { lin := fun z w₁ w₂ w' => hB2 z _ w₁.2 _ w₂.2 _ w'.2
      symm := fun w w' => hB1 _ w.2 _ w'.2
      pos := fun w hw => hB3 _ w.2 (fun h => hw (Subtype.ext h))
      tsymm := fun w w' => by
        show B ((Oml hD hsm w : ↥X) : Fn) w' = B w ((Oml hD hsm w' : ↥X) : Fn)
        rw [coe_Oml, coe_Oml]
        exact B_Om_symm hD B hB1 hB2 hB4 w.2 w'.2
      locfin := fun v => by
        refine ⟨(Vspan (v : Fn)).comap X.subtype, ?_, ?_, ?_⟩
        · exact self_mem_Vspan (v : Fn)
        · haveI := Vspan_fd hfin v.2
          exact LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe (Vspan_le hK v.2)).symm
        · intro w hw
          change ((Oml hD hsm w : ↥X) : Fn) ∈ Vspan (v : Fn)
          rw [coe_Oml]
          simp only [Om]
          refine (Vspan _).add_mem ((Vspan _).add_mem ?_ ?_) ?_ <;>
            exact rot_mem_Vspan hK hfin hsm v.2 (rot_mem_Vspan hK hfin hsm v.2 hw _ _) _ _ }

  let μ₀ : ℂ := if ℓ = 0 then 0 else -2
  refine ⟨hset.proj μ₀, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro u
    haveI := Vspan_fd hfin u.2
    haveI : FiniteDimensional ℂ ((Vspan (u : Fn)).comap X.subtype) :=
      LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe (Vspan_le hK u.2)).symm
    have hst : ∀ w ∈ (Vspan (u : Fn)).comap X.subtype, T w ∈ (Vspan (u : Fn)).comap X.subtype := by
      intro w hw
      change ((Oml hD hsm w : ↥X) : Fn) ∈ Vspan (u : Fn)
      rw [coe_Oml]
      simp only [Om]
      refine (Vspan _).add_mem ((Vspan _).add_mem ?_ ?_) ?_ <;>
        exact rot_mem_Vspan hK hfin hsm u.2 (rot_mem_Vspan hK hfin hsm u.2 hw _ _) _ _
    exact hset.proj_mem_of_mem μ₀ _ hst u (self_mem_Vspan (u : Fn))
  ·
    intro u; exact hset.proj_idem μ₀ u
  ·
    intro u w; exact hset.proj_selfadjoint μ₀ u w
  ·
    intro Φ hΦ u htype o ho

    have hT : ∀ o' : Fin 3 → Fin 3 → ℝ, ColOrth o' → RotCas.rotCas (Φ u) o' = μ₀ * Φ u o' := by
      rcases htype with ⟨hl0, hG⟩ | ⟨hl1, c, hG⟩
      · intro o' ho'
        rw [RotCas.rotCas_eq_zero_of_detType a (Φ u) (fun o r ho hr => hG o r ho hr) o' ho']
        simp [μ₀, hl0]
      · intro o' ho'
        rw [RotCas.rotCas_eq_neg_two_mul_of_stdType a c (Φ u) hG o' ho']
        simp [μ₀, hl1]

    haveI := Vspan_fd hfin u.2
    haveI : FiniteDimensional ℂ ((Vspan (u : Fn)).comap X.subtype) :=
      LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe (Vspan_le hK u.2)).symm
    have hst : ∀ w ∈ (Vspan (u : Fn)).comap X.subtype, T w ∈ (Vspan (u : Fn)).comap X.subtype := by
      intro w hw
      change ((Oml hD hsm w : ↥X) : Fn) ∈ Vspan (u : Fn)
      rw [coe_Oml]
      simp only [Om]
      refine (Vspan _).add_mem ((Vspan _).add_mem ?_ ?_) ?_ <;>
        exact rot_mem_Vspan hK hfin hsm u.2 (rot_mem_Vspan hK hfin hsm u.2 hw _ _) _ _
    obtain ⟨f, hf, hfs, hfp⟩ := hset.exists_decomp _ hst u (self_mem_Vspan (u : Fn))

    have hpow : ∀ (n : ℕ) (ν : ℂ), (T ^ n) (f ν) = ν ^ n • f ν := by
      intro n ν
      have hmem := (Submodule.mem_inf.1 (hf ν)).2
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, ih, map_smul, Module.End.mem_eigenspace_iff.1 hmem, smul_smul,
          pow_succ, mul_comm]
    have hA : ∀ n : ℕ, Φ ((T ^ n) u) o = ∑ ν ∈ f.support, ν ^ n * Φ (f ν) o := by
      intro n
      have hu : u = ∑ ν ∈ f.support, f ν := hfs.symm
      conv_lhs => rw [hu]
      rw [map_sum, map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [hpow, map_smul, Pi.smul_apply, smul_eq_mul]
    have hB : ∀ n : ℕ, ∀ o' : Fin 3 → Fin 3 → ℝ, ColOrth o' → Φ ((T ^ n) u) o' = μ₀ ^ n * Φ u o' := by
      intro n
      induction n with
      | zero => intro o' _; simp
      | succ n ih =>
        intro o' ho'
        rw [pow_succ', Module.End.mul_apply]
        have htr := WsA.transport hD hK hfin hcont hsm Φ hΦ ((T ^ n) u) o' ho'
        have hTy : T ((T ^ n) u) = ⟨Om (((T ^ n) u : ↥X) : Fn), Om_mem hD ((T ^ n) u).2⟩ :=
          Subtype.ext (coe_Oml hD hsm _)
        rw [hTy, htr, RotCas.rotCas_congr (G' := fun o'' => μ₀ ^ n * Φ u o'')
          (fun c₁ c₂ hne s => ih _ (RotCas.colOrth_mulA ho' (colOrth_rotArr hne s))),
          RotCas.rotCas_const_mul, hT o' ho', pow_succ]
        ring
    have hsumA : Φ u o = ∑ ν ∈ f.support, Φ (f ν) o := by
      have := hA 0
      simpa using this
    have hV : ∀ n : ℕ, ∑ ν ∈ f.support, ν ^ n * Φ (f ν) o = μ₀ ^ n * ∑ ν ∈ f.support, Φ (f ν) o := by
      intro n
      rw [← hA n, hB n o ho, hsumA]
    have hz := Vand.eq_zero_of_powersum (fun ν => Φ (f ν) o) μ₀ hV

    rw [hfp μ₀, hsumA]
    by_cases hμS : μ₀ ∈ f.support
    · rw [Finset.sum_eq_single_of_mem μ₀ hμS (fun ν hν hne => hz ν hν hne)]
    · rw [Finset.sum_eq_zero (fun ν hν => hz ν hν (by rintro rfl; exact hμS hν)),
        Finsupp.notMem_support_iff.1 hμS, map_zero, Pi.zero_apply]
  ·
    intro u
    have happ := hset.apply_proj μ₀ u
    have hcoe : Om ((hset.proj μ₀ u : ↥X) : Fn) = μ₀ • ((hset.proj μ₀ u : ↥X) : Fn) := by
      have := congrArg (fun y : ↥X => (y : Fn)) happ
      simp [coe_Oml] at this
      exact this
    rcases hℓ with rfl | rfl
    · left
      refine ⟨rfl, ?_⟩
      have hμ : μ₀ = 0 := if_pos rfl
      set x : Fn := ((hset.proj μ₀ u : ↥X) : Fn) with hx
      have hxX : x ∈ X := (hset.proj μ₀ u).2
      have hOm : Om x = 0 := by rw [hcoe, hμ, zero_smul]

      have hL : ∀ i j : Fin 3, WhittakerBlock.archDeriv i j x - WhittakerBlock.archDeriv j i x ∈ X :=
        fun i j => L_mem hD hxX i j
      have hsq : ∀ i j : Fin 3,
          B (WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv i j x - WhittakerBlock.archDeriv j i x) -
              WhittakerBlock.archDeriv j i (WhittakerBlock.archDeriv i j x - WhittakerBlock.archDeriv j i x)) x =
            - B (WhittakerBlock.archDeriv i j x - WhittakerBlock.archDeriv j i x)
                (WhittakerBlock.archDeriv i j x - WhittakerBlock.archDeriv j i x) :=
        fun i j => B_L_skew hD B hB1 hB2 hB4 (hL i j) hxX i j
      have hsum : B (Om x) x =
          -(B (WhittakerBlock.archDeriv 0 1 x - WhittakerBlock.archDeriv 1 0 x) (WhittakerBlock.archDeriv 0 1 x - WhittakerBlock.archDeriv 1 0 x) +
            B (WhittakerBlock.archDeriv 0 2 x - WhittakerBlock.archDeriv 2 0 x) (WhittakerBlock.archDeriv 0 2 x - WhittakerBlock.archDeriv 2 0 x) +
            B (WhittakerBlock.archDeriv 1 2 x - WhittakerBlock.archDeriv 2 1 x) (WhittakerBlock.archDeriv 1 2 x - WhittakerBlock.archDeriv 2 1 x)) := by
        simp only [Om]
        rw [B_add_left B hB2 (X.add_mem (LL_mem hD hxX 0 1) (LL_mem hD hxX 0 2)) (LL_mem hD hxX 1 2) hxX,
          B_add_left B hB2 (LL_mem hD hxX 0 1) (LL_mem hD hxX 0 2) hxX, hsq, hsq, hsq]
        ring
      rw [hOm] at hsum
      have h0 : B 0 x = 0 := by
        have := hB2 1 _ X.zero_mem _ X.zero_mem _ hxX
        rw [one_smul, add_zero, one_mul] at this
        linear_combination -this
      rw [h0] at hsum
      have hre : ∀ w ∈ X, 0 ≤ (B w w).re := by
        intro w hw
        by_cases h : w = 0
        · subst h
          have h00 := hB2 1 _ X.zero_mem _ X.zero_mem _ X.zero_mem
          rw [one_smul, add_zero, one_mul] at h00
          have : B 0 0 = 0 := by linear_combination -h00
          rw [this]; simp
        · exact (hB3 w hw h).le
      have hzero : ∀ w ∈ X, (B w w).re = 0 → w = 0 := by
        intro w hw h0'
        by_contra hne
        have := hB3 w hw hne
        linarith
      have hreal := congrArg Complex.re hsum
      simp only [Complex.zero_re, Complex.neg_re, Complex.add_re] at hreal
      have r01 := hre _ (hL 0 1)
      have r02 := hre _ (hL 0 2)
      have r12 := hre _ (hL 1 2)
      have e01 := sub_eq_zero.1 (hzero _ (hL 0 1) (by linarith))
      have e02 := sub_eq_zero.1 (hzero _ (hL 0 2) (by linarith))
      have e12 := sub_eq_zero.1 (hzero _ (hL 1 2) (by linarith))
      intro i j
      rw [sub_eq_zero]
      rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl
      all_goals first | rfl | exact e01 | exact e02 | exact e12 | exact e01.symm | exact e02.symm | exact e12.symm
    · right
      refine ⟨rfl, ?_⟩
      have hμ : μ₀ = -2 := if_neg one_ne_zero
      change Om ((hset.proj μ₀ u : ↥X) : Fn) + (2 : ℂ) • ((hset.proj μ₀ u : ↥X) : Fn) = 0
      rw [hcoe, hμ, neg_smul, neg_add_cancel]

end
end
end
end
end
end S_LanglandsTunnell_CubicInduction_exists_isotypicProjector_natural_of_orthFinite_of_derivStable
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_isotypicProjector_natural_of_orthFinite_of_derivStable (solution)
