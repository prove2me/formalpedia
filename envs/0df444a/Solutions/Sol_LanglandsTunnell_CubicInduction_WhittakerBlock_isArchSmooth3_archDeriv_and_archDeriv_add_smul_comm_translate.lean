-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.WhittakerBlock.isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/49b4f922-8710-5808-af17-35a2c6a62cd6

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL archComponent3"
namespace RaySupplyK1
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open _root_.WhittakerBlock LanglandsTunnell.CubicInduction.WhittakerBlock AutomorphicForm AutomorphicForm.StandardKernel Matrix

abbrev G3 : Type := AdelicGL 3 (𝓞 ℚ) ℚ
abbrev M3 : Type := Matrix (Fin 3) (Fin 3) ℝ

def ofRealHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.toRingHom

theorem ofRealHom_apply (r : ℝ) : ofRealHom r = ofReal r := rfl

theorem realCoord_ofReal (r : ℝ) : realCoord (ofReal r) = r :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

def liftR : GL (Fin 3) ℝ →* GL (Fin 3) (InfiniteAdeleRing ℚ) :=
  Units.map (ofRealHom.mapMatrix (m := Fin 3)).toMonoidHom

theorem liftR_apply (g : GL (Fin 3) ℝ) (i j : Fin 3) :
    ((liftR g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j =
      ofReal ((g : M3) i j) := rfl

theorem realGL_liftR (g : GL (Fin 3) ℝ) : realGL (liftR g) = g := by
  refine Units.ext ?_
  ext i j
  change realCoord (ofReal ((g : M3) i j)) = (g : M3) i j
  exact realCoord_ofReal _

theorem liftR_realGL (x : GL (Fin 3) (InfiniteAdeleRing ℚ)) : liftR (realGL x) = x := by
  refine Units.ext ?_
  ext i j
  rw [liftR_apply]
  exact ofReal_realCoord _

def E : GL (Fin 3) ℝ →* G3 := (archInclN (Fin 3) ℚ).comp liftR

theorem E_apply (g : GL (Fin 3) ℝ) (i j : Fin 3) :
    ((E g : G3) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j =
      ((ofReal ((g : M3) i j), (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) :
          InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) := rfl

theorem archComponent3_E (g : GL (Fin 3) ℝ) : archComponent3 (𝓞 ℚ) ℚ (E g) = liftR g :=
  archComponentN_archInclN (Fin 3) ℚ (liftR g)

def toGL (e : Fin 3 → Fin 3 → ℝ) (h : (Matrix.of e).det ≠ 0) : GL (Fin 3) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) h

@[scoped simp] theorem coe_toGL (e : Fin 3 → Fin 3 → ℝ) (h : (Matrix.of e).det ≠ 0) : (toGL e h : M3) = Matrix.of e := rfl

theorem archRealLift3_eq_E (e : Fin 3 → Fin 3 → ℝ) (h : (Matrix.of e).det ≠ 0) :
    archRealLift3 e = E (toGL e h) := by
  have hmat : archRealMat3 e = ((E (toGL e h) : G3) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) := rfl
  have hu : IsUnit (archRealMat3 e) := by rw [hmat]; exact Units.isUnit _
  unfold archRealLift3
  rw [dif_pos hu]
  exact Units.ext (by rw [IsUnit.unit_spec, hmat])

theorem archRealLift3_one' : archRealLift3 (fun i j : Fin 3 => if i = j then (1 : ℝ) else 0) = 1 := by
  have h : (Matrix.of fun i j : Fin 3 => if i = j then (1 : ℝ) else 0).det ≠ 0 := by
    rw [show (Matrix.of fun i j : Fin 3 => if i = j then (1 : ℝ) else 0) = 1 from by
      ext i j; simp [Matrix.one_apply]]
    simp
  rw [archRealLift3_eq_E _ h, ← map_one E]
  congr 1
  refine Units.ext ?_
  ext i j
  simp [toGL, Matrix.one_apply]

theorem archRealLift3_mul (e e' : Fin 3 → Fin 3 → ℝ) (h : (Matrix.of e).det ≠ 0) (h' : (Matrix.of e').det ≠ 0) :
    archRealLift3 e * archRealLift3 e' = archRealLift3 (fun i j => (Matrix.of e * Matrix.of e') i j) := by
  have hh : (Matrix.of fun i j => (Matrix.of e * Matrix.of e') i j).det ≠ 0 := by
    rw [show (Matrix.of fun i j => (Matrix.of e * Matrix.of e') i j) = Matrix.of e * Matrix.of e' from rfl,
      Matrix.det_mul]
    exact mul_ne_zero h h'
  rw [archRealLift3_eq_E e h, archRealLift3_eq_E e' h', archRealLift3_eq_E _ hh, ← map_mul]
  congr 1
  exact Units.ext rfl

abbrev AM3 : Type := Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)

theorem archInclN_coe_apply (x : GL (Fin 3) (InfiniteAdeleRing ℚ)) (i j : Fin 3) :
    ((archInclN (Fin 3) ℚ x : G3) : AM3) i j =
      (((x : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j,
        (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) :
          InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ) := rfl

theorem archInclN_mul_comm_of_archComponent3_eq_one (x : GL (Fin 3) (InfiniteAdeleRing ℚ)) (h : G3)
    (hh : archComponent3 (𝓞 ℚ) ℚ h = 1) : archInclN (Fin 3) ℚ x * h = h * archInclN (Fin 3) ℚ x := by
  set X : AM3 := ((archInclN (Fin 3) ℚ x : G3) : AM3) with hX
  set Hm : AM3 := ((h : G3) : AM3) with hHm
  have hXa : X.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) = (x : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) := by
    ext i j; rfl
  have hXf : X.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ) = 1 := by
    ext i j; rfl
  have hHa : Hm.map (AdelicLevel.adeleArch (𝓞 ℚ) ℚ) = 1 := by
    have := congrArg (fun k : GL (Fin 3) (InfiniteAdeleRing ℚ) => (k : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))) hh
    exact this
  refine Units.ext ?_
  change X * Hm = Hm * X
  ext i j
  refine Prod.ext ?_ ?_
  · change AdelicLevel.adeleArch (𝓞 ℚ) ℚ ((X * Hm) i j) = AdelicLevel.adeleArch (𝓞 ℚ) ℚ ((Hm * X) i j)
    rw [← Matrix.map_apply (f := AdelicLevel.adeleArch (𝓞 ℚ) ℚ) (M := X * Hm),
      ← Matrix.map_apply (f := AdelicLevel.adeleArch (𝓞 ℚ) ℚ) (M := Hm * X), Matrix.map_mul, Matrix.map_mul,
      hXa, hHa, Matrix.mul_one, Matrix.one_mul]
  · change AdelicLevel.adeleFin (𝓞 ℚ) ℚ ((X * Hm) i j) = AdelicLevel.adeleFin (𝓞 ℚ) ℚ ((Hm * X) i j)
    rw [← Matrix.map_apply (f := AdelicLevel.adeleFin (𝓞 ℚ) ℚ) (M := X * Hm),
      ← Matrix.map_apply (f := AdelicLevel.adeleFin (𝓞 ℚ) ℚ) (M := Hm * X), Matrix.map_mul, Matrix.map_mul,
      hXf, Matrix.mul_one, Matrix.one_mul]

theorem E_mul_comm_of_archComponent3_eq_one (g : GL (Fin 3) ℝ) (h : G3) (hh : archComponent3 (𝓞 ℚ) ℚ h = 1) :
    E g * h = h * E g :=
  archInclN_mul_comm_of_archComponent3_eq_one (liftR g) h hh

abbrev Arr : Type := Fin 3 → Fin 3 → ℝ

def idA : Arr := fun a b => if a = b then (1 : ℝ) else 0

def El (i j : Fin 3) : Arr := fun a b => if a = i ∧ b = j then (1 : ℝ) else 0

def sgl (i j : Fin 3) (s : ℝ) : Arr := fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0

def mulA (e e' : Arr) : Arr := fun a b => (Matrix.of e * Matrix.of e') a b

theorem of_mulA (e e' : Arr) : Matrix.of (mulA e e') = Matrix.of e * Matrix.of e' := rfl

theorem of_idA : Matrix.of idA = (1 : M3) := by
  ext a b; simp [idA, Matrix.one_apply]

theorem det_idA : (Matrix.of idA).det ≠ 0 := by rw [of_idA, Matrix.det_one]; exact one_ne_zero

theorem sgl_eq (i j : Fin 3) (s : ℝ) : sgl i j s = idA + s • El i j := by
  funext a b
  simp only [sgl, idA, El, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

theorem sgl_zero (i j : Fin 3) : sgl i j 0 = idA := by
  rw [sgl_eq, zero_smul, add_zero]

theorem mulA_idA (e : Arr) : mulA e idA = e := by
  have : Matrix.of (mulA e idA) = Matrix.of e := by rw [of_mulA, of_idA, Matrix.mul_one]
  exact this

theorem idA_mulA (e : Arr) : mulA idA e = e := by
  have : Matrix.of (mulA idA e) = Matrix.of e := by rw [of_mulA, of_idA, Matrix.one_mul]
  exact this

theorem mulA_add (e x y : Arr) : mulA e (x + y) = mulA e x + mulA e y := by
  have : Matrix.of (mulA e (x + y)) = Matrix.of (mulA e x) + Matrix.of (mulA e y) := by
    rw [of_mulA, of_mulA, of_mulA, show Matrix.of (x + y) = Matrix.of x + Matrix.of y from rfl, Matrix.mul_add]
  exact this

theorem mulA_smul (e : Arr) (s : ℝ) (x : Arr) : mulA e (s • x) = s • mulA e x := by
  have : Matrix.of (mulA e (s • x)) = s • Matrix.of (mulA e x) := by
    rw [of_mulA, of_mulA, show Matrix.of (s • x) = s • Matrix.of x from rfl, Matrix.mul_smul]
  exact this

theorem add_mulA (x y e : Arr) : mulA (x + y) e = mulA x e + mulA y e := by
  have : Matrix.of (mulA (x + y) e) = Matrix.of (mulA x e) + Matrix.of (mulA y e) := by
    rw [of_mulA, of_mulA, of_mulA, show Matrix.of (x + y) = Matrix.of x + Matrix.of y from rfl, Matrix.add_mul]
  exact this

theorem smul_mulA (s : ℝ) (x e : Arr) : mulA (s • x) e = s • mulA x e := by
  have : Matrix.of (mulA (s • x) e) = s • Matrix.of (mulA x e) := by
    rw [of_mulA, of_mulA, show Matrix.of (s • x) = s • Matrix.of x from rfl, Matrix.smul_mul]
  exact this

def mulRightL (K : Arr) : Arr →L[ℝ] Arr :=
  LinearMap.toContinuousLinearMap
    { toFun := fun e => mulA e K
      map_add' := fun x y => add_mulA x y K
      map_smul' := fun s x => smul_mulA s x K }

@[scoped simp] theorem mulRightL_apply (K e : Arr) : mulRightL K e = mulA e K := rfl

def mulLeftL (K : Arr) : Arr →L[ℝ] Arr :=
  LinearMap.toContinuousLinearMap
    { toFun := fun e => mulA K e
      map_add' := fun x y => mulA_add K x y
      map_smul' := fun s x => mulA_smul K s x }

@[scoped simp] theorem mulLeftL_apply (K e : Arr) : mulLeftL K e = mulA K e := rfl

theorem mulA_El (i j k l : Fin 3) : mulA (El i j) (El k l) = if j = k then El i l else 0 := by
  funext a b
  simp only [mulA, Matrix.mul_apply, Matrix.of_apply, El]
  by_cases hjk : j = k
  · subst hjk
    rw [if_pos rfl, Finset.sum_eq_single j]
    · by_cases ha : a = i <;> by_cases hb : b = l <;> simp [ha, hb, El]
    · intro c _ hc; simp [hc]
    · intro h; exact absurd (Finset.mem_univ j) h
  · rw [if_neg hjk]
    simp only [Pi.zero_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases h1 : a = i ∧ c = j
    · rw [if_pos h1, one_mul, if_neg]
      rintro ⟨hc, -⟩; exact hjk (h1.2.symm.trans hc)
    · rw [if_neg h1, zero_mul]

def U3 : Set Arr := {e | (Matrix.of e).det ≠ 0}

theorem continuous_det_of : Continuous fun e : Arr => (Matrix.of e).det := by
  have : Continuous fun e : Arr => Matrix.of e := by
    refine continuous_matrix fun i j => ?_
    exact (continuous_apply j).comp (continuous_apply i)
  exact this.matrix_det

theorem isOpen_U3 : IsOpen U3 :=
  isOpen_ne_fun continuous_det_of continuous_const

theorem idA_mem_U3 : idA ∈ U3 := det_idA

theorem mulA_mem_U3 {e e' : Arr} (h : e ∈ U3) (h' : e' ∈ U3) : mulA e e' ∈ U3 := by
  change (Matrix.of (mulA e e')).det ≠ 0
  rw [of_mulA, Matrix.det_mul]; exact mul_ne_zero h h'

theorem det_sgl (i j : Fin 3) (s : ℝ) : (Matrix.of (sgl i j s)).det = if i = j then 1 + s else 1 := by
  fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_three, sgl]

theorem sgl_mem_U3 (i j : Fin 3) {s : ℝ} (hs : |s| < 1) : sgl i j s ∈ U3 := by
  change (Matrix.of (sgl i j s)).det ≠ 0
  rw [det_sgl]
  split_ifs
  · have := abs_lt.mp hs
    intro h; linarith [this.1]
  · exact one_ne_zero

theorem eventually_sgl_mem_U3 (i j : Fin 3) : ∀ᶠ s in nhds (0 : ℝ), sgl i j s ∈ U3 := by
  have : Set.Ioo (-1 : ℝ) 1 ∈ nhds (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  filter_upwards [this] with s hs
  exact sgl_mem_U3 i j (abs_lt.mpr hs)

def Φ (φ : G3 → ℂ) (g : G3) : Arr → ℂ := fun e => φ (g * archRealLift3 e)

theorem archRealLift3_idA : archRealLift3 idA = 1 := archRealLift3_one'

theorem Φ_idA (φ : G3 → ℂ) (g : G3) : Φ φ g idA = φ g := by
  simp only [Φ, archRealLift3_idA, mul_one]

theorem archDeriv_def (i j : Fin 3) (φ : G3 → ℂ) (g : G3) :
    archDeriv i j φ g = deriv (fun s : ℝ => φ (g * archRealLift3 (sgl i j s))) 0 := rfl

theorem contDiffAt_Φ {φ : G3 → ℂ} (hφ : IsArchSmooth3 φ) (g : G3) {e : Arr} (he : e ∈ U3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (Φ φ g) e :=
  (hφ g).contDiffAt (isOpen_U3.mem_nhds he)

theorem differentiableAt_Φ {φ : G3 → ℂ} (hφ : IsArchSmooth3 φ) (g : G3) {e : Arr} (he : e ∈ U3) :
    DifferentiableAt ℝ (Φ φ g) e :=
  (contDiffAt_Φ hφ g he).differentiableAt (by simp)

theorem line_eventuallyEq (φ : G3 → ℂ) (g : G3) {e : Arr} (he : e ∈ U3) (i j : Fin 3) :
    (fun s : ℝ => φ (g * archRealLift3 e * archRealLift3 (sgl i j s))) =ᶠ[nhds 0]
      fun s => Φ φ g (e + s • mulA e (El i j)) := by
  filter_upwards [eventually_sgl_mem_U3 i j] with s hs
  have harr : (fun a b => (Matrix.of e * Matrix.of (sgl i j s)) a b) = e + s • mulA e (El i j) := by
    change mulA e (sgl i j s) = e + s • mulA e (El i j)
    rw [sgl_eq, mulA_add, mulA_smul, mulA_idA]
  change φ _ = φ _
  rw [mul_assoc, archRealLift3_mul e _ he hs, harr]

theorem hasDerivAt_line {φ : G3 → ℂ} {g : G3} {e : Arr} (he : e ∈ U3) (hd : DifferentiableAt ℝ (Φ φ g) e)
    (i j : Fin 3) :
    HasDerivAt (fun s : ℝ => φ (g * archRealLift3 e * archRealLift3 (sgl i j s)))
      (fderiv ℝ (Φ φ g) e (mulA e (El i j))) 0 := by
  refine HasDerivAt.congr_of_eventuallyEq ?_ (line_eventuallyEq φ g he i j)
  have hline : HasDerivAt (fun s : ℝ => e + s • mulA e (El i j)) (mulA e (El i j)) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (mulA e (El i j))).const_add e
    simpa using this
  have h0 : e = (fun s : ℝ => e + s • mulA e (El i j)) 0 := by simp
  have hcomp := HasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hd.hasFDerivAt hline h0
  exact hcomp

theorem archDeriv_apply_mul_lift {φ : G3 → ℂ} (hφ : IsArchSmooth3 φ) (g : G3) {e : Arr} (he : e ∈ U3)
    (i j : Fin 3) :
    archDeriv i j φ (g * archRealLift3 e) = fderiv ℝ (Φ φ g) e (mulA e (El i j)) :=
  (hasDerivAt_line he (differentiableAt_Φ hφ g he) i j).deriv

theorem archDeriv_eq_fderiv {φ : G3 → ℂ} (hφ : IsArchSmooth3 φ) (g : G3) (i j : Fin 3) :
    archDeriv i j φ g = fderiv ℝ (Φ φ g) idA (El i j) := by
  have := archDeriv_apply_mul_lift hφ g idA_mem_U3 i j
  rwa [archRealLift3_idA, mul_one, idA_mulA] at this

theorem top_add_one_le : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact le_of_eq (by norm_cast)

theorem contDiffOn_fderiv_Φ {φ : G3 → ℂ} (hφ : IsArchSmooth3 φ) (g : G3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun e => fderiv ℝ (Φ φ g) e) U3 :=
  (hφ g).fderiv_of_isOpen isOpen_U3 top_add_one_le

theorem isArchSmooth3_archDeriv {φ : G3 → ℂ} (hφ : IsArchSmooth3 φ) (i j : Fin 3) :
    IsArchSmooth3 (archDeriv i j φ) := by
  intro g
  have hEq : Set.EqOn (fun e => fderiv ℝ (Φ φ g) e (mulRightL (El i j) e)) (Φ (archDeriv i j φ) g) U3 :=
    fun e he => (archDeriv_apply_mul_lift hφ g he i j).symm
  exact ((contDiffOn_fderiv_Φ hφ g).clm_apply (mulRightL (El i j)).contDiff.contDiffOn).congr
    (fun e he => (hEq he).symm)

theorem archDeriv_add {φ ψ : G3 → ℂ} (hφ : IsArchSmooth3 φ) (hψ : IsArchSmooth3 ψ) (i j : Fin 3) :
    archDeriv i j (φ + ψ) = archDeriv i j φ + archDeriv i j ψ := by
  funext g
  have h1 := hasDerivAt_line (φ := φ) (g := g) idA_mem_U3 (differentiableAt_Φ hφ g idA_mem_U3) i j
  have h2 := hasDerivAt_line (φ := ψ) (g := g) idA_mem_U3 (differentiableAt_Φ hψ g idA_mem_U3) i j
  simp only [archRealLift3_idA, mul_one] at h1 h2
  rw [Pi.add_apply, archDeriv_def, archDeriv_def, archDeriv_def, h1.deriv, h2.deriv]
  exact (h1.add h2).deriv

theorem archDeriv_smul (c : ℂ) (φ : G3 → ℂ) (i j : Fin 3) : archDeriv i j (c • φ) = c • archDeriv i j φ := by
  funext g
  show deriv (fun s : ℝ => (c • φ) (g * archRealLift3 (sgl i j s))) 0 =
    c • deriv (fun s : ℝ => φ (g * archRealLift3 (sgl i j s))) 0
  simp only [Pi.smul_apply, smul_eq_mul]
  exact deriv_const_mul_field c

theorem archDeriv_archDeriv {φ : G3 → ℂ} (hφ : IsArchSmooth3 φ) (g : G3) (i j k l : Fin 3) :
    archDeriv i j (archDeriv k l φ) g =
      fderiv ℝ (fderiv ℝ (Φ φ g)) idA (El i j) (El k l) + fderiv ℝ (Φ φ g) idA (mulA (El i j) (El k l)) := by

  set c : Arr → (Arr →L[ℝ] ℂ) := fun e => fderiv ℝ (Φ φ g) e with hc
  set G : Arr → ℂ := fun e => c e (mulRightL (El k l) e) with hG
  have hGeq : ∀ e ∈ U3, Φ (archDeriv k l φ) g e = G e := fun e he => archDeriv_apply_mul_lift hφ g he k l

  have hev : (fun s : ℝ => (archDeriv k l φ) (g * archRealLift3 (sgl i j s))) =ᶠ[nhds 0]
      fun s => G (idA + s • El i j) := by
    filter_upwards [eventually_sgl_mem_U3 i j] with s hs
    rw [← sgl_eq]
    exact hGeq _ hs

  have hcd : DifferentiableAt ℝ c idA :=
    ((contDiffOn_fderiv_Φ hφ g).contDiffAt (isOpen_U3.mem_nhds idA_mem_U3)).differentiableAt (by simp)
  have hG' : HasFDerivAt G ((c idA).comp (mulRightL (El k l)) + (fderiv ℝ c idA).flip (mulRightL (El k l) idA))
      idA :=
    hcd.hasFDerivAt.clm_apply (mulRightL (El k l)).hasFDerivAt
  have hline : HasDerivAt (fun s : ℝ => idA + s • El i j) (El i j) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (El i j)).const_add idA
    simpa using this
  have h0 : idA = (fun s : ℝ => idA + s • El i j) 0 := by simp
  have hcomp := HasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hG' hline h0
  have hfinal := (hcomp.congr_of_eventuallyEq hev).deriv
  rw [archDeriv_def, hfinal]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, mulRightL_apply,
    ContinuousLinearMap.flip_apply, idA_mulA, hc]
  ring

theorem two_le_top : minSmoothness ℝ 2 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  simp only [minSmoothness_of_isRCLikeNormedField]
  have h : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  exact h

theorem archDeriv_comm {φ : G3 → ℂ} (hφ : IsArchSmooth3 φ) (i j k l : Fin 3) :
    archDeriv i j (archDeriv k l φ) - archDeriv k l (archDeriv i j φ) =
      (if j = k then archDeriv i l φ else 0) - (if l = i then archDeriv k j φ else 0) := by
  funext g
  have hsymm : fderiv ℝ (fderiv ℝ (Φ φ g)) idA (El i j) (El k l) = fderiv ℝ (fderiv ℝ (Φ φ g)) idA (El k l) (El i j) :=
    (contDiffAt_Φ hφ g idA_mem_U3).isSymmSndFDerivAt two_le_top (El i j) (El k l)
  rw [Pi.sub_apply, archDeriv_archDeriv hφ g i j k l, archDeriv_archDeriv hφ g k l i j, hsymm, add_sub_add_left_eq_sub,
    ← map_sub, mulA_El, mulA_El]
  rw [Pi.sub_apply]
  have hi : ∀ (P : Prop) [Decidable P] (a b : Fin 3),
      (if P then archDeriv a b φ else 0) g = fderiv ℝ (Φ φ g) idA (if P then El a b else 0) := by
    intro P _ a b
    split_ifs
    · exact archDeriv_eq_fderiv hφ g a b
    · simp
  rw [hi (j = k) i l, hi (l = i) k j, ← map_sub]

def κ (y : G3) : GL (Fin 3) ℝ := realGL (archComponent3 (𝓞 ℚ) ℚ y)

def fin (y : G3) : G3 := (E (κ y))⁻¹ * y

theorem E_κ_mul_fin (y : G3) : E (κ y) * fin y = y := mul_inv_cancel_left _ _

theorem archComponent3_fin (y : G3) : archComponent3 (𝓞 ℚ) ℚ (fin y) = 1 := by
  rw [fin, map_mul, map_inv, archComponent3_E, κ, liftR_realGL, inv_mul_cancel]

def conjA (y : G3) : Arr →L[ℝ] Arr :=
  (mulRightL (fun a b => ((κ y : GL (Fin 3) ℝ) : M3) a b)).comp
    (mulLeftL (fun a b => (((κ y)⁻¹ : GL (Fin 3) ℝ) : M3) a b))

theorem conjA_apply (y : G3) (e : Arr) :
    conjA y e = mulA (mulA (fun a b => (((κ y)⁻¹ : GL (Fin 3) ℝ) : M3) a b) e)
      (fun a b => ((κ y : GL (Fin 3) ℝ) : M3) a b) := rfl

theorem of_conjA (y : G3) (e : Arr) :
    Matrix.of (conjA y e) = (((κ y)⁻¹ : GL (Fin 3) ℝ) : M3) * Matrix.of e * ((κ y : GL (Fin 3) ℝ) : M3) := rfl

theorem conjA_idA (y : G3) : conjA y idA = idA := by
  have : Matrix.of (conjA y idA) = Matrix.of idA := by
    rw [of_conjA, of_idA, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  exact this

theorem conjA_mem_U3 (y : G3) {e : Arr} (he : e ∈ U3) : conjA y e ∈ U3 := by
  change (Matrix.of (conjA y e)).det ≠ 0
  rw [of_conjA, Matrix.det_mul, Matrix.det_mul]
  refine mul_ne_zero (mul_ne_zero ?_ he) ?_
  · rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact ((κ y)⁻¹).det.ne_zero
  · rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (κ y).det.ne_zero

theorem archRealLift3_conjA (y : G3) {e : Arr} (he : e ∈ U3) :
    archRealLift3 (conjA y e) = (E (κ y))⁻¹ * archRealLift3 e * E (κ y) := by
  rw [archRealLift3_eq_E _ (conjA_mem_U3 y he), archRealLift3_eq_E e he, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Units.ext (of_conjA y e)

theorem Φ_translate_eqOn {φ : G3 → ℂ} (y g : G3) :
    Set.EqOn (Φ (fun x => φ (x * y)) g) (Φ φ (g * y) ∘ conjA y) U3 := by
  intro e he
  simp only [Function.comp_apply, Φ]
  rw [archRealLift3_conjA y he, archRealLift3_eq_E e he]
  congr 1
  have hcomm := E_mul_comm_of_archComponent3_eq_one ((κ y)⁻¹ * toGL e he * κ y) (fin y) (archComponent3_fin y)
  rw [map_mul, map_mul, map_inv] at hcomm
  have hy : y = E (κ y) * fin y := (E_κ_mul_fin y).symm
  calc g * E (toGL e he) * y
      = g * E (toGL e he) * (E (κ y) * fin y) := by rw [← hy]
    _ = g * E (κ y) * ((E (κ y))⁻¹ * E (toGL e he) * E (κ y) * fin y) := by
        simp only [mul_assoc, mul_inv_cancel_left]
    _ = g * E (κ y) * (fin y * ((E (κ y))⁻¹ * E (toGL e he) * E (κ y))) := by rw [hcomm]
    _ = g * (E (κ y) * fin y) * ((E (κ y))⁻¹ * E (toGL e he) * E (κ y)) := by simp only [mul_assoc]
    _ = g * y * ((E (κ y))⁻¹ * E (toGL e he) * E (κ y)) := by rw [← hy]

theorem isArchSmooth3_translate {φ : G3 → ℂ} (hφ : IsArchSmooth3 φ) (y : G3) :
    IsArchSmooth3 (fun x => φ (x * y)) := by
  intro g
  refine ContDiffOn.congr ?_ (Φ_translate_eqOn y g)
  exact (hφ (g * y)).comp (conjA y).contDiff.contDiffOn fun e he => conjA_mem_U3 y he

theorem conjA_El (y : G3) (i j : Fin 3) :
    conjA y (El i j) = ∑ p : Fin 3, ∑ q : Fin 3,
      ((((κ y)⁻¹ : GL (Fin 3) ℝ) : M3) p i * ((κ y : GL (Fin 3) ℝ) : M3) j q) • El p q := by
  funext a b
  rw [conjA_apply]
  simp only [mulA, Matrix.mul_apply, Matrix.of_apply, El, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]

  rw [Finset.sum_eq_single j, Finset.sum_eq_single i]
  · simp only [and_self, if_true]
    rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
    · simp
    · intro q _ hq; simp [Ne.symm hq]
    · simp
    · intro p _ hp; simp [Ne.symm hp]
    · simp
  · intro y _ hy; simp [hy]
  · simp
  · intro x _ hx; simp [hx]
  · simp

theorem archDeriv_translate {φ : G3 → ℂ} (hφ : IsArchSmooth3 φ) (y g : G3) (i j : Fin 3) :
    archDeriv i j (fun x => φ (x * y)) g =
      ∑ p : Fin 3, ∑ q : Fin 3,
        ((((κ y)⁻¹ : GL (Fin 3) ℝ) : M3) p i * ((κ y : GL (Fin 3) ℝ) : M3) j q : ℂ) * archDeriv p q φ (g * y) := by
  have hψ := isArchSmooth3_translate hφ y
  rw [archDeriv_eq_fderiv hψ g i j]
  have hev : Φ (fun x => φ (x * y)) g =ᶠ[nhds idA] (Φ φ (g * y) ∘ conjA y) :=
    Filter.eventuallyEq_of_mem (isOpen_U3.mem_nhds idA_mem_U3) (Φ_translate_eqOn y g)
  rw [hev.fderiv_eq]
  have hd : DifferentiableAt ℝ (Φ φ (g * y)) (conjA y idA) := by
    rw [conjA_idA]; exact differentiableAt_Φ hφ (g * y) idA_mem_U3
  rw [fderiv_comp idA hd (conjA y).differentiableAt, (conjA y).fderiv, ContinuousLinearMap.comp_apply,
    conjA_idA, conjA_El, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [ContinuousLinearMap.map_smul, archDeriv_eq_fderiv hφ (g * y) p q, Complex.real_smul, Complex.ofReal_mul]

theorem main :
    (∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, WhittakerBlock.IsArchSmooth3 φ →
      ∀ i j : Fin 3, WhittakerBlock.IsArchSmooth3 (archDeriv i j φ)) ∧
    (∀ φ ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, WhittakerBlock.IsArchSmooth3 φ → WhittakerBlock.IsArchSmooth3 ψ →
      ∀ i j : Fin 3, archDeriv i j (φ + ψ) = archDeriv i j φ + archDeriv i j ψ) ∧
    (∀ (c : ℂ) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ i j : Fin 3, archDeriv i j (c • φ) = c • archDeriv i j φ) ∧
    (∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, WhittakerBlock.IsArchSmooth3 φ → ∀ i j k l : Fin 3,
      archDeriv i j (archDeriv k l φ) - archDeriv k l (archDeriv i j φ) =
        (if j = k then archDeriv i l φ else 0) - (if l = i then archDeriv k j φ else 0)) ∧
    (∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, WhittakerBlock.IsArchSmooth3 φ → ∀ (y : AdelicGL 3 (𝓞 ℚ) ℚ),
      WhittakerBlock.IsArchSmooth3 (fun x => φ (x * y)) ∧
      ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3),
        archDeriv i j (fun x => φ (x * y)) g =
          ∑ p : Fin 3, ∑ q : Fin 3,
            ((((StandardKernel.realGL (archComponent3 (𝓞 ℚ) ℚ y))⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) p i *
              ((StandardKernel.realGL (archComponent3 (𝓞 ℚ) ℚ y) : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) j q : ℂ) *
            archDeriv p q φ (g * y)) :=
  ⟨fun _ hφ i j => isArchSmooth3_archDeriv hφ i j,
   fun _ _ hφ hψ i j => archDeriv_add hφ hψ i j,
   fun c φ i j => archDeriv_smul c φ i j,
   fun _ hφ i j k l => archDeriv_comm hφ i j k l,
   fun _ hφ y => ⟨isArchSmooth3_translate hφ y, fun g i j => archDeriv_translate hφ y g i j⟩⟩

end LanglandsTunnell.CubicInduction.RaySupplyK1
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.LanglandsTunnell.CubicInduction.RaySupplyK1"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.LanglandsTunnell.CubicInduction.RaySupplyK1"

open IsDedekindDomain NumberField AutomorphicForm _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.WhittakerBlock in

theorem solution :
    (∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, WhittakerBlock.IsArchSmooth3 φ →
      ∀ i j : Fin 3, WhittakerBlock.IsArchSmooth3 (archDeriv i j φ)) ∧
    (∀ φ ψ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, WhittakerBlock.IsArchSmooth3 φ → WhittakerBlock.IsArchSmooth3 ψ →
      ∀ i j : Fin 3, archDeriv i j (φ + ψ) = archDeriv i j φ + archDeriv i j ψ) ∧
    (∀ (c : ℂ) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ i j : Fin 3, archDeriv i j (c • φ) = c • archDeriv i j φ) ∧
    (∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, WhittakerBlock.IsArchSmooth3 φ → ∀ i j k l : Fin 3,
      archDeriv i j (archDeriv k l φ) - archDeriv k l (archDeriv i j φ) =
        (if j = k then archDeriv i l φ else 0) - (if l = i then archDeriv k j φ else 0)) ∧
    (∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, WhittakerBlock.IsArchSmooth3 φ → ∀ (y : AdelicGL 3 (𝓞 ℚ) ℚ),
      WhittakerBlock.IsArchSmooth3 (fun x => φ (x * y)) ∧
      ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3),
        archDeriv i j (fun x => φ (x * y)) g =
          ∑ p : Fin 3, ∑ q : Fin 3,
            ((((StandardKernel.realGL (archComponent3 (𝓞 ℚ) ℚ y))⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) p i *
              ((StandardKernel.realGL (archComponent3 (𝓞 ℚ) ℚ y) : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) j q : ℂ) *
            archDeriv p q φ (g * y)) :=
  LanglandsTunnell.CubicInduction.RaySupplyK1.main

end S_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_WhittakerBlock_isArchSmooth3_archDeriv_and_archDeriv_add_smul_comm_translate (solution)
