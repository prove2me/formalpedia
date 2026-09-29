-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.isArchSmooth3_deriv_archRealLift3_mul_and_linear_and_bracket
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/c0c8dab8-fb1a-59ac-84fd-f3a6ecfd60f2

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_isArchSmooth3_deriv_archRealLift3_mul_and_linear_and_bracket

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm Matrix Topology Filter
open LanglandsTunnell.CubicInduction

namespace WsB
namespace LC

abbrev E33 : Type := Fin 3 → Fin 3 → ℝ

def ofRealHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v : InfinitePlace ℚ =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.toRingHom

theorem ofRealHom_apply (r : ℝ) : ofRealHom r = StandardKernel.ofReal r := rfl

theorem ofRealHom_realCoord (x : InfiniteAdeleRing ℚ) : ofRealHom (StandardKernel.realCoord x) = x :=
  StandardKernel.ofReal_realCoord x

theorem realCoord_ofRealHom (r : ℝ) : StandardKernel.realCoord (ofRealHom r) = r :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

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

def idE : E33 := fun a b => if a = b then 1 else 0

theorem of_idE : Matrix.of idE = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext a b; rw [Matrix.of_apply, idE, Matrix.one_apply]

theorem lift_idE : WhittakerBlock.archRealLift3 idE = 1 := by
  have h : (Matrix.of idE).det ≠ 0 := by rw [of_idE, Matrix.det_one]; exact one_ne_zero
  refine Units.ext ?_
  rw [val_lift _ h, archRealMat3_eq, Units.val_one]
  have : realM idE = 1 := by
    change (Matrix.of idE).map ofRealHom = 1
    rw [of_idE, Matrix.map_one ofRealHom (map_zero _) (map_one _)]
  rw [this, archMatrixInclN_one]

abbrev MR : Type := Matrix (Fin 3) (Fin 3) ℝ
abbrev MI : Type := Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)
abbrev MA : Type := Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)

def Mg (g : AdelicGL 3 (𝓞 ℚ) ℚ) : GL (Fin 3) ℝ :=
  Matrix.GeneralLinearGroup.map StandardKernel.realCoord (archComponent3 (𝓞 ℚ) ℚ g)

def MgM (g : AdelicGL 3 (𝓞 ℚ) ℚ) : MR := ((Mg g : GL (Fin 3) ℝ) : MR)
def MgMinv (g : AdelicGL 3 (𝓞 ℚ) ℚ) : MR := (((Mg g)⁻¹ : GL (Fin 3) ℝ) : MR)

theorem MgMinv_mul_MgM (g : AdelicGL 3 (𝓞 ℚ) ℚ) : MgMinv g * MgM g = 1 := by
  unfold MgMinv MgM; rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem MgM_mul_MgMinv (g : AdelicGL 3 (𝓞 ℚ) ℚ) : MgM g * MgMinv g = 1 := by
  unfold MgMinv MgM; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

def conjE (g : AdelicGL 3 (𝓞 ℚ) ℚ) (e : E33) : E33 :=
  fun a b => (MgMinv g * Matrix.of e * MgM g) a b

theorem of_conjE (g : AdelicGL 3 (𝓞 ℚ) ℚ) (e : E33) :
    Matrix.of (conjE g e) = MgMinv g * Matrix.of e * MgM g := rfl

def AgM (g : AdelicGL 3 (𝓞 ℚ) ℚ) : MI := ((archComponent3 (𝓞 ℚ) ℚ g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : MI)
def AgMinv (g : AdelicGL 3 (𝓞 ℚ) ℚ) : MI := (((archComponent3 (𝓞 ℚ) ℚ g)⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : MI)

theorem AgM_mul_AgMinv (g : AdelicGL 3 (𝓞 ℚ) ℚ) : AgM g * AgMinv g = 1 := by
  unfold AgMinv AgM; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem realM_MgM (g : AdelicGL 3 (𝓞 ℚ) ℚ) : realM (MgM g) = AgM g := by
  change ((AgM g).map StandardKernel.realCoord).map ofRealHom = AgM g
  rw [Matrix.map_map]
  have : (⇑ofRealHom ∘ ⇑StandardKernel.realCoord) = id := funext ofRealHom_realCoord
  rw [this, Matrix.map_id]

theorem realM_MgMinv (g : AdelicGL 3 (𝓞 ℚ) ℚ) : realM (MgMinv g) = AgMinv g := by

  have h1 : realM (MgMinv g) * AgM g = 1 := by
    rw [← realM_MgM, ← realM_mul, MgMinv_mul_MgM]
    change (1 : MR).map ofRealHom = 1
    exact Matrix.map_one ofRealHom (map_zero _) (map_one _)
  have h2 : AgM g * AgMinv g = 1 := AgM_mul_AgMinv g
  calc realM (MgMinv g) = realM (MgMinv g) * (AgM g * AgMinv g) := by rw [h2, mul_one]
    _ = (realM (MgMinv g) * AgM g) * AgMinv g := by rw [mul_assoc]
    _ = AgMinv g := by rw [h1, one_mul]

theorem det_conjE (g : AdelicGL 3 (𝓞 ℚ) ℚ) (e : E33) : (Matrix.of (conjE g e)).det = (Matrix.of e).det := by
  rw [of_conjE, Matrix.det_mul, Matrix.det_mul]
  have : (MgMinv g).det * (MgM g).det = 1 := by
    rw [← Matrix.det_mul, MgMinv_mul_MgM, Matrix.det_one]
  linear_combination (Matrix.of e).det * this

theorem lift_mul_eq_mul_lift_conjE (g : AdelicGL 3 (𝓞 ℚ) ℚ) (e : E33) (he : (Matrix.of e).det ≠ 0) :
    WhittakerBlock.archRealLift3 e * g = g * WhittakerBlock.archRealLift3 (conjE g e) := by
  have hc : (Matrix.of (conjE g e)).det ≠ 0 := by rw [det_conjE]; exact he
  have hG : ∀ l j : Fin 3, AdelicLevel.adeleArch (𝓞 ℚ) ℚ (((g : AdelicGL 3 (𝓞 ℚ) ℚ) : MA) l j) = AgM g l j :=
    fun l j => rfl
  have hconj : realM (Matrix.of (conjE g e)) = AgMinv g * realM (Matrix.of e) * AgM g := by
    rw [of_conjE, realM_mul, realM_mul, realM_MgM, realM_MgMinv]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, val_lift e he, val_lift _ hc, archRealMat3_eq, archRealMat3_eq]
  ext i j
  refine Prod.ext ?_ ?_
  · change AdelicLevel.adeleArch (𝓞 ℚ) ℚ ((archMatrixInclN (Fin 3) ℚ (realM e) * ((g : AdelicGL 3 (𝓞 ℚ) ℚ) : MA)) i j) =
      AdelicLevel.adeleArch (𝓞 ℚ) ℚ ((((g : AdelicGL 3 (𝓞 ℚ) ℚ) : MA) * archMatrixInclN (Fin 3) ℚ (realM (conjE g e))) i j)
    simp only [Matrix.mul_apply, map_sum, map_mul, adeleArch_archMatrixInclN, hG]
    rw [← Matrix.mul_apply, ← Matrix.mul_apply]
    change (realM (Matrix.of e) * AgM g) i j = (AgM g * realM (Matrix.of (conjE g e))) i j
    rw [hconj, ← mul_assoc, ← mul_assoc, AgM_mul_AgMinv, one_mul]
  · change AdelicLevel.adeleFin (𝓞 ℚ) ℚ ((archMatrixInclN (Fin 3) ℚ (realM e) * ((g : AdelicGL 3 (𝓞 ℚ) ℚ) : MA)) i j) =
      AdelicLevel.adeleFin (𝓞 ℚ) ℚ ((((g : AdelicGL 3 (𝓞 ℚ) ℚ) : MA) * archMatrixInclN (Fin 3) ℚ (realM (conjE g e))) i j)
    simp only [Matrix.mul_apply, map_sum, map_mul, adeleFin_archMatrixInclN]
    simp [Matrix.one_apply]

end WsB.LC

namespace WsB
namespace LC

def invLocus : Set E33 := {m | (Matrix.of m).det ≠ 0}

theorem isOpen_invLocus : IsOpen invLocus := by
  have hc : Continuous fun e : E33 => (Matrix.of e).det :=
    (continuous_id : Continuous fun e : E33 => (Matrix.of e : Matrix (Fin 3) (Fin 3) ℝ)).matrix_det
  exact isOpen_ne_fun hc continuous_const

theorem idE_mem : idE ∈ invLocus := by
  show (Matrix.of idE).det ≠ 0
  rw [of_idE, Matrix.det_one]; exact one_ne_zero

def linX (X : E33) (s : ℝ) : E33 := fun a b => (if a = b then (1 : ℝ) else 0) + s * X a b

theorem linX_eq (X : E33) (s : ℝ) : linX X s = idE + s • X := by
  funext a b; simp [linX, idE, smul_eq_mul]

theorem continuous_linX (X : E33) : Continuous (linX X) := by
  have : linX X = fun s => idE + s • X := funext (linX_eq X)
  rw [this]
  exact continuous_const.add (continuous_id.smul continuous_const)

theorem eventually_linX_mem_invLocus (X : E33) : ∀ᶠ s in 𝓝 (0 : ℝ), linX X s ∈ invLocus := by
  have hc : Continuous fun s : ℝ => (Matrix.of (linX X s)).det :=
    ((continuous_linX X : Continuous fun s => (Matrix.of (linX X s) : Matrix (Fin 3) (Fin 3) ℝ))).matrix_det
  have h0 : (Matrix.of (linX X 0)).det ≠ 0 := by
    rw [linX_eq, zero_smul, add_zero, of_idE, Matrix.det_one]
    exact one_ne_zero
  exact hc.continuousAt.eventually_ne h0

def mulE (A : MR) (e : E33) : E33 := fun a b => (A * Matrix.of e) a b

def mulEL (A : MR) : E33 →L[ℝ] E33 :=
  LinearMap.toContinuousLinearMap
    { toFun := mulE A
      map_add' := fun e e' => by
        funext a b
        simp only [mulE, Pi.add_apply, Matrix.mul_apply, Matrix.of_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c e => by
        funext a b
        simp only [mulE, Pi.smul_apply, Matrix.mul_apply, Matrix.of_apply, smul_eq_mul, RingHom.id_apply,
          Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => by ring) }

theorem mulEL_apply (A : MR) (e : E33) : mulEL A e = mulE A e := rfl

theorem mulE_add (A : MR) (e e' : E33) : mulE A (e + e') = mulE A e + mulE A e' := (mulEL A).map_add e e'
theorem mulE_smul (A : MR) (c : ℝ) (e : E33) : mulE A (c • e) = c • mulE A e := (mulEL A).map_smul c e

theorem mulE_idE (A : MR) : mulE A idE = fun a b => A a b := by
  funext a b; simp only [mulE, of_idE, Matrix.mul_one]

theorem conjE_add (g : AdelicGL 3 (𝓞 ℚ) ℚ) (e e' : E33) : conjE g (e + e') = conjE g e + conjE g e' := by
  funext a b
  show (MgMinv g * Matrix.of (e + e') * MgM g) a b = (MgMinv g * Matrix.of e * MgM g) a b + (MgMinv g * Matrix.of e' * MgM g) a b
  rw [show Matrix.of (e + e') = Matrix.of e + Matrix.of e' from rfl, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]

theorem conjE_smul (g : AdelicGL 3 (𝓞 ℚ) ℚ) (c : ℝ) (e : E33) : conjE g (c • e) = c • conjE g e := by
  funext a b
  show (MgMinv g * Matrix.of (c • e) * MgM g) a b = c • (MgMinv g * Matrix.of e * MgM g) a b
  rw [show Matrix.of (c • e) = c • Matrix.of e from rfl, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply]

theorem conjE_sub (g : AdelicGL 3 (𝓞 ℚ) ℚ) (e e' : E33) : conjE g (e - e') = conjE g e - conjE g e' := by
  rw [sub_eq_add_neg, conjE_add, show -e' = (-1 : ℝ) • e' by simp, conjE_smul]; simp [sub_eq_add_neg]

theorem conjE_idE (g : AdelicGL 3 (𝓞 ℚ) ℚ) : conjE g idE = idE := by
  funext a b
  show (MgMinv g * Matrix.of idE * MgM g) a b = idE a b
  rw [of_idE, Matrix.mul_one, MgMinv_mul_MgM, idE, Matrix.one_apply]

theorem conjE_linX (g : AdelicGL 3 (𝓞 ℚ) ℚ) (X : E33) (s : ℝ) : conjE g (linX X s) = idE + s • conjE g X := by
  rw [linX_eq, conjE_add, conjE_smul, conjE_idE]

theorem mulE_of_conjE_idE (g : AdelicGL 3 (𝓞 ℚ) ℚ) (X : E33) : mulE (Matrix.of (conjE g X)) idE = conjE g X := by
  rw [mulE_idE]; rfl

theorem mulE_conjE_conjE (g : AdelicGL 3 (𝓞 ℚ) ℚ) (X Y : E33) :
    mulE (Matrix.of (conjE g X)) (conjE g Y) = conjE g (fun a b => (Matrix.of X * Matrix.of Y) a b) := by
  funext a b
  show (Matrix.of (conjE g X) * Matrix.of (conjE g Y)) a b =
    (MgMinv g * Matrix.of (fun a b => (Matrix.of X * Matrix.of Y) a b) * MgM g) a b
  rw [of_conjE, of_conjE, show Matrix.of (fun a b => (Matrix.of X * Matrix.of Y) a b) = Matrix.of X * Matrix.of Y from rfl]
  have hm : MgMinv g * Matrix.of X * MgM g * (MgMinv g * Matrix.of Y * MgM g) =
      MgMinv g * (Matrix.of X * Matrix.of Y) * MgM g := by
    calc MgMinv g * Matrix.of X * MgM g * (MgMinv g * Matrix.of Y * MgM g)
        = MgMinv g * Matrix.of X * (MgM g * MgMinv g) * Matrix.of Y * MgM g := by
          simp only [Matrix.mul_assoc]
      _ = MgMinv g * (Matrix.of X * Matrix.of Y) * MgM g := by
          rw [MgM_mul_MgMinv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [hm]

theorem lift_mul' {c e : E33} (hc : c ∈ invLocus) (he : e ∈ invLocus) :
    WhittakerBlock.archRealLift3 c * WhittakerBlock.archRealLift3 e =
      WhittakerBlock.archRealLift3 (fun a b => (Matrix.of c * Matrix.of e) a b) :=
  (lift_mul (Matrix.of c) (Matrix.of e) hc he).symm

def ψ (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : E33 → ℂ :=
  fun e => φ (g * WhittakerBlock.archRealLift3 e)

theorem ψ_smooth (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 φ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (ψ φ g) invLocus := hsa g

theorem deriv_left_flow (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (X : E33) {e : E33} (he : e ∈ invLocus) :
    deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (linX X s) * (g * WhittakerBlock.archRealLift3 e))) 0 =
      fderiv ℝ (ψ φ g) e (mulE (Matrix.of (conjE g X)) e) := by
  set v : E33 := mulE (Matrix.of (conjE g X)) e with hv
  have hev : (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (linX X s) * (g * WhittakerBlock.archRealLift3 e)))
      =ᶠ[𝓝 0] fun s => ψ φ g (e + s • v) := by
    filter_upwards [eventually_linX_mem_invLocus X] with s hs
    have hcs : conjE g (linX X s) ∈ invLocus := by
      show (Matrix.of (conjE g (linX X s))).det ≠ 0
      rw [det_conjE]; exact hs
    rw [← mul_assoc, lift_mul_eq_mul_lift_conjE g (linX X s) hs, mul_assoc, lift_mul' hcs he]
    show ψ φ g _ = ψ φ g _
    congr 1
    rw [conjE_linX]
    funext a b
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv, mulE]
    rw [show Matrix.of (idE + s • conjE g X) = 1 + s • Matrix.of (conjE g X) by rw [← of_idE]; rfl,
      Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
      smul_eq_mul]
  have hd : HasFDerivAt (ψ φ g) (fderiv ℝ (ψ φ g) e) e :=
    (((ψ_smooth φ hsa g).differentiableOn (by simp)) e he).differentiableAt (isOpen_invLocus.mem_nhds he)
      |>.hasFDerivAt
  have hc : HasDerivAt (fun s : ℝ => e + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add e
  have hd' : HasFDerivAt (ψ φ g) (fderiv ℝ (ψ φ g) e) (e + (0 : ℝ) • v) := by simpa using hd
  rw [hev.deriv_eq, show (fun s : ℝ => ψ φ g (e + s • v)) = ψ φ g ∘ fun s : ℝ => e + s • v from rfl]
  exact (hd'.comp_hasDerivAt (0 : ℝ) hc).deriv

theorem deriv_left_flow_zero (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (X : E33) :
    deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (linX X s) * g)) 0 =
      fderiv ℝ (ψ φ g) idE (conjE g X) := by
  have h := deriv_left_flow φ hsa g X idE_mem
  rw [lift_idE, mul_one, mulE_of_conjE_idE] at h
  exact h

theorem clause_i (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 φ) (X : E33) :
    WhittakerBlock.IsArchSmooth3
      (fun g => deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (linX X s) * g)) 0) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞)
    (fun e : E33 => deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (linX X s) *
      (g * WhittakerBlock.archRealLift3 e))) 0) invLocus
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun e => fderiv ℝ (ψ φ g) e) invLocus :=
    (ψ_smooth φ hsa g).fderiv_of_isOpen isOpen_invLocus (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by exact_mod_cast le_top)
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun e : E33 => mulE (Matrix.of (conjE g X)) e) invLocus :=
    (mulEL (Matrix.of (conjE g X))).contDiff.contDiffOn
  exact (hf.clm_apply hg).congr (fun e he => deriv_left_flow φ hsa g X he)

theorem clause_ii (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (X Y : E33) (α β : ℝ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (linX (fun a' b' => α * X a' b' + β * Y a' b') s) * g)) 0
      = (α : ℂ) * deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (linX X s) * g)) 0
        + (β : ℂ) * deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (linX Y s) * g)) 0 := by
  rw [deriv_left_flow_zero φ hsa, deriv_left_flow_zero φ hsa, deriv_left_flow_zero φ hsa]
  have : (fun a' b' => α * X a' b' + β * Y a' b') = α • X + β • Y := by
    funext a b; simp [smul_eq_mul]
  rw [this, conjE_add, conjE_smul, conjE_smul, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

theorem deriv_deriv_left_flows (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (X Y : E33) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (linX X s) *
        (WhittakerBlock.archRealLift3 (linX Y t) * g))) 0) 0
      = fderiv ℝ (fderiv ℝ (ψ φ g)) idE (conjE g Y) (conjE g X)
        + fderiv ℝ (ψ φ g) idE (mulE (Matrix.of (conjE g X)) (conjE g Y)) := by
  set cY : E33 := conjE g Y with hcY
  set CX : MR := Matrix.of (conjE g X) with hCX
  have hev : (fun t : ℝ => deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (linX X s) *
        (WhittakerBlock.archRealLift3 (linX Y t) * g))) 0)
      =ᶠ[𝓝 0] fun t => (fderiv ℝ (ψ φ g) (idE + t • cY)) (mulE CX (idE + t • cY)) := by
    filter_upwards [eventually_linX_mem_invLocus Y] with t ht
    have hct : conjE g (linX Y t) ∈ invLocus := by
      show (Matrix.of (conjE g (linX Y t))).det ≠ 0
      rw [det_conjE]; exact ht
    rw [lift_mul_eq_mul_lift_conjE g (linX Y t) ht, deriv_left_flow φ hsa g X hct, conjE_linX]
  rw [hev.deriv_eq]
  have hψ : ContDiffAt ℝ (⊤ : ℕ∞) (ψ φ g) idE := (ψ_smooth φ hsa g).contDiffAt (isOpen_invLocus.mem_nhds idE_mem)
  have hdd : DifferentiableAt ℝ (fderiv ℝ (ψ φ g)) idE :=
    (hψ.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by exact_mod_cast le_top)).differentiableAt (by simp)
  have h1 : HasFDerivAt (fderiv ℝ (ψ φ g)) (fderiv ℝ (fderiv ℝ (ψ φ g)) idE) (idE + (0 : ℝ) • cY) := by
    simpa using hdd.hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => idE + t • cY) cY 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const cY).const_add idE
  have hc : HasDerivAt (fun t : ℝ => fderiv ℝ (ψ φ g) (idE + t • cY)) (fderiv ℝ (fderiv ℝ (ψ φ g)) idE cY) 0 :=
    h1.comp_hasDerivAt (0 : ℝ) h2
  have hu : HasDerivAt (fun t : ℝ => mulE CX (idE + t • cY)) (mulE CX cY) 0 := by
    have : (fun t : ℝ => mulE CX (idE + t • cY)) = fun t => mulE CX idE + t • mulE CX cY := by
      funext t; rw [mulE_add, mulE_smul]
    rw [this]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (mulE CX cY)).const_add (mulE CX idE)
  have h := (hc.clm_apply hu).deriv
  rw [h]
  simp only [zero_smul, add_zero, hCX, mulE_of_conjE_idE]

theorem clause_iii (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 φ)
    (X Y : E33) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (linX X s) *
        (WhittakerBlock.archRealLift3 (linX Y t) * g))) 0) 0
      - deriv (fun t : ℝ => deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (linX Y s) *
        (WhittakerBlock.archRealLift3 (linX X t) * g))) 0) 0
      = deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3
          (linX (fun a' b' => (Matrix.of X * Matrix.of Y - Matrix.of Y * Matrix.of X) a' b') s) * g)) 0 := by
  rw [deriv_deriv_left_flows φ hsa X Y g, deriv_deriv_left_flows φ hsa Y X g, deriv_left_flow_zero φ hsa]
  have hψ : ContDiffAt ℝ (⊤ : ℕ∞) (ψ φ g) idE := (ψ_smooth φ hsa g).contDiffAt (isOpen_invLocus.mem_nhds idE_mem)
  have hsymm : IsSymmSndFDerivAt ℝ (ψ φ g) idE :=
    hψ.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 le_top)
  have hs : fderiv ℝ (fderiv ℝ (ψ φ g)) idE (conjE g Y) (conjE g X) =
      fderiv ℝ (fderiv ℝ (ψ φ g)) idE (conjE g X) (conjE g Y) := hsymm (conjE g Y) (conjE g X)
  have hD : (fun a' b' => (Matrix.of X * Matrix.of Y - Matrix.of Y * Matrix.of X) a' b') =
      (fun a b => (Matrix.of X * Matrix.of Y) a b) - (fun a b => (Matrix.of Y * Matrix.of X) a b) := by
    funext a b; simp [Matrix.sub_apply]
  rw [hs, mulE_conjE_conjE, mulE_conjE_conjE, hD, conjE_sub, map_sub]
  ring

end WsB.LC

open WsB.LC in
theorem solution
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 φ) :
    (∀ X : Fin 3 → Fin 3 → ℝ,
      WhittakerBlock.IsArchSmooth3 (fun g => deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + s * X a b) * g)) 0)) ∧
    (∀ (X Y : Fin 3 → Fin 3 → ℝ) (α β : ℝ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + s * (fun a' b' => α * X a' b' + β * Y a' b') a b) * g)) 0
        = (α : ℂ) * deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + s * X a b) * g)) 0
          + (β : ℂ) * deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + s * Y a b) * g)) 0) ∧
    (∀ (X Y : Fin 3 → Fin 3 → ℝ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      deriv (fun t : ℝ => deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + s * X a b) * (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + t * Y a b) * g))) 0) 0
        - deriv (fun t : ℝ => deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + s * Y a b) * (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + t * X a b) * g))) 0) 0
        = deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b => (if a = b then (1 : ℝ) else 0) + s * (fun a' b' => (Matrix.of X * Matrix.of Y - Matrix.of Y * Matrix.of X) a' b') a b) * g)) 0) :=
  ⟨fun X => clause_i φ hsa X, fun X Y α β g => clause_ii φ hsa X Y α β g, fun X Y g => clause_iii φ hsa X Y g⟩

end
end S_LanglandsTunnell_CubicInduction_isArchSmooth3_deriv_archRealLift3_mul_and_linear_and_bracket
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_isArchSmooth3_deriv_archRealLift3_mul_and_linear_and_bracket (solution)
