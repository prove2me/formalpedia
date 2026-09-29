-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.archDeriv_comp_transposeInv3_of_isArchSmooth3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/0099cb57-b9c1-5aa1-ba67-a499cf24bf05

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmoothSpace3
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_archDeriv_comp_transposeInv3_of_isArchSmooth3

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace R1DerivInvol

open Filter Topology Metric
open IsDedekindDomain NumberField AutomorphicForm Matrix
open LanglandsTunnell.CubicInduction
open LanglandsTunnell.CubicInduction.WhittakerBlock (archDeriv archRealLift3_mul)

section Iota

variable {A : Type*} [CommRing A]

theorem coe_transposeInv3 (g : GL (Fin 3) A) :
    ((transposeInv3 g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      ((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ := rfl

theorem coe_inv_transposeInv3 (g : GL (Fin 3) A) :
    (((transposeInv3 g)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      ((g : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ := rfl

theorem transposeInv3_mul (g h : GL (Fin 3) A) :
    transposeInv3 (g * h) = transposeInv3 g * transposeInv3 h := by
  apply Units.ext
  simp only [coe_transposeInv3, Units.val_mul, _root_.mul_inv_rev, Matrix.transpose_mul]

end Iota

section Arch

def ofRealHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.toRingHom

theorem realCoord_ofReal (r : ℝ) : StandardKernel.realCoord (StandardKernel.ofReal r) = r := by
  show (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)
    ((InfinitePlace.Completion.ringEquivRealOfIsReal _).symm r) = r
  exact RingEquiv.apply_symm_apply _ _

def rho : Matrix (Fin 3) (Fin 3) ℝ →+* Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) := ofRealHom.mapMatrix

def psi : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) →+* Matrix (Fin 3) (Fin 3) ℝ :=
  (StandardKernel.realCoord.comp (AdelicLevel.adeleArch (𝓞 ℚ) ℚ)).mapMatrix

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

theorem coe_archRealLift3 (e : Fin 3 → Fin 3 → ℝ) (h : (Matrix.of e).det ≠ 0) :
    ((WhittakerBlock.archRealLift3 e : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      WhittakerBlock.archRealMat3 e := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_pos ((isUnit_archRealMat3_iff e).mpr h)]
  exact ((isUnit_archRealMat3_iff e).mpr h).unit_spec

theorem archRealMat3_transpose (e : Fin 3 → Fin 3 → ℝ) :
    WhittakerBlock.archRealMat3 (fun a b => e b a) = (WhittakerBlock.archRealMat3 e)ᵀ := by
  ext i j
  change ((ofRealHom (e j i), (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ) =
    (ofRealHom (e j i), (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) j i)
  by_cases hij : i = j
  · subst hij; rfl
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]

theorem archRealLift3_one_array :
    WhittakerBlock.archRealLift3 (fun a b : Fin 3 => (1 : Matrix (Fin 3) (Fin 3) ℝ) a b) = 1 := by
  have h1 : (Matrix.of fun a b : Fin 3 => (1 : Matrix (Fin 3) (Fin 3) ℝ) a b) = 1 := by ext a b; rfl
  apply Units.ext
  rw [coe_archRealLift3 _ (by rw [h1, Matrix.det_one]; exact one_ne_zero), Units.val_one]
  change archMatrixInclN (Fin 3) ℚ (rho 1) = 1
  rw [map_one, archMatrixInclN_one]

def cfun (i j : Fin 3) (s : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0

def kap (i j : Fin 3) (s : ℝ) : ℝ := 1 + if i = j then s else 0

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

theorem cfun_transpose (i j : Fin 3) (s : ℝ) : (fun a b => cfun i j s b a) = cfun j i s := by
  funext a b
  simp only [cfun]
  congr 1
  · by_cases h : a = b
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
  · by_cases h : b = i ∧ a = j
    · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩)]

def sig (i j : Fin 3) (s : ℝ) : ℝ := if i = j then (1 + s)⁻¹ - 1 else -s

theorem sig_zero (i j : Fin 3) : sig i j 0 = 0 := by
  unfold sig; split_ifs <;> simp

theorem hasDerivAt_sig (i j : Fin 3) : HasDerivAt (sig i j) (-1) 0 := by
  unfold sig
  split_ifs with h
  · have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 0 := (hasDerivAt_id (0 : ℝ)).const_add 1
    have h2 := (h1.inv (by norm_num)).sub_const 1
    convert h2 using 1
    all_goals try rfl
    norm_num
  · exact (hasDerivAt_neg (0 : ℝ))

theorem of_cfun_mul_sig (i j : Fin 3) {s : ℝ} (hs : |s| < 1) :
    Matrix.of (cfun j i s) * Matrix.of (cfun j i (sig i j s)) = 1 := by
  rw [of_cfun_mul, ← cfun_zero j i]
  congr 2
  unfold kap sig
  by_cases h : i = j
  · subst h
    simp only [if_true]
    have h1 : (1 + s) ≠ 0 := by have := (abs_lt.mp hs).1; linarith
    field_simp
    ring
  · rw [if_neg (Ne.symm h), if_neg h]; ring

theorem abs_sig_lt (i j : Fin 3) {s : ℝ} (hs : |s| < 1 / 2) : |sig i j s| < 1 := by
  unfold sig
  obtain ⟨h1, h2⟩ := abs_lt.mp hs
  split_ifs with h
  · have hpos : 0 < 1 + s := by linarith
    rw [abs_lt]
    constructor
    · have : (1 + s)⁻¹ > 0 := inv_pos.mpr hpos
      linarith
    · have : (1 + s)⁻¹ < 2 := by
        rw [inv_lt_comm₀ hpos (by norm_num)]
        linarith
      linarith
  · rw [abs_neg]; linarith

def L (i j : Fin 3) (s : ℝ) : AdelicGL 3 (𝓞 ℚ) ℚ := WhittakerBlock.archRealLift3 (cfun i j s)

theorem archDeriv_apply (i j : Fin 3) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archDeriv i j φ g = deriv (fun s => φ (g * L i j s)) 0 := rfl

theorem transposeInv3_L (i j : Fin 3) {s : ℝ} (hs : |s| < 1 / 2) : transposeInv3 (L i j s) = L j i (sig i j s) := by
  have hs1 : |s| < 1 := lt_trans hs (by norm_num)
  have hdet : (Matrix.of (cfun i j s)).det ≠ 0 := det_cfun_ne i j hs1
  have hdetT : (Matrix.of (cfun j i s)).det ≠ 0 := det_cfun_ne j i hs1
  have hdetS : (Matrix.of (cfun j i (sig i j s))).det ≠ 0 := det_cfun_ne j i (abs_sig_lt i j hs)

  have hinv : (transposeInv3 (L i j s))⁻¹ = L j i s := by
    apply Units.ext
    rw [coe_inv_transposeInv3, L, L, coe_archRealLift3 _ hdet, coe_archRealLift3 _ hdetT, ← cfun_transpose i j s]
    exact (archRealMat3_transpose (cfun i j s)).symm

  have hprod : L j i s * L j i (sig i j s) = 1 := by
    rw [L, L, archRealLift3_mul hdetT hdetS, of_cfun_mul_sig i j hs1]
    exact archRealLift3_one_array
  rw [← _root_.inv_inj, hinv]
  exact eq_inv_of_mul_eq_one_left hprod

def U : Set (Fin 3 → Fin 3 → ℝ) := {e | (Matrix.of e).det ≠ 0}

theorem isOpen_U : IsOpen U := by
  have hc : Continuous fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).det :=
    (continuous_id : Continuous fun e : Fin 3 → Fin 3 → ℝ => Matrix.of e).matrix_det
  exact isOpen_compl_singleton.preimage hc

theorem hasDerivAt_cfun (i j : Fin 3) (s : ℝ) :
    HasDerivAt (cfun i j) (fun a b => if a = i ∧ b = j then (1 : ℝ) else 0) s := by
  have heq : cfun i j = fun s => (fun a b => if a = b then (1 : ℝ) else 0) +
      s • (fun a b => if a = i ∧ b = j then (1 : ℝ) else 0 : Fin 3 → Fin 3 → ℝ) := by
    funext s a b
    simp only [cfun, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [heq]
  have h := ((hasDerivAt_id s).smul_const (fun a b => if a = i ∧ b = j then (1 : ℝ) else 0 : Fin 3 → Fin 3 → ℝ)).const_add
    (fun a b : Fin 3 => if a = b then (1 : ℝ) else 0)
  rw [one_smul] at h
  exact h

variable {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}

theorem differentiableAt_comp_L (hΦ : WhittakerBlock.IsArchSmooth3 Φ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) :
    DifferentiableAt ℝ (fun σ => Φ (h * L i j σ)) 0 := by
  have hmem : cfun i j 0 ∈ U := by
    show (Matrix.of (cfun i j 0)).det ≠ 0
    rw [cfun_zero, Matrix.det_one]; exact one_ne_zero
  have hslice : DifferentiableAt ℝ (fun e : Fin 3 → Fin 3 → ℝ => Φ (h * WhittakerBlock.archRealLift3 e)) (cfun i j 0) :=
    ((hΦ h).differentiableOn (by simp)).differentiableAt (isOpen_U.mem_nhds hmem)
  exact hslice.comp (0 : ℝ) (hasDerivAt_cfun i j 0).differentiableAt

end Arch

end R1DerivInvol

open IsDedekindDomain NumberField AutomorphicForm
open Filter Topology Metric in
open LanglandsTunnell.CubicInduction R1DerivInvol in
theorem solution
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : WhittakerBlock.IsArchSmooth3 φ) (i j : Fin 3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.archDeriv i j (fun x => φ (transposeInv3 x)) g =
      -WhittakerBlock.archDeriv j i φ (transposeInv3 g) := by
  rw [archDeriv_apply, archDeriv_apply]

  have hev : (fun s => φ (transposeInv3 (g * L i j s))) =ᶠ[𝓝 0]
      fun s => (fun τ => φ (transposeInv3 g * L j i τ)) (sig i j s) := by
    have hnb : ball (0 : ℝ) (1 / 2) ∈ 𝓝 (0 : ℝ) := isOpen_ball.mem_nhds (by simp)
    filter_upwards [hnb] with s hs
    have hs' : |s| < 1 / 2 := by simpa [Real.dist_eq] using hs
    show φ (transposeInv3 (g * L i j s)) = φ (transposeInv3 g * L j i (sig i j s))
    rw [transposeInv3_mul, transposeInv3_L i j hs']
  rw [hev.deriv_eq]
  have hΦ : HasDerivAt (fun τ => φ (transposeInv3 g * L j i τ))
      (deriv (fun τ => φ (transposeInv3 g * L j i τ)) 0) (sig i j 0) := by
    rw [sig_zero]
    exact (differentiableAt_comp_L hφ (transposeInv3 g) j i).hasDerivAt
  have hcomp := hΦ.scomp (0 : ℝ) (hasDerivAt_sig i j)
  exact hcomp.deriv.trans (neg_one_smul ℝ _)

end
end S_LanglandsTunnell_CubicInduction_archDeriv_comp_transposeInv3_of_isArchSmooth3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_archDeriv_comp_transposeInv3_of_isArchSmooth3 (solution)
