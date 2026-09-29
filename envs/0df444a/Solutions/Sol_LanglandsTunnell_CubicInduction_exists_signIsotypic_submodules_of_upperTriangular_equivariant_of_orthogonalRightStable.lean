-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_signIsotypic_submodules_of_upperTriangular_equivariant_of_orthogonalRightStable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ae0c8500-337f-5fb4-b860-91570afdb3b5

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_signIsotypic_submodules_of_upperTriangular_equivariant_of_orthogonalRightStable

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace R4SignProj

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

abbrev G3 : Type _ := AdelicGL 3 (𝓞 ℚ) ℚ

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

def liftGL : GL (Fin 3) ℝ →* G3 := (archInclN (Fin 3) ℚ).comp (Units.map rho.toMonoidHom)

def toGL (e : Matrix (Fin 3) (Fin 3) ℝ) (h : e.det ≠ 0) : GL (Fin 3) ℝ :=
  Matrix.nonsingInvUnit e (isUnit_iff_ne_zero.mpr h)

theorem archRealLift3_eq (e : Matrix (Fin 3) (Fin 3) ℝ) (h : e.det ≠ 0) :
    WhittakerBlock.archRealLift3 e = liftGL (toGL e h) := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_pos ((isUnit_archRealMat3_iff e).mpr h)]
  exact Units.ext (by rw [IsUnit.unit_spec]; rfl)

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

def sgn (σ : Fin 3 → Fin 2) : Fin 3 → Fin 3 → ℝ := fun a b => if a = b then (-1 : ℝ) ^ (σ a : ℕ) else 0

theorem of_sgn (σ : Fin 3 → Fin 2) : Matrix.of (sgn σ) = Matrix.diagonal fun a => (-1 : ℝ) ^ (σ a : ℕ) := by
  ext a b
  simp only [sgn, Matrix.of_apply, Matrix.diagonal_apply]

theorem neg_one_pow_mul_self (n : ℕ) : (-1 : ℝ) ^ n * (-1) ^ n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]; norm_num

theorem det_sgn (σ : Fin 3 → Fin 2) : (Matrix.of (sgn σ)).det ≠ 0 := by
  rw [of_sgn, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun a _ => pow_ne_zero _ (by norm_num)

theorem neg_one_pow_fin2_add (s t : Fin 2) :
    (-1 : ℝ) ^ ((s + t : Fin 2) : ℕ) = (-1) ^ (s : ℕ) * (-1) ^ (t : ℕ) := by
  rw [Fin.val_add]
  fin_cases s <;> fin_cases t <;> norm_num

theorem of_sgn_mul_of_sgn (σ τ : Fin 3 → Fin 2) :
    Matrix.of (sgn σ) * Matrix.of (sgn τ) = Matrix.of (sgn (σ + τ)) := by
  rw [of_sgn, of_sgn, of_sgn, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  rw [Pi.add_apply, neg_one_pow_fin2_add]

theorem sgn_zero : sgn 0 = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  funext a b
  simp only [sgn, Pi.zero_apply, Fin.val_zero, pow_zero, Matrix.one_apply]

def L (σ : Fin 3 → Fin 2) : G3 := WhittakerBlock.archRealLift3 (sgn σ)

theorem L_mul (σ τ : Fin 3 → Fin 2) : L σ * L τ = L (σ + τ) := by
  unfold L
  rw [← archRealLift3_mul _ _ (det_sgn σ) (det_sgn τ), of_sgn_mul_of_sgn]
  rfl

theorem L_zero : L 0 = 1 := by
  unfold L
  rw [sgn_zero]
  exact archRealLift3_one

def conj (σ : Fin 3 → Fin 2) (t : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j => (-1 : ℝ) ^ (σ i : ℕ) * t i j * (-1) ^ (σ j : ℕ)

theorem conj_upper {t : Fin 3 → Fin 3 → ℝ} (ht : ∀ i j : Fin 3, j < i → t i j = 0) (σ : Fin 3 → Fin 2) :
    ∀ i j : Fin 3, j < i → conj σ t i j = 0 := by
  intro i j hij
  simp only [conj, ht i j hij, mul_zero, zero_mul]

theorem conj_diag (σ : Fin 3 → Fin 2) (t : Fin 3 → Fin 3 → ℝ) (i : Fin 3) : conj σ t i i = t i i := by
  unfold conj
  rw [mul_comm ((-1 : ℝ) ^ (σ i : ℕ)) (t i i), mul_assoc, neg_one_pow_mul_self, mul_one]

theorem det_upper_ne {t : Fin 3 → Fin 3 → ℝ} (ht : ∀ i j : Fin 3, j < i → t i j = 0)
    (hpos : ∀ i : Fin 3, 0 < t i i) : (Matrix.of t).det ≠ 0 := by
  have hbt : (Matrix.of t).BlockTriangular id := fun i j hij => ht i j hij
  rw [Matrix.det_of_upperTriangular hbt]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => (hpos i).ne'

theorem of_conj_mul_of_sgn (σ : Fin 3 → Fin 2) (t : Fin 3 → Fin 3 → ℝ) :
    Matrix.of (conj σ t) * Matrix.of (sgn σ) = Matrix.of (sgn σ) * Matrix.of t := by
  ext i j
  rw [of_sgn, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, Matrix.of_apply]
  unfold conj
  rw [mul_assoc, neg_one_pow_mul_self, mul_one]

theorem L_mul_lift_upper (σ : Fin 3 → Fin 2) {t : Fin 3 → Fin 3 → ℝ}
    (ht : ∀ i j : Fin 3, j < i → t i j = 0) (hpos : ∀ i : Fin 3, 0 < t i i) :
    L σ * WhittakerBlock.archRealLift3 t = WhittakerBlock.archRealLift3 (conj σ t) * L σ := by
  have hdt := det_upper_ne ht hpos
  have hdc := det_upper_ne (conj_upper ht σ) (fun i => by rw [conj_diag]; exact hpos i)
  unfold L
  rw [← archRealLift3_mul _ _ (det_sgn σ) hdt, ← archRealLift3_mul _ _ hdc (det_sgn σ), of_conj_mul_of_sgn]

def chi (ε σ : Fin 3 → Fin 2) : ℂ := (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (σ a : ℕ))

theorem chi_eq_prod (ε σ : Fin 3 → Fin 2) : chi ε σ = ∏ a : Fin 3, (-1 : ℂ) ^ ((ε a : ℕ) * (σ a : ℕ)) := by
  unfold chi
  rw [Finset.prod_pow_eq_pow_sum]

theorem chi_coord_add (e s t : Fin 2) :
    (-1 : ℂ) ^ ((e : ℕ) * ((s + t : Fin 2) : ℕ)) = (-1) ^ ((e : ℕ) * (s : ℕ)) * (-1) ^ ((e : ℕ) * (t : ℕ)) := by
  rw [Fin.val_add]
  fin_cases e <;> fin_cases s <;> fin_cases t <;> norm_num

theorem chi_add_right (ε σ τ : Fin 3 → Fin 2) : chi ε (σ + τ) = chi ε σ * chi ε τ := by
  rw [chi_eq_prod, chi_eq_prod, chi_eq_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun a _ => by rw [Pi.add_apply]; exact chi_coord_add _ _ _

theorem chi_mul_self (ε σ : Fin 3 → Fin 2) : chi ε σ * chi ε σ = 1 := by
  unfold chi
  rw [← pow_add, ← two_mul, pow_mul]; norm_num

theorem sum_chi (σ : Fin 3 → Fin 2) : ∑ ε : Fin 3 → Fin 2, chi ε σ = if σ = 0 then 8 else 0 := by
  classical
  have h : ∑ ε : Fin 3 → Fin 2, chi ε σ = ∏ a : Fin 3, ∑ e : Fin 2, (-1 : ℂ) ^ ((e : ℕ) * (σ a : ℕ)) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    exact Finset.sum_congr rfl fun ε _ => chi_eq_prod ε σ
  rw [h]
  split_ifs with hσ
  · subst hσ
    simp only [Pi.zero_apply, Fin.val_zero, mul_zero, pow_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, mul_one, Finset.prod_const]
    norm_num
  · obtain ⟨a, ha⟩ : ∃ a, σ a ≠ 0 := by
      by_contra h'
      push Not at h'
      exact hσ (funext h')
    have h1 : σ a = 1 := by
      rcases Fin.exists_fin_two.mp ⟨σ a, rfl⟩ with h0 | h0
      · exact absurd h0 ha
      · exact h0
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    rw [Fin.sum_univ_two, h1]
    norm_num

def T (σ : Fin 3 → Fin 2) : (G3 → ℂ) →ₗ[ℂ] (G3 → ℂ) := LinearMap.funLeft ℂ ℂ fun g : G3 => L σ * g

@[scoped simp] theorem T_apply (σ : Fin 3 → Fin 2) (F : G3 → ℂ) (g : G3) : T σ F g = F (L σ * g) := rfl

def P (ε : Fin 3 → Fin 2) : (G3 → ℂ) →ₗ[ℂ] (G3 → ℂ) := (1 / 8 : ℂ) • ∑ σ : Fin 3 → Fin 2, chi ε σ • T σ

theorem P_apply (ε : Fin 3 → Fin 2) (F : G3 → ℂ) (g : G3) :
    P ε F g = (1 / 8 : ℂ) * ∑ σ : Fin 3 → Fin 2, chi ε σ * F (L σ * g) := by
  simp only [P, LinearMap.smul_apply, LinearMap.sum_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
    T_apply]

theorem P_rightTranslate (ε : Fin 3 → Fin 2) (F : G3 → ℂ) (k : G3) :
    P ε (fun g => F (g * k)) = fun g => P ε F (g * k) := by
  funext g
  rw [P_apply, P_apply]
  simp only [mul_assoc]

theorem P_leftSign (ε : Fin 3 → Fin 2) (F : G3 → ℂ) (τ : Fin 3 → Fin 2) (g : G3) :
    P ε F (L τ * g) = chi ε τ * P ε F g := by
  rw [P_apply, P_apply, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight τ) _ _ fun σ => ?_
  simp only [Equiv.coe_addRight]
  rw [← mul_assoc (L σ) (L τ) g, L_mul, chi_add_right]
  linear_combination (-(1 / 8 : ℂ) * chi ε σ * F (L (σ + τ) * g)) * chi_mul_self ε τ

theorem sum_P (F : G3 → ℂ) (g : G3) : ∑ ε : Fin 3 → Fin 2, P ε F g = F g := by
  have h1 : ∀ ε : Fin 3 → Fin 2, P ε F g = ∑ σ : Fin 3 → Fin 2, (1 / 8 : ℂ) * (chi ε σ * F (L σ * g)) :=
    fun ε => by rw [P_apply, Finset.mul_sum]
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ σ : Fin 3 → Fin 2, ∑ ε : Fin 3 → Fin 2, (1 / 8 : ℂ) * (chi ε σ * F (L σ * g)) =
      (1 / 8 : ℂ) * F (L σ * g) * ∑ ε : Fin 3 → Fin 2, chi ε σ := by
    intro σ
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ε _ => by ring
  simp_rw [h2, sum_chi]
  rw [Finset.sum_eq_single (0 : Fin 3 → Fin 2)]
  · rw [if_pos rfl, L_zero, one_mul]; ring
  · intro σ _ hσ; rw [if_neg hσ, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem continuous_P (ε : Fin 3 → Fin 2) {F : G3 → ℂ} (hc : Continuous F) : Continuous (P ε F) := by
  have : (P ε F : G3 → ℂ) = fun g => (1 / 8 : ℂ) * ∑ σ : Fin 3 → Fin 2, chi ε σ * F (L σ * g) :=
    funext fun g => P_apply ε F g
  rw [this]
  exact continuous_const.mul
    (continuous_finsetSum _ fun σ _ => continuous_const.mul (hc.comp (continuous_const.mul continuous_id)))

theorem isArchSmooth3_P (ε : Fin 3 → Fin 2) {F : G3 → ℂ} (hs : WhittakerBlock.IsArchSmooth3 F) :
    WhittakerBlock.IsArchSmooth3 (P ε F) := by
  intro g
  have : (fun e : Fin 3 → Fin 3 → ℝ => P ε F (g * WhittakerBlock.archRealLift3 e)) =
      fun e => (1 / 8 : ℂ) * ∑ σ : Fin 3 → Fin 2, chi ε σ * F ((L σ * g) * WhittakerBlock.archRealLift3 e) := by
    funext e
    rw [P_apply]
    simp only [mul_assoc]
  rw [this]
  exact contDiffOn_const.mul (ContDiffOn.sum fun σ _ => contDiffOn_const.mul (hs (L σ * g)))

theorem hasDerivAt_P (ε : Fin 3 → Fin 2) (i j : Fin 3) (F F' : G3 → ℂ)
    (h : ∀ g : G3, HasDerivAt (fun s : ℝ => F (g * WhittakerBlock.archRealLift3 fun a b =>
        (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0)) (F' g) 0) (g : G3) :
    HasDerivAt (fun s : ℝ => P ε F (g * WhittakerBlock.archRealLift3 fun a b =>
        (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0)) (P ε F' g) 0 := by
  simp only [P_apply]
  refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun σ _ => HasDerivAt.const_mul _ ?_)
  simpa only [mul_assoc] using h (L σ * g)

theorem archDeriv_P (ε : Fin 3 → Fin 2) (i j : Fin 3) (F F' : G3 → ℂ)
    (h : ∀ g : G3, HasDerivAt (fun s : ℝ => F (g * WhittakerBlock.archRealLift3 fun a b =>
        (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0)) (F' g) 0) :
    WhittakerBlock.archDeriv i j (P ε F) = P ε F' := by
  funext g
  exact (hasDerivAt_P ε i j F F' h g).deriv

def FlowClosed (V : Submodule ℂ (G3 → ℂ)) : Prop :=
  ∀ G ∈ V, ∀ c₀ d₀ : Fin 3, ∃ G' ∈ V, ∀ g : G3,
    HasDerivAt (fun s : ℝ => G (g * WhittakerBlock.archRealLift3 fun a b =>
      (if a = b then (1 : ℝ) else 0) + if a = c₀ ∧ b = d₀ then s else 0)) (G' g) 0

theorem archDeriv_mem {V : Submodule ℂ (G3 → ℂ)} (hV : FlowClosed V) {F : G3 → ℂ} (hF : F ∈ V)
    (i j : Fin 3) : WhittakerBlock.archDeriv i j F ∈ V := by
  obtain ⟨F', hF', h⟩ := hV F hF i j
  have e : WhittakerBlock.archDeriv i j F = F' := funext fun g => (h g).deriv
  rw [e]
  exact hF'

theorem archDeriv_P_of_mem {V : Submodule ℂ (G3 → ℂ)} (hV : FlowClosed V) (ε : Fin 3 → Fin 2)
    {F : G3 → ℂ} (hF : F ∈ V) (i j : Fin 3) :
    WhittakerBlock.archDeriv i j (P ε F) = P ε (WhittakerBlock.archDeriv i j F) := by
  obtain ⟨F', hF', h⟩ := hV F hF i j
  have e : WhittakerBlock.archDeriv i j F = F' := funext fun g => (h g).deriv
  rw [e]
  exact archDeriv_P ε i j F F' h

theorem casimir1_P {V : Submodule ℂ (G3 → ℂ)} (hV : FlowClosed V) (ε : Fin 3 → Fin 2)
    {F : G3 → ℂ} (hF : F ∈ V) : WhittakerBlock.casimir1 (P ε F) = P ε (WhittakerBlock.casimir1 F) := by
  funext g
  show (∑ i : Fin 3, WhittakerBlock.archDeriv i i (P ε F) g) =
    P ε (fun g : G3 => ∑ i : Fin 3, WhittakerBlock.archDeriv i i F g) g
  have e : (fun g : G3 => ∑ i : Fin 3, WhittakerBlock.archDeriv i i F g) =
      ∑ i : Fin 3, WhittakerBlock.archDeriv i i F := by
    funext g
    rw [Finset.sum_apply]
  rw [e, map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [archDeriv_P_of_mem hV ε hF]

theorem casimir2_P {V : Submodule ℂ (G3 → ℂ)} (hV : FlowClosed V) (ε : Fin 3 → Fin 2)
    {F : G3 → ℂ} (hF : F ∈ V) : WhittakerBlock.casimir2 (P ε F) = P ε (WhittakerBlock.casimir2 F) := by
  funext g
  show (∑ i : Fin 3, ∑ j : Fin 3, WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j i (P ε F)) g) =
    P ε (fun g : G3 => ∑ i : Fin 3, ∑ j : Fin 3,
      WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j i F) g) g
  have e : (fun g : G3 => ∑ i : Fin 3, ∑ j : Fin 3,
      WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j i F) g) =
      ∑ i : Fin 3, ∑ j : Fin 3, WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j i F) := by
    funext g
    simp only [Finset.sum_apply]
  rw [e, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [archDeriv_P_of_mem hV ε hF, archDeriv_P_of_mem hV ε (archDeriv_mem hV hF j i)]

theorem casimir3_P {V : Submodule ℂ (G3 → ℂ)} (hV : FlowClosed V) (ε : Fin 3 → Fin 2)
    {F : G3 → ℂ} (hF : F ∈ V) : WhittakerBlock.casimir3 (P ε F) = P ε (WhittakerBlock.casimir3 F) := by
  funext g
  show (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, WhittakerBlock.archDeriv i j
      (WhittakerBlock.archDeriv j k (WhittakerBlock.archDeriv k i (P ε F))) g) =
    P ε (fun g : G3 => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j k (WhittakerBlock.archDeriv k i F)) g) g
  have e : (fun g : G3 => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j k (WhittakerBlock.archDeriv k i F)) g) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        WhittakerBlock.archDeriv i j (WhittakerBlock.archDeriv j k (WhittakerBlock.archDeriv k i F)) := by
    funext g
    simp only [Finset.sum_apply]
  rw [e, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [archDeriv_P_of_mem hV ε hF, archDeriv_P_of_mem hV ε (archDeriv_mem hV hF k i),
    archDeriv_P_of_mem hV ε (archDeriv_mem hV (archDeriv_mem hV hF k i) j k)]

theorem equivariant_P (ε : Fin 3 → Fin 2) (ν : Fin 3 → ℂ) {F : G3 → ℂ}
    (heq : ∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : G3, F (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * F g)
    (t : Fin 3 → Fin 3 → ℝ) (ht : ∀ i j : Fin 3, j < i → t i j = 0) (hpos : ∀ i : Fin 3, 0 < t i i)
    (g : G3) :
    P ε F (WhittakerBlock.archRealLift3 t * g) =
      (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * P ε F g := by
  rw [P_apply, P_apply, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hct := conj_upper ht σ
  have hcpos : ∀ i : Fin 3, 0 < conj σ t i i := fun i => by rw [conj_diag]; exact hpos i
  rw [← mul_assoc (L σ), L_mul_lift_upper σ ht hpos, mul_assoc (WhittakerBlock.archRealLift3 (conj σ t)) (L σ) g,
    heq (conj σ t) hct hcpos (L σ * g)]
  simp only [conj_diag]
  ring

end R4SignProj
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_signIsotypic_submodules_of_upperTriangular_equivariant_of_orthogonalRightStable.R4SignProj"

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

theorem solution
    (ν : Fin 3 → ℂ) (lam₁ lam₂ lam₃ : ℂ) (V : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1)
    (hcont : (∀ G ∈ V, Continuous G))
    (hcas : (∀ G ∈ V, WhittakerBlock.IsArchSmooth3 G ∧ WhittakerBlock.casimir1 G = lam₁ • G ∧
        WhittakerBlock.casimir2 G = lam₂ • G ∧ WhittakerBlock.casimir3 G = lam₃ • G))
    (heq : (∀ G ∈ V, ∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, G (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * G g))
    (hstab : (∀ G ∈ V, ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) →
        archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 → (fun g => G (g * k')) ∈ V))
    (hfin : (∀ G ∈ V, ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) → archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 →
          (fun g => G (g * k')) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))))
    (hflow : (∀ G ∈ V, ∀ c₀ d₀ : Fin 3, ∃ G' ∈ V, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        HasDerivAt (fun s : ℝ => G (g * WhittakerBlock.archRealLift3 fun a b =>
          (if a = b then (1 : ℝ) else 0) + if a = c₀ ∧ b = d₀ then s else 0)) (G' g) 0))
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ V)
    (hne : ∃ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) ∧ F (WhittakerBlock.archRealLift3 o * k₁) ≠ 0) :
    ∃ Vf : (Fin 3 → Fin 2) → Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (∀ ε : Fin 3 → Fin 2,
      (∀ G ∈ Vf ε, Continuous G) ∧
      (∀ G ∈ Vf ε, WhittakerBlock.IsArchSmooth3 G ∧ WhittakerBlock.casimir1 G = lam₁ • G ∧
        WhittakerBlock.casimir2 G = lam₂ • G ∧ WhittakerBlock.casimir3 G = lam₃ • G) ∧
      (∀ G ∈ Vf ε, ∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, G (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * G g) ∧
      (∀ G ∈ Vf ε, ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) →
        archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 → (fun g => G (g * k')) ∈ Vf ε) ∧
      (∀ G ∈ Vf ε, ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k' : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1) → archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3 →
          (fun g => G (g * k')) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) ∧
      (∀ G ∈ Vf ε, ∀ c₀ d₀ : Fin 3, ∃ G' ∈ Vf ε, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        HasDerivAt (fun s : ℝ => G (g * WhittakerBlock.archRealLift3 fun a b =>
          (if a = b then (1 : ℝ) else 0) + if a = c₀ ∧ b = d₀ then s else 0)) (G' g) 0) ∧
      (∀ G ∈ Vf ε, ∀ σ : Fin 3 → Fin 2, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        G (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (σ a : ℕ) else 0) * g) =
          (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (σ a : ℕ)) * G g) ∧
      (∀ G ∈ Vf ε, ∃ F ∈ V, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        G g = (1 / 8 : ℂ) * ∑ σ : Fin 3 → Fin 2, (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (σ a : ℕ)) *
          F (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (σ a : ℕ) else 0) * g))) ∧
      ∃ ε : Fin 3 → Fin 2, ∃ G ∈ Vf ε, ∃ o : Fin 3 → Fin 3 → ℝ,
        (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) ∧ G (WhittakerBlock.archRealLift3 o * k₁) ≠ 0 := by
  classical
  have hfl : R4SignProj.FlowClosed V := hflow
  refine ⟨fun ε => V.map (R4SignProj.P ε), fun ε => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    intro G hG
    obtain ⟨F', hF', rfl⟩ := Submodule.mem_map.mp hG
    exact R4SignProj.continuous_P ε (hcont F' hF')
  ·
    intro G hG
    obtain ⟨F', hF', rfl⟩ := Submodule.mem_map.mp hG
    obtain ⟨hs, h1, h2, h3⟩ := hcas F' hF'
    refine ⟨R4SignProj.isArchSmooth3_P ε hs, ?_, ?_, ?_⟩
    · rw [R4SignProj.casimir1_P hfl ε hF', h1, map_smul]
    · rw [R4SignProj.casimir2_P hfl ε hF', h2, map_smul]
    · rw [R4SignProj.casimir3_P hfl ε hF', h3, map_smul]
  ·
    intro G hG t ht hpos g
    obtain ⟨F', hF', rfl⟩ := Submodule.mem_map.mp hG
    exact R4SignProj.equivariant_P ε ν (heq F' hF') t ht hpos g
  ·
    intro G hG k' hk₁ hk₂
    obtain ⟨F', hF', rfl⟩ := Submodule.mem_map.mp hG
    rw [← R4SignProj.P_rightTranslate]
    exact Submodule.mem_map_of_mem (hstab F' hF' k' hk₁ hk₂)
  ·
    intro G hG
    obtain ⟨F', hF', rfl⟩ := Submodule.mem_map.mp hG
    obtain ⟨s, hs⟩ := hfin F' hF'
    refine ⟨s.image (R4SignProj.P ε), fun k' hk₁ hk₂ => ?_⟩
    rw [← R4SignProj.P_rightTranslate, Finset.coe_image, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem (hs k' hk₁ hk₂)
  ·
    intro G hG c₀ d₀
    obtain ⟨F', hF', rfl⟩ := Submodule.mem_map.mp hG
    obtain ⟨F'', hF'', h⟩ := hflow F' hF' c₀ d₀
    exact ⟨R4SignProj.P ε F'', Submodule.mem_map_of_mem hF'', R4SignProj.hasDerivAt_P ε c₀ d₀ F' F'' h⟩
  ·
    intro G hG σ g
    obtain ⟨F', hF', rfl⟩ := Submodule.mem_map.mp hG
    exact R4SignProj.P_leftSign ε F' σ g
  ·
    intro G hG
    obtain ⟨F', hF', rfl⟩ := Submodule.mem_map.mp hG
    exact ⟨F', hF', fun g => R4SignProj.P_apply ε F' g⟩
  ·
    obtain ⟨o, ho, hFo⟩ := hne
    have hsum := R4SignProj.sum_P F (WhittakerBlock.archRealLift3 o * k₁)
    rw [← hsum] at hFo
    obtain ⟨ε, -, hε⟩ := Finset.exists_ne_zero_of_sum_ne_zero hFo
    exact ⟨ε, R4SignProj.P ε F, Submodule.mem_map_of_mem hF, o, ho, hε⟩

end
end S_LanglandsTunnell_CubicInduction_exists_signIsotypic_submodules_of_upperTriangular_equivariant_of_orthogonalRightStable
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_signIsotypic_submodules_of_upperTriangular_equivariant_of_orthogonalRightStable (solution)
