-- Prove2me | solution 1 for ModularCurve.exists_mem_periodLatticeOf_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/0c604594-1bce-5629-8485-6827b9260719

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitiveOf
import Theorems.Thm_ModularCurve_periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_mem_periodLatticeOf_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "periodOf periodLatticeOf periodOf_mem_periodLatticeOf HasEquivariantPrimitiveOf period Period.IsParabolicHom exists_hasEquivariantPrimitiveOf periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf"
namespace PoincareDualIntegrality
p2m_open "ModularCurve"

open UpperHalfPlane Filter Complex MeasureTheory Asymptotics
open scoped MatrixGroups Topology ModularForm Real Pointwise

section Coboundary

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem exists_eq_coboundary (f : Equiv.Perm α) (ψ : α → ℤ)
    (h : ∀ x n, 0 < n → (f ^ n) x = x → ∑ j ∈ Finset.range n, ψ ((f ^ j) x) = 0) :
    ∃ m : α → ℤ, ∀ x, ψ x = m (f x) - m x := by
  classical
  let S : Setoid α := Equiv.Perm.SameCycle.setoid f
  let rep : α → α := fun x => (Quotient.mk S x).out
  have hrep : ∀ x, f.SameCycle (rep x) x := fun x => Quotient.mk_out (s := S) x
  have hrepf : ∀ x, rep (f x) = rep x := by
    intro x
    simp only [rep]
    congr 1
    exact Quotient.sound (s := S) ((Equiv.Perm.sameCycle_apply_left).mpr (Equiv.Perm.SameCycle.refl f x))
  have hex : ∀ x, ∃ k : ℕ, (f ^ k) (rep x) = x := fun x => by
    obtain ⟨i, -, hi⟩ := (hrep x).exists_pow_eq'
    exact ⟨i, hi⟩
  let k : α → ℕ := fun x => Nat.find (hex x)
  have hk : ∀ x, (f ^ k x) (rep x) = x := fun x => Nat.find_spec (hex x)
  have hkmin : ∀ x j, j < k x → (f ^ j) (rep x) ≠ x := fun x j hj => Nat.find_min (hex x) hj
  refine ⟨fun x => ∑ j ∈ Finset.range (k x), ψ ((f ^ j) (rep x)), fun x => ?_⟩
  simp only [hrepf]

  have hle : k (f x) ≤ k x + 1 := by
    apply Nat.find_min'
    rw [pow_succ', Equiv.Perm.mul_apply, hrepf, hk]
  rcases Nat.lt_or_ge (k (f x)) (k x + 1) with hlt | hge
  ·

    have hk0 : k (f x) = 0 := by
      by_contra hne
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hne
      have h1 := hk (f x)
      rw [hrepf, hj, pow_succ', Equiv.Perm.mul_apply, f.injective.eq_iff] at h1
      exact hkmin x j (by omega) h1
    have hfx : f x = rep x := by simpa [hk0, hrepf] using (hk (f x)).symm

    have hper : (f ^ (k x + 1)) (rep x) = rep x := by
      rw [pow_succ', Equiv.Perm.mul_apply, hk, hfx]
    have hsum := h (rep x) (k x + 1) (Nat.succ_pos _) hper
    rw [Finset.sum_range_succ, hk] at hsum
    rw [hk0, Finset.sum_range_zero]
    linarith
  · have hkeq : k (f x) = k x + 1 := le_antisymm hle hge
    rw [hkeq, Finset.sum_range_succ, hk]
    ring

omit [DecidableEq α] in

theorem sum_coboundary_mul (f : Equiv.Perm α) (a : α → ℂ) (m : α → ℤ)
    (ha : ∀ x, a x = m (f x) - m x)
    (X P : α → ℂ) (hX : ∀ x, X (f x) = X x + P x) :
    ∑ x, a x * X x = -∑ x, (m (f x) : ℂ) * P x := by
  have h1 : ∑ x, (m x : ℂ) * X x = ∑ x, (m (f x) : ℂ) * X (f x) :=
    (Equiv.sum_comp f (fun x => (m x : ℂ) * X x)).symm
  simp only [ha, sub_mul, Finset.sum_sub_distrib, h1, hX, mul_add, Finset.sum_add_distrib]
  ring

end Coboundary

section Cocycle

variable {Γ : Subgroup SL(2, ℤ)} [hn : Fact ((-1 : SL(2, ℤ)) ∈ Γ)]

local notation "Q" => SL(2, ℤ) ⧸ Γ

theorem gam_mem (M : SL(2, ℤ)) (q : Q) :
    (Quotient.out (M • q))⁻¹ * M * Quotient.out q ∈ Γ := by
  rw [mul_assoc, ← QuotientGroup.eq, QuotientGroup.out_eq', ← MulAction.Quotient.coe_smul_out,
    smul_eq_mul]

def gam (M : SL(2, ℤ)) (q : Q) : Γ := ⟨_, gam_mem M q⟩

@[scoped simp] theorem coe_gam (M : SL(2, ℤ)) (q : Q) :
    ((gam M q : Γ) : SL(2, ℤ)) = (Quotient.out (M • q))⁻¹ * M * Quotient.out q := rfl

theorem gam_mul (M M' : SL(2, ℤ)) (q : Q) : gam (M * M') q = gam M (M' • q) * gam M' q := by
  ext1
  simp only [coe_gam, Subgroup.coe_mul, mul_smul]
  group

theorem gam_one (q : Q) : gam (1 : SL(2, ℤ)) q = 1 := by
  ext1; simp

theorem sum_range_phi_gam (φ : Additive Γ →+ ℤ) (M : SL(2, ℤ)) (q : Q) (n : ℕ) :
    ∑ j ∈ Finset.range n, φ (Additive.ofMul (gam M (M ^ j • q))) =
      φ (Additive.ofMul (gam (M ^ n) q)) := by
  induction n with
  | zero => simp [gam_one]
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ', gam_mul, ofMul_mul, map_add, add_comm]

theorem toPerm_pow_apply (M : SL(2, ℤ)) (j : ℕ) (q : Q) :
    ((MulAction.toPerm M : Equiv.Perm Q) ^ j) q = M ^ j • q := by
  induction j generalizing q with
  | zero => simp
  | succ j ih => rw [pow_succ, Equiv.Perm.mul_apply, MulAction.toPerm_apply, ih, ← mul_smul, ← pow_succ]

theorem exists_phi_gam_eq_coboundary [Fintype Q] (φ : Additive Γ →+ ℤ) (M : SL(2, ℤ))
    (hM : ∀ (q : Q) (n : ℕ), 0 < n → M ^ n • q = q → φ (Additive.ofMul (gam (M ^ n) q)) = 0) :
    ∃ m : Q → ℤ, ∀ q, φ (Additive.ofMul (gam M q)) = m (M • q) - m q := by
  classical
  obtain ⟨m, hm⟩ := exists_eq_coboundary (MulAction.toPerm M)
    (fun q => φ (Additive.ofMul (gam M q))) (fun q n hn hq => by
      simp only [toPerm_pow_apply] at hq ⊢
      rw [sum_range_phi_gam, hM q n hn hq])
  exact ⟨m, fun q => by simpa using hm q⟩

theorem phi_eq_zero_of_pow_eq_one (φ : Additive Γ →+ ℤ) (γ : Γ) {k : ℕ} (hk : 0 < k)
    (h : γ ^ k = 1) : φ (Additive.ofMul γ) = 0 := by
  have : k • φ (Additive.ofMul γ) = 0 := by
    rw [← map_nsmul, ← ofMul_pow, h, ofMul_one, map_zero]
  simpa [hk.ne'] using this

theorem gam_pow_of_smul_eq (M : SL(2, ℤ)) (q : Q) (h : M • q = q) (k : ℕ) :
    ((gam M q ^ k : Γ) : SL(2, ℤ)) = (Quotient.out q)⁻¹ * M ^ k * Quotient.out q := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Subgroup.coe_mul, ih, coe_gam, h, pow_succ]
    group

theorem phi_gam_pow_eq_zero_of_torsion (φ : Additive Γ →+ ℤ) (M : SL(2, ℤ)) {k : ℕ} (hk : 0 < k)
    (hMk : M ^ k = 1) (q : Q) (n : ℕ) (hq : M ^ n • q = q) :
    φ (Additive.ofMul (gam (M ^ n) q)) = 0 := by
  apply phi_eq_zero_of_pow_eq_one φ _ hk
  ext1
  rw [gam_pow_of_smul_eq _ q hq, ← pow_mul, mul_comm, pow_mul, hMk, one_pow]
  simp

theorem phi_gam_T_pow_eq_zero (φ : Additive Γ →+ ℤ) (hφ : Period.IsParabolicHom Γ φ)
    (q : Q) (n : ℕ) (hq : ModularGroup.T ^ n • q = q) :
    φ (Additive.ofMul (gam (ModularGroup.T ^ n) q)) = 0 := by
  apply hφ
  rw [coe_gam, hq, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm,
    Matrix.SpecialLinearGroup.coe_mul, ← mul_assoc, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.mul_adjugate, Matrix.SpecialLinearGroup.det_coe, one_smul, one_mul]
  have : ((ModularGroup.T ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (n : ℤ); 0, 1] := by
    rw [← zpow_natCast]; exact ModularGroup.coe_T_zpow n
  rw [this, Matrix.trace_fin_two_of]
  norm_num

def W : SL(2, ℤ) := ModularGroup.T⁻¹ * ModularGroup.S

theorem coe_W : (W : Matrix (Fin 2) (Fin 2) ℤ) = !![-1, -1; 1, 0] := by
  rw [W, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_inv, ModularGroup.coe_S]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem W_pow_three : W ^ 3 = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_W]
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

theorem S_pow_two : ModularGroup.S ^ 2 = -1 := by
  ext1
  rw [Matrix.SpecialLinearGroup.coe_pow, pow_two, ModularGroup.S_mul_S_eq]
  simp

theorem S_pow_four : ModularGroup.S ^ 4 = 1 := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, S_pow_two]; simp

theorem neg_one_mem : (-1 : SL(2, ℤ)) ∈ Γ := hn.out

theorem neg_one_smul (q : Q) : (-1 : SL(2, ℤ)) • q = q := by
  induction q using QuotientGroup.induction_on with
  | H σ =>
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul]
    simpa using neg_one_mem (Γ := Γ)

theorem S_smul_S_smul (q : Q) : ModularGroup.S • ModularGroup.S • q = q := by
  rw [← mul_smul, ← pow_two, S_pow_two, neg_one_smul]

theorem trace_neg_one_sq : ((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.trace_neg,
    Matrix.trace_one]
  norm_num

theorem coe_gam_S_S_mul (q : Q) :
    ((gam ModularGroup.S (ModularGroup.S • q) * gam ModularGroup.S q : Γ) : SL(2, ℤ)) = -1 := by
  rw [← gam_mul, coe_gam, ← pow_two, S_pow_two, neg_one_smul]
  simp

theorem phi_gam_S_S (φ : Additive Γ →+ ℤ) (hφ : Period.IsParabolicHom Γ φ) (q : Q) :
    φ (Additive.ofMul (gam ModularGroup.S (ModularGroup.S • q))) =
      -φ (Additive.ofMul (gam ModularGroup.S q)) := by
  rw [eq_neg_iff_add_eq_zero, ← map_add, ← ofMul_mul]
  apply hφ
  rw [coe_gam_S_S_mul]
  exact trace_neg_one_sq

end Cocycle

theorem det_entries (γ : SL(2, ℤ)) :
    ((γ 0 0 : ℤ) : ℂ) * γ 1 1 - ((γ 0 1 : ℤ) : ℂ) * γ 1 0 = 1 := by
  have := γ.det_coe; rw [Matrix.det_fin_two] at this; exact_mod_cast this

theorem denom_eq (γ : SL(2, ℤ)) (z : ℂ) :
    denom γ z = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := by
  simp [denom]

theorem num_eq (γ : SL(2, ℤ)) (z : ℂ) :
    num γ z = ((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ) := by
  simp [num]

theorem denom_ne_zero' (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : denom γ z ≠ 0 :=
  UpperHalfPlane.denom_ne_zero_of_im γ hz.ne'

def mob (γ : SL(2, ℤ)) (z : ℂ) : ℂ := num γ z / denom γ z

theorem coe_smul (γ : SL(2, ℤ)) (τ : ℍ) : ((γ • τ : ℍ) : ℂ) = mob γ τ := by
  rw [ModularGroup.sl_moeb, coe_smul_of_det_pos (by simp)]; rfl

theorem hasDerivAt_denom (γ : SL(2, ℤ)) (z : ℂ) :
    HasDerivAt (denom (γ : GL (Fin 2) ℝ)) ((γ 1 0 : ℤ) : ℂ) z := by
  have : denom (γ : GL (Fin 2) ℝ) = fun z => ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) :=
    funext (denom_eq γ)
  rw [this]
  simpa using ((hasDerivAt_id z).const_mul ((γ 1 0 : ℤ) : ℂ)).add_const ((γ 1 1 : ℤ) : ℂ)

theorem hasDerivAt_num (γ : SL(2, ℤ)) (z : ℂ) :
    HasDerivAt (num (γ : GL (Fin 2) ℝ)) ((γ 0 0 : ℤ) : ℂ) z := by
  have : num (γ : GL (Fin 2) ℝ) = fun z => ((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ) :=
    funext (num_eq γ)
  rw [this]
  simpa using ((hasDerivAt_id z).const_mul ((γ 0 0 : ℤ) : ℂ)).add_const ((γ 0 1 : ℤ) : ℂ)

theorem hasDerivAt_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (mob γ) (1 / denom γ z ^ 2) z := by
  have hD := denom_ne_zero' γ hz
  have h := (hasDerivAt_num γ z).div (hasDerivAt_denom γ z) hD
  convert h using 1
  all_goals try rfl
  rw [num_eq, denom_eq, ← det_entries γ]
  simp only [denom_eq] at hD ⊢
  field_simp
  ring

theorem coe_smul_ofComplex (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    ((γ • ofComplex z : ℍ) : ℂ) = mob γ z := by
  rw [coe_smul, ofComplex_apply_of_im_pos hz]

def slashC (φ : ℍ → ℂ) (σ : SL(2, ℤ)) (z : ℂ) : ℂ :=
  φ (σ • ofComplex z) / denom (σ : GL (Fin 2) ℝ) (ofComplex z) ^ 2

theorem slashC_eq_slash (φ : ℍ → ℂ) (σ : SL(2, ℤ)) (z : ℂ) :
    slashC φ σ z = (φ ∣[(2 : ℤ)] σ) (ofComplex z) := by
  rw [slashC, ModularForm.SL_slash_apply, zpow_neg, div_eq_mul_inv]
  norm_cast

section CuspAnalytics

variable {Γ : Subgroup SL(2, ℤ)} (f : CuspForm Γ 2) (σ : SL(2, ℤ))

scoped instance isArithmetic_conj [Γ.FiniteIndex] :
    (ConjAct.toConjAct ((σ : GL (Fin 2) ℝ)⁻¹) •
      ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
  have h := Subgroup.IsArithmetic.conj ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
      (Matrix.SpecialLinearGroup.mapGL ℚ σ)⁻¹
  simp [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv,
    Matrix.SpecialLinearGroup.map_mapGL] at h
  exact h

def tr : CuspForm (ConjAct.toConjAct ((σ : GL (Fin 2) ℝ)⁻¹) •
    ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) 2 :=
  CuspForm.translate f (σ : GL (Fin 2) ℝ)

theorem coe_tr : ⇑(tr f σ) = (⇑f ∣[(2 : ℤ)] σ) := rfl

theorem slashC_eq_tr : slashC f σ = fun z => tr f σ (ofComplex z) := by
  funext z; rw [slashC_eq_slash, coe_tr]

theorem differentiableOn_slashC : DifferentiableOn ℂ (slashC f σ) {z : ℂ | 0 < z.im} := by
  rw [slashC_eq_tr]
  exact UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo (tr f σ))

theorem continuousOn_slashC : ContinuousOn (slashC f σ) {z : ℂ | 0 < z.im} :=
  (differentiableOn_slashC f σ).continuousOn

variable [Γ.FiniteIndex]

theorem tr_decay {a : ℝ} (ha : 0 < a) :
    ∃ c > 0, ∃ C, 0 ≤ C ∧ ∀ τ : ℍ, a ≤ τ.im → ‖tr f σ τ‖ ≤ C * Real.exp (-c * τ.im) := by
  obtain ⟨c, hc, hO⟩ := CuspFormClass.exp_decay_atImInfty' (tr f σ)
  obtain ⟨C₁, hC₁⟩ := hO.bound
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hC₁
  obtain ⟨C₂, hC₂⟩ := CuspFormClass.exists_bound (tr f σ)
  refine ⟨c, hc, max (max C₁ 0) (|C₂| / a * Real.exp (c * max A 0)), ?_, fun τ hτ => ?_⟩
  · exact le_max_of_le_left (le_max_right _ _)
  rcases le_or_gt A τ.im with h | h
  · have := hA τ h
    simp only [Set.mem_setOf_eq, Real.norm_eq_abs, Real.abs_exp] at this
    refine this.trans ?_
    gcongr
    exact le_max_of_le_left (le_max_left _ _)
  · have h2 := hC₂ τ
    have hk : ((2 : ℤ) : ℝ) / 2 = 1 := by norm_num
    rw [hk, Real.rpow_one] at h2
    have hpos := τ.im_pos
    calc ‖tr f σ τ‖ ≤ C₂ / τ.im := h2
      _ ≤ |C₂| / a := by
        rw [div_le_div_iff₀ hpos ha]
        calc C₂ * a ≤ |C₂| * a := by gcongr; exact le_abs_self _
          _ ≤ |C₂| * τ.im := by gcongr
      _ ≤ |C₂| / a * Real.exp (c * max A 0) * Real.exp (-c * τ.im) := by
        rw [mul_assoc, ← Real.exp_add]
        have : 0 ≤ c * max A 0 + -c * τ.im := by
          have : τ.im ≤ max A 0 := h.le.trans (le_max_left _ _)
          nlinarith
        calc |C₂| / a = |C₂| / a * 1 := (mul_one _).symm
          _ ≤ |C₂| / a * Real.exp (c * max A 0 + -c * τ.im) := by
            gcongr; exact Real.one_le_exp this
      _ ≤ _ := by gcongr; exact le_max_right _ _

theorem slashC_decay {a : ℝ} (ha : 0 < a) :
    ∃ c > 0, ∃ C, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.im → ‖slashC f σ z‖ ≤ C * Real.exp (-c * z.im) := by
  obtain ⟨c, hc, C, hC0, hC⟩ := tr_decay f σ ha
  refine ⟨c, hc, C, hC0, fun z hz => ?_⟩
  have hz0 : 0 < z.im := ha.trans_le hz
  have him : (ofComplex z).im = z.im := by rw [ofComplex_apply_of_im_pos hz0]; rfl
  have := hC (ofComplex z) (by rw [him]; exact hz)
  rw [him] at this
  simpa [slashC_eq_tr] using this

end CuspAnalytics

section Primitive

variable {U : ℍ → ℂ} {k : ℍ → ℂ} (σ : SL(2, ℤ))

def V (U : ℍ → ℂ) (σ : SL(2, ℤ)) (z : ℂ) : ℂ := U (σ • ofComplex z)

theorem V_eventuallyEq {z : ℂ} (hz : 0 < z.im) :
    V U σ =ᶠ[𝓝 z] (U ∘ ofComplex) ∘ mob σ := by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
  simp only [Function.comp_apply, V]
  rw [← coe_smul_ofComplex σ hw, ofComplex_apply]

theorem hasDerivAt_V (hU : ∀ τ : ℍ, HasDerivAt (U ∘ ofComplex) (k τ) τ) {z : ℂ}
    (hz : 0 < z.im) : HasDerivAt (V U σ) (slashC k σ z) z := by
  have h1 : HasDerivAt (U ∘ ofComplex) (k (σ • ofComplex z)) (mob σ z) := by
    have := hU (σ • ofComplex z); rwa [coe_smul_ofComplex σ hz] at this
  have h2 := (h1.comp z (hasDerivAt_mob σ hz)).congr_of_eventuallyEq (V_eventuallyEq σ hz)
  refine h2.congr_deriv ?_
  rw [slashC, mul_one_div, ofComplex_apply_of_im_pos hz]

end Primitive

section Edges

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (g : CuspForm Γ 2) {U : ℍ → ℂ}
  (σ : SL(2, ℤ))

theorem sqrt3_div_two_pos : (0 : ℝ) < Real.sqrt 3 / 2 := by positivity

theorem I_mul_integral_ray (hU : ∀ τ : ℍ, HasDerivAt (U ∘ ofComplex) (g τ) τ) {L : ℂ}
    (hL : Tendsto (fun w : ℍ => U (σ • w)) atImInfty (𝓝 L)) :
    Complex.I * ∫ y in Set.Ioi (Real.sqrt 3 / 2), slashC g σ (-(1 / 2) + y * Complex.I) =
      L - V U σ (-(1 / 2) + (Real.sqrt 3 / 2 : ℝ) * Complex.I) := by
  have him : ∀ y : ℝ, (-(1 / 2) + y * Complex.I : ℂ).im = y := fun y => by simp
  have hpath : ∀ y : ℝ, HasDerivAt (fun u : ℂ => (-(1 / 2) + u * Complex.I : ℂ)) Complex.I y :=
    fun y => by simpa using ((hasDerivAt_id (y : ℂ)).mul_const Complex.I).const_add (-(1 / 2) : ℂ)
  have hderiv : ∀ y : ℝ, 0 < y → HasDerivAt (fun y : ℝ => V U σ (-(1 / 2) + y * Complex.I))
      (slashC g σ (-(1 / 2) + y * Complex.I) * Complex.I) y := by
    intro y hy
    have h1 := hasDerivAt_V σ hU (z := -(1 / 2) + y * Complex.I) (by rw [him]; exact hy)
    exact (h1.comp (y : ℂ) (hpath y)).comp_ofReal
  have hcont : ContinuousWithinAt (fun y : ℝ => V U σ (-(1 / 2) + y * Complex.I))
      (Set.Ici (Real.sqrt 3 / 2)) (Real.sqrt 3 / 2) :=
    (hderiv _ sqrt3_div_two_pos).continuousAt.continuousWithinAt

  obtain ⟨c, hc, C, -, hC⟩ := slashC_decay g σ sqrt3_div_two_pos
  have hint : IntegrableOn (fun y : ℝ => slashC g σ (-(1 / 2) + y * Complex.I) * Complex.I)
      (Set.Ioi (Real.sqrt 3 / 2)) := by
    refine Integrable.mul_const ?_ _
    have hpc : Continuous fun y : ℝ => (-(1 / 2) + y * Complex.I : ℂ) := by fun_prop
    have hco : ContinuousOn (fun y : ℝ => slashC g σ (-(1 / 2) + y * Complex.I))
        (Set.Ioi (Real.sqrt 3 / 2)) :=
      (continuousOn_slashC g σ).comp hpc.continuousOn fun y hy => by
        show 0 < (-(1 / 2) + y * Complex.I : ℂ).im
        rw [him]; exact sqrt3_div_two_pos.trans hy
    refine Integrable.mono' ((exp_neg_integrableOn_Ioi _ hc).const_mul C)
      (hco.aestronglyMeasurable measurableSet_Ioi) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_
    have := hC (-(1 / 2) + y * Complex.I) (by rw [him]; exact le_of_lt hy)
    simpa using this

  have hlim : Tendsto (fun y : ℝ => V U σ (-(1 / 2) + y * Complex.I)) atTop (𝓝 L) := by
    have hto : Tendsto (fun y : ℝ => ofComplex (-(1 / 2) + y * Complex.I)) atTop atImInfty := by
      rw [atImInfty, tendsto_comap_iff]
      refine tendsto_id.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      simp only [Function.comp_apply, id]
      rw [ofComplex_apply_of_im_pos (by rw [him]; exact hy)]
      exact (him y).symm
    exact hL.comp hto
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun y hy => hderiv y (sqrt3_div_two_pos.trans hy)) hint hlim
  rw [integral_mul_const] at this
  rw [mul_comm, this]

theorem integral_arc (hU : ∀ τ : ℍ, HasDerivAt (U ∘ ofComplex) (g τ) τ) :
    ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
        slashC g σ (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I)) =
      V U σ (Complex.exp ((2 * Real.pi / 3 : ℝ) * Complex.I)) -
        V U σ (Complex.exp ((Real.pi / 3 : ℝ) * Complex.I)) := by
  have hmem : ∀ θ ∈ Set.uIcc (Real.pi / 3) (2 * Real.pi / 3),
      0 < (Complex.exp (θ * Complex.I)).im := by
    intro θ hθ
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
    rw [Complex.exp_ofReal_mul_I_im]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos, hθ.1])
      (by linarith [Real.pi_pos, hθ.2])
  have hpath : ∀ θ : ℝ, HasDerivAt (fun u : ℂ => Complex.exp (u * Complex.I))
      (Complex.exp (θ * Complex.I) * Complex.I) θ := fun θ => by
    simpa using ((hasDerivAt_id (θ : ℂ)).mul_const Complex.I).cexp
  have hderiv : ∀ θ ∈ Set.uIcc (Real.pi / 3) (2 * Real.pi / 3),
      HasDerivAt (fun θ : ℝ => V U σ (Complex.exp (θ * Complex.I)))
        (slashC g σ (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I))) θ := by
    intro θ hθ
    have h1 := hasDerivAt_V σ hU (hmem θ hθ)
    have := (h1.comp (θ : ℂ) (hpath θ)).comp_ofReal
    convert this using 1
    all_goals try rfl
    ring
  have hint : IntervalIntegrable (fun θ : ℝ => slashC g σ (Complex.exp (θ * Complex.I)) *
      (Complex.I * Complex.exp (θ * Complex.I))) volume (Real.pi / 3) (2 * Real.pi / 3) := by
    refine ContinuousOn.intervalIntegrable ?_
    have hpc : Continuous fun θ : ℝ => Complex.exp (θ * Complex.I) := by fun_prop
    have h2 : Continuous fun θ : ℝ => Complex.I * Complex.exp (θ * Complex.I) := by fun_prop
    exact ((continuousOn_slashC g σ).comp hpc.continuousOn hmem).mul h2.continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]

end Edges

section Corners

theorem exp_two_pi_div_three :
    Complex.exp ((2 * Real.pi / 3 : ℝ) * Complex.I) = -(1 / 2) + (Real.sqrt 3 / 2 : ℝ) * Complex.I := by
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
    simp
  · rw [Complex.exp_ofReal_mul_I_im, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.sin_pi_sub, Real.sin_pi_div_three]
    simp

theorem exp_pi_div_three :
    Complex.exp ((Real.pi / 3 : ℝ) * Complex.I) = (1 / 2) + (Real.sqrt 3 / 2 : ℝ) * Complex.I := by
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_three]; simp
  · rw [Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_three]; simp

def rho : ℍ := ⟨-(1 / 2) + (Real.sqrt 3 / 2 : ℝ) * Complex.I, by simp⟩

def rho' : ℍ := ⟨(1 / 2) + (Real.sqrt 3 / 2 : ℝ) * Complex.I, by simp⟩

@[scoped simp] theorem coe_rho : ((rho : ℍ) : ℂ) = -(1 / 2) + (Real.sqrt 3 / 2 : ℝ) * Complex.I := rfl
@[scoped simp] theorem coe_rho' : ((rho' : ℍ) : ℂ) = (1 / 2) + (Real.sqrt 3 / 2 : ℝ) * Complex.I := rfl

theorem ofComplex_rho : ofComplex (-(1 / 2) + (Real.sqrt 3 / 2 : ℝ) * Complex.I) = rho :=
  ofComplex_apply rho

theorem ofComplex_rho' : ofComplex ((1 / 2) + (Real.sqrt 3 / 2 : ℝ) * Complex.I) = rho' :=
  ofComplex_apply rho'

theorem ofComplex_exp_two_pi_div_three :
    ofComplex (Complex.exp ((2 * Real.pi / 3 : ℝ) * Complex.I)) = rho := by
  rw [exp_two_pi_div_three]; exact ofComplex_rho

theorem ofComplex_exp_pi_div_three :
    ofComplex (Complex.exp ((Real.pi / 3 : ℝ) * Complex.I)) = rho' := by
  rw [exp_pi_div_three]; exact ofComplex_rho'

theorem sqrt3_sq : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

theorem T_smul_rho : ModularGroup.T • rho = rho' := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd, coe_rho, coe_rho']
  push_cast; ring

theorem S_smul_rho' : ModularGroup.S • rho' = rho := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul, coe_rho]
  change (-((rho' : ℍ) : ℂ))⁻¹ = _
  rw [coe_rho', inv_eq_of_mul_eq_one_right]
  have := sqrt3_sq
  push_cast
  linear_combination (-Complex.I ^ 2 / 4) * this + (-3 / 4 : ℂ) * Complex.I_sq

theorem S_smul_rho : ModularGroup.S • rho = rho' := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul, coe_rho']
  change (-((rho : ℍ) : ℂ))⁻¹ = _
  rw [coe_rho, inv_eq_of_mul_eq_one_right]
  have := sqrt3_sq
  push_cast
  linear_combination (-Complex.I ^ 2 / 4) * this + (-3 / 4 : ℂ) * Complex.I_sq

theorem W_smul_rho : W • rho = rho := by
  rw [W, mul_smul, S_smul_rho, ← T_smul_rho, inv_smul_smul]

end Corners

section Limits

variable {U : ℍ → ℂ}

theorem im_T_inv_smul (w : ℍ) : (ModularGroup.T⁻¹ • w).im = w.im := by
  rw [show ModularGroup.T⁻¹ = ModularGroup.T ^ (-1 : ℤ) by simp, UpperHalfPlane.modular_T_zpow_smul,
    UpperHalfPlane.vadd_im]

theorem tendsto_T_inv_smul : Tendsto (fun w : ℍ => ModularGroup.T⁻¹ • w) atImInfty atImInfty := by
  rw [atImInfty, tendsto_comap_iff]
  have : UpperHalfPlane.im ∘ (fun w : ℍ => ModularGroup.T⁻¹ • w) = UpperHalfPlane.im :=
    funext im_T_inv_smul
  rw [this]
  exact tendsto_comap

theorem tendsto_comp_T_inv (σ : SL(2, ℤ)) {L : ℂ}
    (hL : Tendsto (fun w : ℍ => U (σ • w)) atImInfty (𝓝 L)) :
    Tendsto (fun w : ℍ => U ((σ * ModularGroup.T⁻¹) • w)) atImInfty (𝓝 L) := by
  simpa [mul_smul, Function.comp_def] using hL.comp tendsto_T_inv_smul

end Limits

section EdgesRead

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (g : CuspForm Γ 2) {U : ℍ → ℂ}
  (σ : SL(2, ℤ))

theorem I_mul_integral_ray' (hU : ∀ τ : ℍ, HasDerivAt (U ∘ ofComplex) (g τ) τ) {L : ℂ}
    (hL : Tendsto (fun w : ℍ => U (σ • w)) atImInfty (𝓝 L)) :
    Complex.I * ∫ y in Set.Ioi (Real.sqrt 3 / 2), slashC g σ (-(1 / 2) + y * Complex.I) =
      L - U (σ • rho) := by
  rw [I_mul_integral_ray g σ hU hL, V, ofComplex_rho]

theorem integral_arc' (hU : ∀ τ : ℍ, HasDerivAt (U ∘ ofComplex) (g τ) τ) :
    ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
        slashC g σ (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I)) =
      U (σ • rho) - U (σ • rho') := by
  rw [integral_arc g σ hU, V, V, ofComplex_exp_two_pi_div_three, ofComplex_exp_pi_div_three]

end EdgesRead

section Assembly

variable {Γ : Subgroup SL(2, ℤ)} [hn : Fact ((-1 : SL(2, ℤ)) ∈ Γ)]

local notation "Q" => SL(2, ℤ) ⧸ Γ

theorem out_inv_smul (M : SL(2, ℤ)) (q : Q) (τ : ℍ) :
    (Quotient.out (M • q))⁻¹ • τ =
      ((gam M q : Γ) : SL(2, ℤ)) • (Quotient.out q)⁻¹ • M⁻¹ • τ := by
  rw [← mul_smul, ← mul_smul, coe_gam]
  congr 1; group

theorem phi_gam_S_eq (φ : Additive Γ →+ ℤ) (q : Q) :
    φ (Additive.ofMul (gam ModularGroup.S q)) =
      φ (Additive.ofMul (gam W q)) + φ (Additive.ofMul (gam ModularGroup.T (W • q))) := by
  have h : ModularGroup.S = ModularGroup.T * W := by rw [W, mul_inv_cancel_left]
  conv_lhs => rw [h, gam_mul]
  rw [ofMul_mul, map_add, add_comm]

theorem zsmul_period_apply (m : ℤ) (γ : Γ) (g : CuspForm Γ 2) :
    (m • ModularCurve.periodOf Γ γ) g = (m : ℂ) * ModularCurve.periodOf Γ γ g := by
  rw [LinearMap.smul_apply, zsmul_eq_mul]

variable [Γ.FiniteIndex] (g : CuspForm Γ 2) {U : ℍ → ℂ}
  (hU : ModularCurve.HasEquivariantPrimitiveOf Γ g U)
include hU

theorem U_smul {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (τ : ℍ) :
    U (γ • τ) = U τ + ModularCurve.periodOf Γ ⟨γ, hγ⟩ g := by
  have h1 := hU.2.2.1.sub_eq_period ⟨γ, hγ⟩ τ
  have h2 := ModularCurve.periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf Γ g hU ⟨γ, hγ⟩
  rw [h2]
  change U (γ • τ) - U τ = U (γ • UpperHalfPlane.I) - U UpperHalfPlane.I at h1
  change U (γ • τ) = U τ + (U (γ • UpperHalfPlane.I) - U UpperHalfPlane.I)
  rw [← h1]; ring

theorem U_smul' (γ : Γ) (τ : ℍ) :
    U ((γ : SL(2, ℤ)) • τ) = U τ + ModularCurve.periodOf Γ γ g :=
  U_smul g hU γ.2 τ

theorem period_mul (γ δ : Γ) :
    ModularCurve.periodOf Γ (γ * δ) g = ModularCurve.periodOf Γ γ g + ModularCurve.periodOf Γ δ g := by
  have h1 := U_smul' g hU (γ * δ) UpperHalfPlane.I
  have h2 := U_smul' g hU γ ((δ : SL(2, ℤ)) • UpperHalfPlane.I)
  have h3 := U_smul' g hU δ UpperHalfPlane.I
  rw [Subgroup.coe_mul, mul_smul] at h1
  linear_combination -h1 + h2 + h3

theorem period_neg_one : ModularCurve.periodOf Γ ⟨-1, neg_one_mem⟩ g = 0 := by
  have h := U_smul g hU neg_one_mem UpperHalfPlane.I
  rw [ModularGroup.SL_neg_smul, one_smul] at h
  linear_combination -h

theorem period_gam_S_S (q : Q) :
    ModularCurve.periodOf Γ (gam ModularGroup.S (ModularGroup.S • q)) g =
      -ModularCurve.periodOf Γ (gam ModularGroup.S q) g := by
  have h := period_mul g hU (gam ModularGroup.S (ModularGroup.S • q)) (gam ModularGroup.S q)
  have h2 : gam ModularGroup.S (ModularGroup.S • q) * gam ModularGroup.S q = ⟨-1, neg_one_mem⟩ :=
    Subtype.ext (coe_gam_S_S_mul q)
  rw [h2, period_neg_one g hU] at h
  linear_combination -h

theorem U_out_inv_smul (M : SL(2, ℤ)) (q : Q) (τ : ℍ) :
    U ((Quotient.out (M • q))⁻¹ • τ) =
      U ((Quotient.out q)⁻¹ • M⁻¹ • τ) + ModularCurve.periodOf Γ (gam M q) g := by
  rw [out_inv_smul, U_smul' g hU]

theorem lim_T_smul {L : SL(2, ℤ) → ℂ}
    (hL : ∀ σ, Tendsto (fun w : ℍ => U (σ • w)) atImInfty (𝓝 (L σ))) (q : Q) :
    L (Quotient.out (ModularGroup.T • q))⁻¹ =
      L (Quotient.out q)⁻¹ + ModularCurve.periodOf Γ (gam ModularGroup.T q) g := by
  refine tendsto_nhds_unique (hL _) ?_
  have : (fun w : ℍ => U ((Quotient.out (ModularGroup.T • q))⁻¹ • w)) = fun w =>
      U ((Quotient.out q)⁻¹ • ModularGroup.T⁻¹ • w) +
        ModularCurve.periodOf Γ (gam ModularGroup.T q) g :=
    funext fun w => U_out_inv_smul g hU _ q w
  rw [this]
  exact ((hL _).comp tendsto_T_inv_smul).add_const _

end Assembly

end ModularCurve.PoincareDualIntegrality
p2m_reactivate "P2MW.S_ModularCurve_exists_mem_periodLatticeOf_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom.ModularCurve P2MW.S_ModularCurve_exists_mem_periodLatticeOf_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom.ModularCurve.PoincareDualIntegrality"
p2m_reactivate "P2MW.S_ModularCurve_exists_mem_periodLatticeOf_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_mem_periodLatticeOf_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom.ModularCurve P2MW.S_ModularCurve_exists_mem_periodLatticeOf_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom.ModularCurve.PoincareDualIntegrality"

open UpperHalfPlane MeasureTheory Filter ModularCurve.PoincareDualIntegrality
open scoped MatrixGroups Topology

theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    [Fintype (SL(2, ℤ) ⧸ Γ)]
    (γT γS : SL(2, ℤ) ⧸ Γ → Γ)
    (hT : ∀ q, ((γT q : Γ) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q)
    (hS : ∀ q, ((γS q : Γ) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q)
    (φ : Additive Γ →+ ℤ)
    (hφ : ModularCurve.Period.IsParabolicHom Γ φ) :
    ∃ Λ ∈ ModularCurve.periodLatticeOf Γ,
      ∀ (g : CuspForm Γ 2)
        (G : SL(2, ℤ) ⧸ Γ → ℂ → ℂ),
        (∀ q z, G q z = g ((Quotient.out q)⁻¹ • ofComplex z) /
          denom (((Quotient.out q)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2) →
        Complex.I * ∑ q : SL(2, ℤ) ⧸ Γ,
              ((φ (Additive.ofMul (γT q)) : ℤ) : ℂ) *
                (∫ y in Set.Ioi (Real.sqrt 3 / 2), G q (-(1 / 2) + y * Complex.I)) +
            1 / 2 * ∑ q : SL(2, ℤ) ⧸ Γ,
              ((φ (Additive.ofMul (γS q)) : ℤ) : ℂ) *
                (∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
                  G q (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I))) =
          Λ g := by
  classical
  haveI : Fact ((-1 : SL(2, ℤ)) ∈ Γ) := ⟨hneg⟩

  have hγT : ∀ q, γT q = gam ModularGroup.T q := fun q => Subtype.ext (hT q)
  have hγS : ∀ q, γS q = gam ModularGroup.S q := fun q => Subtype.ext (hS q)

  obtain ⟨mT, hmT⟩ := exists_phi_gam_eq_coboundary φ ModularGroup.T
    (fun q n _ hq => phi_gam_T_pow_eq_zero φ hφ q n hq)
  obtain ⟨mW, hmW⟩ := exists_phi_gam_eq_coboundary φ W
    (fun q n _ hq => phi_gam_pow_eq_zero_of_torsion φ W (by norm_num) W_pow_three q n hq)
  obtain ⟨mS, hmS⟩ := exists_phi_gam_eq_coboundary φ ModularGroup.S
    (fun q n _ hq => phi_gam_pow_eq_zero_of_torsion φ ModularGroup.S (by norm_num) S_pow_four q n hq)
  refine ⟨-(∑ q : SL(2, ℤ) ⧸ Γ,
        mT (ModularGroup.T • q) • ModularCurve.periodOf Γ (gam ModularGroup.T q)) -
      (∑ q : SL(2, ℤ) ⧸ Γ,
        (mW (W • q) + φ (Additive.ofMul (gam ModularGroup.T (W • q)))) •
          ModularCurve.periodOf Γ (gam W q)) -
      ∑ q : SL(2, ℤ) ⧸ Γ,
        mS q • ModularCurve.periodOf Γ (gam ModularGroup.S q), ?_, ?_⟩
  · refine sub_mem (sub_mem (neg_mem ?_) ?_) ?_ <;>
      exact sum_mem fun q _ => zsmul_mem (ModularCurve.periodOf_mem_periodLatticeOf Γ _) _
  intro g G hG
  obtain ⟨U, hU⟩ := ModularCurve.exists_hasEquivariantPrimitiveOf Γ g
  choose L hL using hU.2.2.2
  have hGf : ∀ q, G q = slashC g (Quotient.out q)⁻¹ := fun q => funext fun z => hG q z

  obtain ⟨ray, hray⟩ : ∃ ray : SL(2, ℤ) ⧸ Γ → ℂ, ∀ q,
      ray q = ∫ y in Set.Ioi (Real.sqrt 3 / 2), G q (-(1 / 2) + y * Complex.I) := ⟨_, fun _ => rfl⟩
  obtain ⟨arc, harc⟩ : ∃ arc : SL(2, ℤ) ⧸ Γ → ℂ, ∀ q,
      arc q = ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
        G q (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨aT, haT⟩ : ∃ aT : SL(2, ℤ) ⧸ Γ → ℂ, ∀ q,
      aT q = ((φ (Additive.ofMul (gam ModularGroup.T q)) : ℤ) : ℂ) := ⟨_, fun _ => rfl⟩
  obtain ⟨aS, haS⟩ : ∃ aS : SL(2, ℤ) ⧸ Γ → ℂ, ∀ q,
      aS q = ((φ (Additive.ofMul (gam ModularGroup.S q)) : ℤ) : ℂ) := ⟨_, fun _ => rfl⟩
  obtain ⟨aW, haW⟩ : ∃ aW : SL(2, ℤ) ⧸ Γ → ℂ, ∀ q,
      aW q = ((φ (Additive.ofMul (gam W q)) : ℤ) : ℂ) := ⟨_, fun _ => rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : SL(2, ℤ) ⧸ Γ → ℂ, ∀ q,
      x q = U ((Quotient.out q)⁻¹ • rho) := ⟨_, fun _ => rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : SL(2, ℤ) ⧸ Γ → ℂ, ∀ q,
      y q = U ((Quotient.out q)⁻¹ • rho') := ⟨_, fun _ => rfl⟩
  obtain ⟨Lq, hLq⟩ : ∃ Lq : SL(2, ℤ) ⧸ Γ → ℂ, ∀ q,
      Lq q = L (Quotient.out q)⁻¹ := ⟨_, fun _ => rfl⟩
  obtain ⟨PT, hPT⟩ : ∃ PT : SL(2, ℤ) ⧸ Γ → ℂ, ∀ q,
      PT q = ModularCurve.periodOf Γ (gam ModularGroup.T q) g := ⟨_, fun _ => rfl⟩
  obtain ⟨PW, hPW⟩ : ∃ PW : SL(2, ℤ) ⧸ Γ → ℂ, ∀ q,
      PW q = ModularCurve.periodOf Γ (gam W q) g := ⟨_, fun _ => rfl⟩
  obtain ⟨PS, hPS⟩ : ∃ PS : SL(2, ℤ) ⧸ Γ → ℂ, ∀ q,
      PS q = ModularCurve.periodOf Γ (gam ModularGroup.S q) g := ⟨_, fun _ => rfl⟩
  simp only [hγT, hγS, ← hray, ← harc, ← haT, ← haS, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.sum_apply, zsmul_period_apply, ← hPT, ← hPW, ← hPS]

  have hrayv : ∀ q, Complex.I * ray q = Lq q - x q := fun q => by
    rw [hray, hGf q, hLq, hx]; exact I_mul_integral_ray' g _ hU.1 (hL _)
  have harcv : ∀ q, arc q = x q - y q := fun q => by
    rw [harc, hGf q, hx, hy]; exact integral_arc' g _ hU.1
  have hxW : ∀ q, x (W • q) = x q + PW q := fun q => by
    rw [hx, hx, hPW, U_out_inv_smul g hU W q rho, inv_smul_eq_iff.mpr W_smul_rho.symm]
  have hxS : ∀ q, x (ModularGroup.S • q) = y q + PS q := fun q => by
    rw [hx, hy, hPS, U_out_inv_smul g hU ModularGroup.S q rho,
      inv_smul_eq_iff.mpr S_smul_rho'.symm]
  have hLT : ∀ q, Lq (ModularGroup.T • q) = Lq q + PT q := fun q => by
    rw [hLq, hLq, hPT]; exact lim_T_smul g hU hL q
  have hPSS : ∀ q, PS (ModularGroup.S • q) = -PS q := fun q => by
    rw [hPS, hPS]; exact period_gam_S_S g hU q
  have haSS : ∀ q, aS (ModularGroup.S • q) = -aS q := fun q => by
    rw [haS, haS, phi_gam_S_S φ hφ q, Int.cast_neg]
  have haSW : ∀ q, aS q = aW q + aT (W • q) := fun q => by
    rw [haS, haW, haT, phi_gam_S_eq φ q, Int.cast_add]
  have hcT : ∀ q, aT q = (mT (ModularGroup.T • q) : ℂ) - mT q := fun q => by
    rw [haT, hmT, Int.cast_sub]
  have hcW : ∀ q, aW q = (mW (W • q) : ℂ) - mW q := fun q => by
    rw [haW, hmW, Int.cast_sub]
  have hcS : ∀ q, aS q = (mS (ModularGroup.S • q) : ℂ) - mS q := fun q => by
    rw [haS, hmS, Int.cast_sub]

  have f1 : Complex.I * ∑ q, aT q * ray q = ∑ q, aT q * Lq q - ∑ q, aT q * x q := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [mul_left_comm, hrayv, mul_sub]
  have f2 : ∑ q, aS q * arc q =
      ∑ q, aS q * x q - ∑ q, aS q * x (ModularGroup.S • q) + ∑ q, aS q * PS q := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [harcv, hxS]; ring
  have fA : ∑ q, aT q * Lq q = -∑ q, (mT (ModularGroup.T • q) : ℂ) * PT q := by
    simpa only [MulAction.toPerm_apply] using
      sum_coboundary_mul (MulAction.toPerm ModularGroup.T) aT mT
        (fun q => by rw [MulAction.toPerm_apply]; exact hcT q) Lq PT
        (fun q => by rw [MulAction.toPerm_apply]; exact hLT q)
  have fD1 : ∑ q, aW q * x q = -∑ q, (mW (W • q) : ℂ) * PW q := by
    simpa only [MulAction.toPerm_apply] using
      sum_coboundary_mul (MulAction.toPerm W) aW mW
        (fun q => by rw [MulAction.toPerm_apply]; exact hcW q) x PW
        (fun q => by rw [MulAction.toPerm_apply]; exact hxW q)
  have fD2 : ∑ q, aT q * x q = ∑ q, aT (W • q) * x q + ∑ q, aT (W • q) * PW q := by
    rw [← Equiv.sum_comp (MulAction.toPerm W) (fun q => aT q * x q), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [MulAction.toPerm_apply]
    rw [hxW]; ring
  have fE : ∑ q, aS q * x q = ∑ q, aW q * x q + ∑ q, aT (W • q) * x q := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by rw [haSW, add_mul]
  have fB1 : ∑ q, aS q * x (ModularGroup.S • q) = -∑ q, aS q * x q := by
    rw [← Equiv.sum_comp (MulAction.toPerm ModularGroup.S) (fun q => aS q * x (ModularGroup.S • q)),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [MulAction.toPerm_apply]
    rw [S_smul_S_smul, haSS, neg_mul]
  have fC : ∑ q, aS q * PS q = -2 * ∑ q, (mS q : ℂ) * PS q := by
    have h1 : ∑ q, (mS (ModularGroup.S • q) : ℂ) * PS q = -∑ q, (mS q : ℂ) * PS q := by
      rw [← Equiv.sum_comp (MulAction.toPerm ModularGroup.S)
          (fun q => (mS (ModularGroup.S • q) : ℂ) * PS q), ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [MulAction.toPerm_apply]
      rw [S_smul_S_smul, hPSS, mul_neg]
    have h2 : ∑ q, aS q * PS q =
        ∑ q, (mS (ModularGroup.S • q) : ℂ) * PS q - ∑ q, (mS q : ℂ) * PS q := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun q _ => by rw [hcS, sub_mul]
    rw [h2, h1]; ring
  have fsplit : ∑ q, ((mW (W • q) + φ (Additive.ofMul (gam ModularGroup.T (W • q))) : ℤ) : ℂ) * PW q =
      ∑ q, (mW (W • q) : ℂ) * PW q + ∑ q, aT (W • q) * PW q := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by rw [Int.cast_add, ← haT, add_mul]
  linear_combination f1 + (1 / 2 : ℂ) * f2 + fA - fD2 + fE - (1 / 2 : ℂ) * fB1 +
    (1 / 2 : ℂ) * fC + fD1 + fsplit

end S_ModularCurve_exists_mem_periodLatticeOf_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom
end P2MW
export P2MW.S_ModularCurve_exists_mem_periodLatticeOf_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom (solution)
