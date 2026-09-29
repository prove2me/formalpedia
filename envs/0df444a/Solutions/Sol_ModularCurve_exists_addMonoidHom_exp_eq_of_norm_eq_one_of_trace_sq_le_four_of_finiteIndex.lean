-- Prove2me | solution 1 for ModularCurve.exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four_of_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/38b5af0a-22fe-58b0-a9f9-f4ee42dcc604

import Mathlib
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_ModularCurve_Period_exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four_of_finiteIndex

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups
open CongruenceSubgroup

namespace KbUnitaryCharExpOf

theorem mul_self_eq_trace_smul_sub_one (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1) :
    M * M = M.trace • M - 1 := by
  rw [Matrix.det_fin_two] at hdet
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.trace_fin_two, smul_eq_mul]
  fin_cases i <;> fin_cases j
  · simp; linear_combination (-1 : ℤ) * hdet
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, ne_eq, zero_ne_one, not_false_eq_true,
      Matrix.one_apply_ne, sub_zero]; ring
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, ne_eq, one_ne_zero, not_false_eq_true,
      Matrix.one_apply_ne, sub_zero]; ring
  · simp; linear_combination (-1 : ℤ) * hdet

theorem pow_twelve_eq_one (γ : SL(2, ℤ)) (h : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 < 4) :
    γ ^ 12 = 1 := by
  have hM := mul_self_eq_trace_smul_sub_one (γ : Matrix (Fin 2) (Fin 2) ℤ) γ.det_coe
  generalize ht : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = t at h hM
  have h1 : t < 2 := by nlinarith
  have h2 : -2 < t := by nlinarith
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  set M := (γ : Matrix (Fin 2) (Fin 2) ℤ)
  interval_cases t
  · have h3 : M ^ 3 = 1 := by
      rw [pow_succ, sq, hM]; simp only [neg_smul, one_smul, Int.reduceNeg]
      rw [sub_mul, neg_mul, hM]; simp
    rw [show (12 : ℕ) = 3 * 4 from rfl, pow_mul, h3, one_pow]
  · have h4 : M ^ 2 = -1 := by rw [sq, hM]; simp
    rw [show (12 : ℕ) = 2 * 6 from rfl, pow_mul, h4]; norm_num
  · have h3 : M ^ 3 = -1 := by
      rw [pow_succ, sq, hM]; simp only [one_smul]
      rw [sub_mul, hM]; simp
    rw [show (12 : ℕ) = 3 * 4 from rfl, pow_mul, h3]; norm_num

def cheb (t : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => t * cheb t (n + 1) - cheb t n

theorem pow_succ_eq_cheb (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1) (n : ℕ) :
    M ^ (n + 1) = cheb M.trace (n + 1) • M - cheb M.trace n • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [cheb]
    | 1, _ =>
      rw [show (1 + 1 : ℕ) = 2 from rfl, sq, mul_self_eq_trace_smul_sub_one M hdet]
      simp [cheb]
    | (k + 2), ih =>
      have h1 := ih (k + 1) (by omega)
      rw [show k + 1 + 1 = k + 2 from rfl] at h1
      have hc : cheb M.trace (k + 2 + 1) = M.trace * cheb M.trace (k + 2) - cheb M.trace (k + 1) := rfl
      rw [pow_succ, h1, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul,
        mul_self_eq_trace_smul_sub_one M hdet, smul_sub, smul_smul, hc]
      module

theorem abs_cheb_succ_ge (t : ℤ) (ht : 3 ≤ |t|) (n : ℕ) :
    |cheb t n| + 1 ≤ |cheb t (n + 1)| := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [cheb]
    | (k + 1), ih =>
      have h1 := ih k (by omega)
      have hrec : cheb t (k + 1 + 1) = t * cheb t (k + 1) - cheb t k := rfl
      rw [hrec]
      have h2 : |t| * |cheb t (k + 1)| - |cheb t k| ≤ |t * cheb t (k + 1) - cheb t k| := by
        rw [← abs_mul]
        exact abs_sub_abs_le_abs_sub _ _
      have h3 : 3 * |cheb t (k + 1)| ≤ |t| * |cheb t (k + 1)| :=
        mul_le_mul_of_nonneg_right ht (abs_nonneg _)
      have h0 : 0 ≤ |cheb t k| := abs_nonneg _
      linarith

theorem cheb_ne_zero (t : ℤ) (ht : 3 ≤ |t|) (n : ℕ) : cheb t (n + 1) ≠ 0 := by
  have h := abs_cheb_succ_ge t ht n
  have h0 : 0 ≤ |cheb t n| := abs_nonneg _
  intro hz
  rw [hz, abs_zero] at h
  linarith

theorem trace_sq_le_four_of_isOfFinOrder (γ : SL(2, ℤ)) (hγ : IsOfFinOrder γ) :
    ((γ : Matrix (Fin 2) (Fin 2) ℤ)).trace ^ 2 ≤ 4 := by
  by_contra hlt
  rw [not_le] at hlt
  set M := (γ : Matrix (Fin 2) (Fin 2) ℤ) with hM
  set t := M.trace with htdef
  have ht : 3 ≤ |t| := by
    by_contra h
    rw [not_le] at h
    have : t ^ 2 ≤ 4 := by
      rw [sq, ← abs_mul_abs_self]
      nlinarith [abs_nonneg t]
    exact absurd hlt (not_lt.mpr this)
  obtain ⟨m, hm, hγm⟩ := hγ.exists_pow_eq_one
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hpow : M ^ (n + 1) = 1 := by
    rw [hM, ← Matrix.SpecialLinearGroup.coe_pow, hγm, Matrix.SpecialLinearGroup.coe_one]
  rw [pow_succ_eq_cheb M γ.det_coe n] at hpow
  have hne := cheb_ne_zero t ht n

  have hent : ∀ i j : Fin 2,
      cheb t (n + 1) * M i j - cheb t n * (1 : Matrix (Fin 2) (Fin 2) ℤ) i j =
        (1 : Matrix (Fin 2) (Fin 2) ℤ) i j := by
    intro i j
    exact congrFun (congrFun hpow i) j
  have h01 : M 0 1 = 0 := by
    have h := hent 0 1
    simp only [Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), mul_zero, sub_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hne
  have h10 : M 1 0 = 0 := by
    have h := hent 1 0
    simp only [Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), mul_zero, sub_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hne
  have hdiag : M 0 0 = M 1 1 := by
    have h0 := hent 0 0
    have h1 := hent 1 1
    simp only [Matrix.one_apply_eq, mul_one] at h0 h1
    exact mul_left_cancel₀ hne (by linarith)
  have hdet : M 0 0 * M 1 1 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    rw [← hM, h01, h10] at this
    linarith
  have htr : t = M 0 0 + M 1 1 := by rw [htdef, Matrix.trace_fin_two]
  rw [← hdiag] at hdet
  rcases mul_self_eq_one_iff.mp hdet with h1 | h1
  · rw [htr, ← hdiag, h1] at ht; norm_num at ht
  · rw [htr, ← hdiag, h1] at ht; norm_num at ht

variable (Γ : Subgroup SL(2, ℤ))

def Ell : Set Γ := {γ | ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4}

def Msub : Subgroup (Abelianization Γ) :=
  Subgroup.closure (Abelianization.of '' Ell Γ)

abbrev Qm := Abelianization Γ ⧸ Msub Γ

abbrev Q := Additive (Qm Γ)

def piM : Γ →* Qm Γ := (QuotientGroup.mk' (Msub Γ)).comp Abelianization.of

def piA : Additive Γ →+ Q Γ := MonoidHom.toAdditive (piM Γ)

theorem piM_surjective : Function.Surjective (piM Γ) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H a =>
    induction a using QuotientGroup.induction_on with
    | H g => exact ⟨g, rfl⟩

theorem piA_surjective : Function.Surjective (piA Γ) := fun q =>
  let ⟨g, hg⟩ := piM_surjective Γ (Additive.toMul q); ⟨Additive.ofMul g, hg⟩

theorem piM_eq_one {γ : Γ} (hγ : γ ∈ Ell Γ) : piM Γ γ = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_closure ⟨γ, hγ, rfl⟩)

theorem piA_apply (γ : Γ) : piA Γ (Additive.ofMul γ) = Additive.ofMul (piM Γ γ) := rfl

theorem piA_eq_zero {γ : Γ} (hγ : γ ∈ Ell Γ) : piA Γ (Additive.ofMul γ) = 0 := by
  rw [piA_apply, piM_eq_one Γ hγ]; rfl

variable {Γ} in

def desc {A : Type*} [CommGroup A] (f : Γ →* A) (hf : ∀ γ ∈ Ell Γ, f γ = 1) : Qm Γ →* A :=
  QuotientGroup.lift (Msub Γ) (Abelianization.lift f) ((Subgroup.closure_le _).mpr (by
    rintro _ ⟨γ, hγ, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, Abelianization.lift_apply_of, hf γ hγ]))

theorem desc_piM {A : Type*} [CommGroup A] (f : Γ →* A) (hf : ∀ γ ∈ Ell Γ, f γ = 1)
    (γ : Γ) : desc f hf (piM Γ γ) = f γ := rfl

variable {Γ} in

def descA {A : Type*} [AddCommGroup A] (φ : Additive Γ →+ A)
    (hφ : ∀ γ ∈ Ell Γ, φ (Additive.ofMul γ) = 0) : Q Γ →+ A :=
  MonoidHom.toAdditiveLeft (desc (AddMonoidHom.toMultiplicativeRight φ) hφ)

theorem descA_piA {A : Type*} [AddCommGroup A] (φ : Additive Γ →+ A)
    (hφ : ∀ γ ∈ Ell Γ, φ (Additive.ofMul γ) = 0) (γ : Γ) :
    descA φ hφ (piA Γ (Additive.ofMul γ)) = φ (Additive.ofMul γ) := rfl

theorem fg_SL2Z : Group.FG SL(2, ℤ) :=
  Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T},
    _root_.SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩

scoped instance fgQ [Γ.FiniteIndex] : AddGroup.FG (Q Γ) := by
  haveI := fg_SL2Z
  haveI : Group.FG Γ := inferInstance
  haveI : Group.FG (Qm Γ) := Group.fg_of_surjective (piM_surjective Γ)
  infer_instance

theorem apply_eq_zero_of_nsmul_eq_zero {A : Type*} [AddGroup A] (ψ : A →+ ℝ) {x : A} {m : ℕ}
    (hm : m ≠ 0) (hx : m • x = 0) : ψ x = 0 := by
  have h : (m : ℝ) * ψ x = 0 := by rw [← nsmul_eq_mul, ← map_nsmul, hx, map_zero]
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h (Nat.cast_ne_zero.mpr hm)
  · exact h

section Decomp

variable {Γ} [Γ.FiniteIndex]
variable {n : ℕ} {ι : Type} [Fintype ι] {p e : ι → ℕ}
  (eqv : Q Γ ≃+ (Fin n →₀ ℤ) × DirectSum ι (fun i => ZMod (p i ^ e i)))

omit [Fintype ι] in

theorem hom_ext_of_basis {A : Type*} [AddCommGroup A] (ψ₁ ψ₂ : Q Γ →+ A)
    (hb : ∀ j, ψ₁ (eqv.symm (Finsupp.single j 1, 0)) = ψ₂ (eqv.symm (Finsupp.single j 1, 0)))
    (ht : ∀ t, ψ₁ (eqv.symm (0, t)) = ψ₂ (eqv.symm (0, t))) : ψ₁ = ψ₂ := by
  have hfree : ψ₁.comp (eqv.symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)) =
      ψ₂.comp (eqv.symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)) := by
    refine Finsupp.addHom_ext' fun j => AddMonoidHom.ext_int ?_
    simpa using hb j
  refine AddMonoidHom.ext fun q => ?_
  obtain ⟨⟨v, t⟩, rfl⟩ := eqv.symm.surjective q
  have hsplit : ((v, t) : (Fin n →₀ ℤ) × DirectSum ι (fun i => ZMod (p i ^ e i))) =
      (v, 0) + (0, t) := by simp
  rw [hsplit, map_add, map_add, map_add, ht t]
  congr 1
  exact DFunLike.congr_fun hfree v

theorem realChar_eq_zero (hp : ∀ i, (p i).Prime) (ψ : Q Γ →+ ℝ)
    (hψ : ∀ j, ψ (eqv.symm (Finsupp.single j 1, 0)) = 0) : ψ = 0 := by
  classical
  haveI : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  haveI : Finite (DirectSum ι fun i => ZMod (p i ^ e i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  refine hom_ext_of_basis eqv ψ 0 (by simpa using hψ) fun t => ?_
  obtain ⟨m, hm, hmt⟩ := (isOfFinAddOrder_of_finite t).exists_nsmul_eq_zero
  rw [AddMonoidHom.zero_apply]
  refine apply_eq_zero_of_nsmul_eq_zero _ hm.ne' ?_
  rw [← map_nsmul, Prod.smul_mk, smul_zero, hmt, Prod.mk_zero_zero, map_zero]

end Decomp

def unitChar (χ : Γ → ℂ) (hmul : ∀ γ δ, χ (γ * δ) = χ γ * χ δ)
    (hunit : ∀ γ, ‖χ γ‖ = 1) : Γ →* Circle where
  toFun γ := ⟨χ γ, mem_sphere_zero_iff_norm.2 (hunit γ)⟩
  map_one' := Circle.ext (by
    have h1 : χ 1 ≠ 0 := fun h => by simpa [h] using hunit 1
    have h2 : χ 1 * χ 1 = χ 1 * 1 := by rw [mul_one, ← hmul, one_mul]
    rw [Circle.coe_one]
    exact (mul_right_inj' h1).mp h2)
  map_mul' γ δ := Circle.ext (by rw [Circle.coe_mul]; exact hmul γ δ)

theorem unitChar_apply (χ : Γ → ℂ) (hmul : ∀ γ δ, χ (γ * δ) = χ γ * χ δ)
    (hunit : ∀ γ, ‖χ γ‖ = 1) (γ : Γ) : (unitChar Γ χ hmul hunit γ : ℂ) = χ γ := rfl

theorem main [Γ.FiniteIndex] (χ : Γ → ℂ) (hmul : ∀ γ δ, χ (γ * δ) = χ γ * χ δ)
    (hunit : ∀ γ, ‖χ γ‖ = 1)
    (htriv : ∀ γ : Γ,
      ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 → χ γ = 1) :
    ∃ φ : Additive Γ →+ ℝ,
      (∀ γ : Γ, ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 →
        φ (Additive.ofMul γ) = 0) ∧
      ∀ γ, χ γ = Complex.exp (2 * Real.pi * Complex.I * (φ (Additive.ofMul γ) : ℂ)) := by
  classical
  obtain ⟨n, ι, _, p, hp, e, ⟨eqv⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod (Q Γ)

  have he : ∀ i, e i = 0 := by
    by_contra hne
    obtain ⟨i₀, hi₀⟩ := not_forall.mp hne
    haveI : Fact (1 < p i₀ ^ e i₀) := ⟨Nat.one_lt_pow hi₀ (hp i₀).one_lt⟩

    let tcrd : Q Γ →+ ZMod (p i₀ ^ e i₀) :=
      (DirectSum.component ℤ ι (fun i => ZMod (p i ^ e i)) i₀).toAddMonoidHom.comp
        ((AddMonoidHom.snd _ _).comp eqv.toAddMonoidHom)
    let Φ : Additive Γ →+ ZMod (p i₀ ^ e i₀) := tcrd.comp (piA Γ)
    have hΦEll : ∀ γ ∈ Ell Γ, Φ (Additive.ofMul γ) = 0 := by
      intro γ hγ
      simp [Φ, piA_eq_zero Γ hγ]
    have hΦpar : ModularCurve.Period.IsParabolicHom Γ Φ := fun γ hγ => hΦEll γ (le_of_eq hγ)
    have hΦfin : ∀ γ : Γ, IsOfFinOrder γ → Φ (Additive.ofMul γ) = 0 := by
      intro γ hγ
      refine hΦEll γ ?_
      exact trace_sq_le_four_of_isOfFinOrder (γ : SL(2, ℤ)) (Γ.subtype.isOfFinOrder hγ)

    obtain ⟨x, hx⟩ :=
      ModularCurve.Period.exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder Γ
        (p i₀ ^ e i₀) ⟨Φ, ModularCurve.Period.mem_parabolicHoms_iff.mpr hΦpar⟩ hΦfin

    have hxEll : ∀ γ ∈ Ell Γ, (x : Additive Γ →+ ℤ) (Additive.ofMul γ) = 0 := by
      intro γ hγ
      rcases (show ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 from hγ).lt_or_eq with
        hlt | heq
      · have h12 : γ ^ 12 = 1 := Subtype.ext (by
          rw [Subgroup.coe_pow, Subgroup.coe_one]; exact pow_twelve_eq_one _ hlt)
        have h : (x : Additive Γ →+ ℤ) (Additive.ofMul (γ ^ 12)) =
            12 • (x : Additive Γ →+ ℤ) (Additive.ofMul γ) := by
          rw [ofMul_pow, map_nsmul]
        rw [h12, ofMul_one, map_zero] at h
        simpa using h.symm
      · exact (ModularCurve.Period.mem_parabolicHoms_iff.mp x.2) γ heq

    obtain ⟨g₀, hg₀⟩ :=
      piA_surjective Γ (eqv.symm (0, DirectSum.of (fun i => ZMod (p i ^ e i)) i₀ 1))
    have htor : (p i₀ ^ e i₀) • piA Γ g₀ = 0 := by
      rw [hg₀, ← map_nsmul, Prod.smul_mk, smul_zero,
        ← map_nsmul (DirectSum.of (fun i => ZMod (p i ^ e i)) i₀) (p i₀ ^ e i₀) (1 : ZMod (p i₀ ^ e i₀)),
        nsmul_eq_mul, mul_one, ZMod.natCast_self, map_zero, Prod.mk_zero_zero, map_zero]
    have hx0 : (x : Additive Γ →+ ℤ) g₀ = 0 := by
      have h := congrArg (descA (x : Additive Γ →+ ℤ) hxEll) htor
      rw [map_nsmul, map_zero] at h
      have h' : (p i₀ ^ e i₀) • (x : Additive Γ →+ ℤ) g₀ = 0 := h
      rw [nsmul_eq_mul, mul_eq_zero] at h'
      rcases h' with h' | h'
      · exact absurd (by exact_mod_cast h' : p i₀ ^ e i₀ = 0) (pow_ne_zero _ (hp i₀).ne_zero)
      · exact h'
    have hΦg : Φ g₀ = 1 := by
      simp [Φ, tcrd, hg₀, ← DirectSum.apply_eq_component, DirectSum.of_eq_same]
    have hΦg' : Φ g₀ = 0 := by
      have h := DFunLike.congr_fun hx g₀
      simp only [AddMonoidHom.coe_comp, Function.comp_apply] at h
      rw [← h, hx0, map_zero]
    rw [hΦg'] at hΦg
    exact zero_ne_one hΦg
  have hsub : ∀ i, Subsingleton (ZMod (p i ^ e i)) := fun i =>
    ZMod.subsingleton_iff.mpr (by rw [he i, pow_zero])
  have htors : ∀ t : DirectSum ι (fun i => ZMod (p i ^ e i)), t = 0 := fun t =>
    DFinsupp.ext fun i => Subsingleton.elim _ _

  set χc := unitChar Γ χ hmul hunit with hχc_def
  have hχc : ∀ γ ∈ Ell Γ, χc γ = 1 := fun γ hγ =>
    Circle.ext (by rw [unitChar_apply, Circle.coe_one]; exact htriv γ hγ)
  let χQ : Q Γ →+ Additive Circle := MonoidHom.toAdditive (desc χc hχc)

  choose θ hθ using fun j : Fin n =>
    Circle.exp_surjective (Additive.toMul (χQ (eqv.symm (Finsupp.single j 1, 0))))
  let ψ : Q Γ →+ ℝ :=
    { toFun := fun q => ∑ j, ((eqv q).1 j : ℝ) * θ j
      map_zero' := by simp
      map_add' := fun a b => by simp [Finset.sum_add_distrib, add_mul] }
  have hψb : ∀ j, ψ (eqv.symm (Finsupp.single j 1, 0)) = θ j := by
    intro j
    simp [ψ, Finsupp.single_apply]
  have hfactor : χQ = Circle.expHom.comp ψ := by
    refine hom_ext_of_basis eqv _ _ (fun j => ?_) (fun t => ?_)
    · rw [AddMonoidHom.comp_apply, hψb, Circle.expHom_apply, Function.comp_apply, hθ]
      rfl
    · rw [htors t, Prod.mk_zero_zero, map_zero, map_zero, map_zero]
  refine ⟨(AddMonoidHom.mulLeft (1 / (2 * Real.pi))).comp (ψ.comp (piA Γ)), fun γ hγ => ?_,
    fun γ => ?_⟩
  · simp [piA_eq_zero Γ hγ]
  · have h1 : χ γ = ((desc χc hχc (piM Γ γ) : Circle) : ℂ) := rfl
    have h2 : desc χc hχc (piM Γ γ) = Circle.exp (ψ (piA Γ (Additive.ofMul γ))) := by
      have h := DFunLike.congr_fun hfactor (piA Γ (Additive.ofMul γ))
      exact Additive.ofMul.injective h
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [h1, h2, Circle.coe_exp]
    congr 1
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft]
    push_cast
    field_simp

end KbUnitaryCharExpOf
p2m_reactivate "P2MW.S_ModularCurve_exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four_of_finiteIndex.KbUnitaryCharExpOf"

theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (χ : Γ → ℂ)
    (hmul : ∀ γ δ, χ (γ * δ) = χ γ * χ δ) (hunit : ∀ γ, ‖χ γ‖ = 1)
    (htriv : ∀ γ : Γ,
      ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 → χ γ = 1) :
    ∃ φ : Additive Γ →+ ℝ,
      (∀ γ : Γ,
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 → φ (Additive.ofMul γ) = 0) ∧
      ∀ γ, χ γ = Complex.exp (2 * Real.pi * Complex.I * (φ (Additive.ofMul γ) : ℂ)) :=
  KbUnitaryCharExpOf.main Γ χ hmul hunit htriv

end S_ModularCurve_exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four_of_finiteIndex
end P2MW
export P2MW.S_ModularCurve_exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four_of_finiteIndex (solution)
