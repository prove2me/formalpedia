-- Prove2me | solution 1 for LiouvilleDiffAlg.inv_X_antideriv_logExtension
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T13:08:10.079094+00:00
-- url     : https://prove2.me/submissions/e5b30e36-b554-4dc5-adca-a834f9d40bd5

import Mathlib
import Definitions.Def_LiouvilleDiffAlg_Basic
import Definitions.Def_LiouvilleDiffAlg_RatFunc
import Theorems.Thm_LiouvilleDiffAlg_inv_X_no_antideriv
import Theorems.Thm_LiouvilleDiffAlg_constants_ratFunc

open scoped Differential
open Polynomial
open LiouvilleDiffAlg

attribute [local instance 2000] Ring.toIntAlgebra

section Construction

variable {K : Type*} [Field K] [Differential K]

/-- the ring map `p ↦ p + (D̃ p) ε` into the dual numbers over `K(T)` -/
private noncomputable def dualHom (w : K) :
    K[X] →+* TrivSqZeroExt (RatFunc K) (RatFunc K) where
  toFun p := TrivSqZeroExt.inl (algebraMap _ (RatFunc K) p) +
    TrivSqZeroExt.inr (algebraMap _ (RatFunc K)
      (Differential.implicitDeriv (Polynomial.C w) p))
  map_one' := by
    apply TrivSqZeroExt.ext <;>
      simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_one,
        Derivation.map_one_eq_zero, map_zero, TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one,
        add_zero, zero_add]
  map_zero' := by
    apply TrivSqZeroExt.ext <;>
      simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_zero,
        TrivSqZeroExt.fst_zero, TrivSqZeroExt.snd_zero, add_zero, zero_add]
  map_add' p q := by
    apply TrivSqZeroExt.ext <;>
      simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_add] <;> ring
  map_mul' p q := by
    apply TrivSqZeroExt.ext
    · simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, map_mul, add_zero]
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr,
        TrivSqZeroExt.snd_inr, Derivation.leibniz, map_add, map_mul, smul_eq_mul,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, add_zero, zero_add]
      ring

private lemma dualHom_fst (w : K) (p : K[X]) :
    (dualHom w p).fst = algebraMap _ (RatFunc K) p := by
  simp only [dualHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.fst_add,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]

private lemma dualHom_snd (w : K) (p : K[X]) :
    (dualHom w p).snd =
      algebraMap _ (RatFunc K) (Differential.implicitDeriv (Polynomial.C w) p) := by
  simp only [dualHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add,
    TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]

private lemma dualHom_unit (w : K) (y : nonZeroDivisors K[X]) : IsUnit (dualHom w y) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, dualHom_fst]
  refine isUnit_iff_ne_zero.2 ?_
  rw [map_ne_zero_iff _ (RatFunc.algebraMap_injective K)]
  exact nonZeroDivisors.coe_ne_zero y

private noncomputable def dualLift (w : K) :
    RatFunc K →+* TrivSqZeroExt (RatFunc K) (RatFunc K) :=
  IsLocalization.lift (M := nonZeroDivisors K[X]) (dualHom_unit w)

private lemma dualLift_algebraMap (w : K) (p : K[X]) :
    dualLift w (algebraMap _ (RatFunc K) p) = dualHom w p :=
  IsLocalization.lift_eq _ _

private lemma dualLift_fst (w : K) (x : RatFunc K) : (dualLift w x).fst = x := by
  have : ((TrivSqZeroExt.fstHom K (RatFunc K) (RatFunc K)).toRingHom.comp (dualLift w)) =
      RingHom.id (RatFunc K) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors K[X])
    refine RingHom.ext fun p => ?_
    simp only [RingHom.comp_apply, dualLift_algebraMap]
    exact dualHom_fst w p
  exact congrArg (fun f => f x) this

set_option warn.classDefReducibility false in
/-- the derivation on `K(T)` extending that of `K` with `T′ = w` -/
private noncomputable def logDiff (w : K) : Differential (RatFunc K) where
  deriv := Derivation.mk'
    { toFun := fun x => (dualLift w x).snd
      map_add' := fun x y => by simp only [map_add, TrivSqZeroExt.snd_add]
      map_smul' := fun n x => by
        simp only [map_zsmul, TrivSqZeroExt.snd_smul, RingHom.id_apply] }
    (fun a b => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, map_mul, TrivSqZeroExt.snd_mul,
        dualLift_fst, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      ring)

private lemma logDiff_poly (w : K) (p : K[X]) :
    (logDiff w).deriv (algebraMap _ (RatFunc K) p) =
      algebraMap _ (RatFunc K) (Differential.implicitDeriv (Polynomial.C w) p) := by
  show (dualLift w (algebraMap _ (RatFunc K) p)).snd = _
  rw [dualLift_algebraMap, dualHom_snd]

end Construction

section Constants

variable {K : Type*} [Field K] [Differential K] [CharZero K]

private lemma coeff_implicitDeriv (w : K) (p : K[X]) (k : ℕ) :
    (Differential.implicitDeriv (Polynomial.C w) p).coeff k =
      (p.coeff k)′ + w * (((k : K) + 1) * p.coeff (k + 1)) := by
  simp only [Differential.implicitDeriv, Derivation.coe_add, Pi.add_apply,
    Polynomial.coeff_add, Differential.coeff_mapCoeffs]
  congr 1
  simp [Polynomial.coeff_derivative]
  exact Or.inl (mul_comm _ _)

/-- a polynomial annihilated by `D̃` is a constant polynomial with constant coefficient -/
private lemma implicitDeriv_eq_zero (w : K) (hw : ¬ ∃ g : K, g′ = w) (p : K[X])
    (hp : Differential.implicitDeriv (Polynomial.C w) p = 0) :
    ∃ a : K, a′ = 0 ∧ p = Polynomial.C a := by
  have hc : ∀ k, (p.coeff k)′ + w * (((k : K) + 1) * p.coeff (k + 1)) = 0 := by
    intro k
    have := congrArg (fun q => q.coeff k) hp
    simpa [coeff_implicitDeriv] using this
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · refine ⟨p.coeff 0, ?_, Polynomial.eq_C_of_natDegree_eq_zero h0⟩
    have h1 := hc 0
    have h2 : p.coeff 1 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simpa [h2] using h1
  · exfalso
    obtain ⟨e, he⟩ : ∃ e, p.natDegree = e + 1 := ⟨p.natDegree - 1, by omega⟩
    have hlead : p.coeff (e + 1) ≠ 0 := by
      have : p ≠ 0 := by
        rintro rfl; simp at hpos
      have := Polynomial.leadingCoeff_ne_zero.2 this
      rwa [Polynomial.leadingCoeff, he] at this
    have h2 : p.coeff (e + 1 + 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hl : (p.coeff (e + 1))′ = 0 := by
      have := hc (e + 1)
      simpa [h2] using this
    have he1 := hc e
    have hne : ((e : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero e
    apply hw
    refine ⟨-(p.coeff e) / (((e : K) + 1) * p.coeff (e + 1)), ?_⟩
    have hden : ((((e : K) + 1) * p.coeff (e + 1)))′ = 0 := by
      simp [Derivation.leibniz, hl]
    rw [Derivation.leibniz_div_const _ _ _ hden, map_neg]
    simp only [smul_eq_mul]
    have : (p.coeff e)′ = -(w * (((e : K) + 1) * p.coeff (e + 1))) := by
      linear_combination he1
    rw [this]
    field_simp

/-- the constants of `K(T)` (for `T′ = w` with `w` not a derivative in `K`) lie in `K` -/
private lemma logDiff_consts (w : K) (hw : ¬ ∃ g : K, g′ = w) (x : RatFunc K)
    (hx : (logDiff w).deriv x = 0) :
    ∃ a : K, a′ = 0 ∧ x = algebraMap K (RatFunc K) a := by
  set A := x.num with hA
  set B := x.denom with hB
  have hBm : B.Monic := RatFunc.monic_denom x
  have hB0 : B ≠ 0 := hBm.ne_zero
  have hden : algebraMap _ (RatFunc K) B ≠ 0 := by
    rw [map_ne_zero_iff _ (RatFunc.algebraMap_injective K)]
    exact hB0
  have h0 : x * algebraMap _ (RatFunc K) B = algebraMap _ (RatFunc K) A := by
    have := RatFunc.num_div_denom x
    rw [div_eq_iff hden] at this
    exact this.symm
  have h1 := congrArg (logDiff w).deriv h0
  rw [Derivation.leibniz, hx, logDiff_poly, logDiff_poly] at h1
  simp only [smul_zero, zero_add, smul_eq_mul] at h1
  -- `D̃ A * B = A * D̃ B`
  have h2 : algebraMap _ (RatFunc K) (Differential.implicitDeriv (Polynomial.C w) A * B) =
      algebraMap _ (RatFunc K) (A * Differential.implicitDeriv (Polynomial.C w) B) := by
    rw [map_mul, map_mul, ← h1, ← h0]
    ring
  have h3 := RatFunc.algebraMap_injective K h2
  have hcop : IsCoprime A B := x.isCoprime_num_denom
  have hdvd : B ∣ Differential.implicitDeriv (Polynomial.C w) B :=
    hcop.symm.dvd_of_dvd_mul_left ⟨Differential.implicitDeriv (Polynomial.C w) A, by
      rw [← h3]; ring⟩
  have hlt : (Differential.implicitDeriv (Polynomial.C w) B).degree < B.degree := by
    rw [Polynomial.degree_eq_natDegree hB0, Polynomial.degree_lt_iff_coeff_zero]
    intro m hm
    rw [coeff_implicitDeriv]
    rcases Nat.eq_or_lt_of_le hm with rfl | hlt'
    · have h4 : B.coeff (B.natDegree + 1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [h4, hBm.coeff_natDegree]
    · have h4 : B.coeff m = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hlt'
      have h5 : B.coeff (m + 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [h4, h5]
  have hDB : Differential.implicitDeriv (Polynomial.C w) B = 0 :=
    Polynomial.eq_zero_of_dvd_of_degree_lt hdvd hlt
  have hDA : Differential.implicitDeriv (Polynomial.C w) A = 0 := by
    rw [hDB, mul_zero] at h3
    exact (mul_eq_zero.1 h3).resolve_right hB0
  obtain ⟨a, ha, hAa⟩ := implicitDeriv_eq_zero w hw A hDA
  obtain ⟨b, hb, hBb⟩ := implicitDeriv_eq_zero w hw B hDB
  have hb0 : b ≠ 0 := by
    rintro rfl; apply hB0; rw [hBb]; simp
  refine ⟨a / b, ?_, ?_⟩
  · rw [Derivation.leibniz_div_const _ _ _ hb, ha]; simp
  · have hxa : x = algebraMap _ (RatFunc K) A / algebraMap _ (RatFunc K) B :=
      (RatFunc.num_div_denom x).symm
    rw [hxa, hAa, hBb, RatFunc.algebraMap_C, RatFunc.algebraMap_C, map_div₀]
    rfl

end Constants

theorem solution [Differential (RatFunc ℂ)] (hD : IsStandardDerivation) :
    ∃ (G : Type) (_ : Field G) (_ : Differential G) (_ : Algebra (RatFunc ℂ) G)
      (_ : DifferentialAlgebra (RatFunc ℂ) G) (t : G),
      IntermediateField.adjoin (RatFunc ℂ) {t} = ⊤ ∧ Transcendental (RatFunc ℂ) t ∧
      t′ = (algebraMap (RatFunc ℂ) G RatFunc.X)′ / algebraMap (RatFunc ℂ) G RatFunc.X ∧
      ∀ g : G, g′ = algebraMap (RatFunc ℂ) G (1 / RatFunc.X) ↔
        ∃ c : ℂ, g = t + algebraMap (RatFunc ℂ) G (algebraMap ℂ (RatFunc ℂ) c) := by
  -- basic facts about the standard derivation
  have hC : ∀ c : ℂ, (algebraMap ℂ (RatFunc ℂ) c)′ = 0 := by
    intro c
    have h1 := hD (Polynomial.C c)
    rw [RatFunc.algebraMap_C, Polynomial.derivative_C, map_zero] at h1
    exact h1
  have hX : (RatFunc.X : RatFunc ℂ)′ = 1 := by
    have h1 := hD Polynomial.X
    rw [RatFunc.algebraMap_X, Polynomial.derivative_X, map_one] at h1
    exact h1
  have hconst : ∀ k : RatFunc ℂ, k′ = 0 → ∃ c : ℂ, k = algebraMap ℂ (RatFunc ℂ) c := by
    intro k hk
    have := constants_ratFunc hD
    have hk' : k ∈ constants (RatFunc ℂ) := hk
    rw [this] at hk'
    obtain ⟨c, hc⟩ := hk'
    exact ⟨c, hc.symm⟩
  set w : RatFunc ℂ := 1 / RatFunc.X with hw
  have hwnd : ¬ ∃ g : RatFunc ℂ, g′ = w := inv_X_no_antideriv hD
  letI : Differential (RatFunc (RatFunc ℂ)) := logDiff w
  haveI : DifferentialAlgebra (RatFunc ℂ) (RatFunc (RatFunc ℂ)) :=
    ⟨fun a => by
      have h1 := logDiff_poly w (Polynomial.C a)
      rw [RatFunc.algebraMap_C, Differential.implicitDeriv_C, RatFunc.algebraMap_C] at h1
      exact h1⟩
  have htd : (RatFunc.X : RatFunc (RatFunc ℂ))′ =
      algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ)) w := by
    have h1 := logDiff_poly w Polynomial.X
    rw [RatFunc.algebraMap_X, Differential.implicitDeriv_X, RatFunc.algebraMap_C] at h1
    exact h1
  refine ⟨RatFunc (RatFunc ℂ), inferInstance, inferInstance, inferInstance, inferInstance,
    RatFunc.X, RatFunc.adjoin_X, RatFunc.transcendental_X, ?_, ?_⟩
  · rw [htd, deriv_algebraMap, hX, map_one, hw, map_div₀, map_one]
  · intro g
    constructor
    · intro hg
      have hg' : g′ = algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ)) w := hg
      have h0 : (g - RatFunc.X)′ = 0 := by
        rw [map_sub, hg', htd, sub_self]
      obtain ⟨a, ha, hga⟩ := logDiff_consts w hwnd (g - RatFunc.X) h0
      obtain ⟨c, hc⟩ := hconst a ha
      refine ⟨c, ?_⟩
      rw [← hc, ← hga]
      ring
    · rintro ⟨c, rfl⟩
      show (RatFunc.X + algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ))
        (algebraMap ℂ (RatFunc ℂ) c))′ = _
      rw [map_add, htd, deriv_algebraMap, hC, map_zero, add_zero]
