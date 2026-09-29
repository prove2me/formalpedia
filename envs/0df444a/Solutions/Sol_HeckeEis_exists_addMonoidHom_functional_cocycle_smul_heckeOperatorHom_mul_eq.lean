-- Prove2me | solution 1 for HeckeEis.exists_addMonoidHom_functional_cocycle_smul_heckeOperatorHom_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/849bf39c-1ad9-5923-a718-72be26bca126

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Theorems.Thm_HeckeEis_sum_repr_sub_coeffHeckeFun_mem_coeffCoboundaries
import Theorems.Thm_ModularCurve_index_heckeUpper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_addMonoidHom_functional_cocycle_smul_heckeOperatorHom_mul_eq

set_option autoImplicit false

namespace FunTransfer

open CongruenceSubgroup HeckeEis
open scoped MatrixGroups

section Lift

theorem eq_of_alphaMat_mul_eq {ℓ : ℕ} (hℓ : (ℓ : ℤ) ≠ 0) {A B : Matrix (Fin 2) (Fin 2) ℤ}
    (h : alphaMat ℓ * A = alphaMat ℓ * B) : A = B := by
  ext i j
  have h0 := congrFun (congrFun h 0) j
  have h1 := congrFun (congrFun h 1) j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, alphaMat_apply_zero_zero,
    alphaMat_apply_zero_one, alphaMat_apply_one_zero, alphaMat_apply_one_one,
    one_mul, zero_mul, add_zero, zero_add] at h0 h1
  fin_cases i
  · exact h0
  · exact mul_left_cancel₀ hℓ h1

variable (p : ℕ)

def liftMat (g : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![g 0 0, (p : ℤ) * g 0 1; g 1 0 / (p : ℤ), g 1 1]

@[scoped simp] theorem liftMat_apply_zero_zero (g : Matrix (Fin 2) (Fin 2) ℤ) : liftMat p g 0 0 = g 0 0 := rfl
@[scoped simp] theorem liftMat_apply_zero_one (g : Matrix (Fin 2) (Fin 2) ℤ) :
    liftMat p g 0 1 = (p : ℤ) * g 0 1 := rfl
@[scoped simp] theorem liftMat_apply_one_zero (g : Matrix (Fin 2) (Fin 2) ℤ) :
    liftMat p g 1 0 = g 1 0 / (p : ℤ) := rfl
@[scoped simp] theorem liftMat_apply_one_one (g : Matrix (Fin 2) (Fin 2) ℤ) : liftMat p g 1 1 = g 1 1 := rfl

theorem alphaMat_mul_liftMat {g : Matrix (Fin 2) (Fin 2) ℤ} (hg : (p : ℤ) ∣ g 1 0) :
    alphaMat p * liftMat p g = g * alphaMat p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, liftMat, Int.mul_ediv_cancel' hg, mul_comm]

variable {p}

theorem liftMat_mul (hp : (p : ℤ) ≠ 0) {g h : Matrix (Fin 2) (Fin 2) ℤ}
    (hg : (p : ℤ) ∣ g 1 0) (hh : (p : ℤ) ∣ h 1 0) (hgh : (p : ℤ) ∣ (g * h) 1 0) :
    liftMat p (g * h) = liftMat p g * liftMat p h := by
  apply eq_of_alphaMat_mul_eq hp
  rw [alphaMat_mul_liftMat p hgh, ← mul_assoc, alphaMat_mul_liftMat p hg, mul_assoc, mul_assoc,
    alphaMat_mul_liftMat p hh]

theorem liftMat_one : liftMat p (1 : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [liftMat]

theorem det_liftMat (hp : (p : ℤ) ≠ 0) {g : Matrix (Fin 2) (Fin 2) ℤ} (hg : (p : ℤ) ∣ g 1 0) :
    (liftMat p g).det = g.det := by
  have h := congrArg Matrix.det (alphaMat_mul_liftMat p hg)
  rw [Matrix.det_mul, Matrix.det_mul, det_alphaMat] at h
  exact mul_left_cancel₀ hp (by linear_combination h)

theorem heckeConjMat_liftMat {ℓ : ℕ} {g : Matrix (Fin 2) (Fin 2) ℤ}
    (hℓ : (ℓ : ℤ) ∣ g 0 1) (hp : (p : ℤ) ∣ g 1 0) :
    heckeConjMat ℓ (liftMat p g) = liftMat p (heckeConjMat ℓ g) := by
  obtain ⟨k, hk⟩ := hp
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · show (p : ℤ) * g 0 1 / (ℓ : ℤ) = (p : ℤ) * (g 0 1 / (ℓ : ℤ))
    exact Int.mul_ediv_assoc _ hℓ
  · show g 1 0 / (p : ℤ) * (ℓ : ℤ) = g 1 0 * (ℓ : ℤ) / (p : ℤ)
    by_cases hp0 : (p : ℤ) = 0
    · simp [hp0]
    · rw [hk, mul_assoc, Int.mul_ediv_cancel_left _ hp0, Int.mul_ediv_cancel_left _ hp0]
  · rfl

variable (p) [Fact p.Prime] (N : ℕ)

theorem natCast_p_ne_zero : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Fact.out : p.Prime).ne_zero

omit [Fact p.Prime] in

theorem dvd_entry_of_mem (γ : Gamma0 (N * p)) : ((N * p : ℕ) : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 := by
  have h := Gamma0_mem.mp γ.2
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

omit [Fact p.Prime] in
theorem p_dvd_entry (γ : Gamma0 (N * p)) : (p : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
  (show (p : ℤ) ∣ ((N * p : ℕ) : ℤ) from ⟨(N : ℤ), by push_cast; ring⟩).trans (dvd_entry_of_mem p N γ)

theorem dvd_entry_div (γ : Gamma0 (N * p)) : (N : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 / (p : ℤ) := by
  obtain ⟨k, hk⟩ := dvd_entry_of_mem p N γ
  rw [hk, show (((N * p : ℕ) : ℤ)) * k = (p : ℤ) * ((N : ℤ) * k) by push_cast; ring,
    Int.mul_ediv_cancel_left _ (natCast_p_ne_zero p)]
  exact Dvd.intro k rfl

def liftSL (γ : Gamma0 (N * p)) : SL(2, ℤ) :=
  ⟨liftMat p ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ), by
    rw [det_liftMat (natCast_p_ne_zero p) (p_dvd_entry p N γ)]
    exact (γ : SL(2, ℤ)).2⟩

@[scoped simp] theorem coe_liftSL (γ : Gamma0 (N * p)) :
    ((liftSL p N γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      liftMat p ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := rfl

theorem liftSL_mem (γ : Gamma0 (N * p)) : liftSL p N γ ∈ Gamma0 N := by
  rw [Gamma0_mem]
  show ((((γ : SL(2, ℤ)) 1 0 / (p : ℤ) : ℤ)) : ZMod N) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact dvd_entry_div p N γ

def lift : Gamma0 (N * p) →* Gamma0 N where
  toFun γ := ⟨liftSL p N γ, liftSL_mem p N γ⟩
  map_one' := by
    refine Subtype.ext (Subtype.ext ?_)
    show liftMat p (1 : Matrix (Fin 2) (Fin 2) ℤ) = 1
    exact liftMat_one
  map_mul' γ δ := by
    refine Subtype.ext (Subtype.ext ?_)
    show liftMat p ((((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) * ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
      = liftMat p ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * liftMat p ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
    exact liftMat_mul (natCast_p_ne_zero p) (p_dvd_entry p N γ) (p_dvd_entry p N δ) (p_dvd_entry p N (γ * δ))

@[scoped simp] theorem coe_lift (γ : Gamma0 (N * p)) :
    (((lift p N γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      liftMat p ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := rfl

theorem lift_eq_of_mul_alphaMat_eq (γ : Gamma0 (N * p)) (δ : Gamma0 N)
    (h : ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * alphaMat p =
      alphaMat p * ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) :
    lift p N γ = δ := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [coe_lift]
  apply eq_of_alphaMat_mul_eq (natCast_p_ne_zero p)
  rw [alphaMat_mul_liftMat p (p_dvd_entry p N γ), h]

theorem p_dvd_lift_zero_one (γ : Gamma0 (N * p)) :
    (p : ℤ) ∣ ((lift p N γ : Gamma0 N) : SL(2, ℤ)) 0 1 :=
  ⟨(γ : SL(2, ℤ)) 0 1, rfl⟩

end Lift

section Transfer

variable (p : ℕ) [Fact p.Prime] (N : ℕ) {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable {ρ : Representation K (Gamma0 N) V} {μ : V →ₗ[K] K}
variable (hμρ : ∀ δ : Gamma0 N, (p : ℤ) ∣ (δ : SL(2, ℤ)) 0 1 → μ ∘ₗ ρ δ = μ)
variable {z : Gamma0 N → V} (hz : z ∈ coeffCocycles ρ)

include hμρ in
theorem mu_rho_lift (γ : Gamma0 (N * p)) (v : V) : μ (ρ (lift p N γ) v) = μ v :=
  LinearMap.congr_fun (hμρ _ (p_dvd_lift_zero_one p N γ)) v

include hμρ hz in

theorem transfer_add (γ δ : Gamma0 (N * p)) :
    μ (z (lift p N (γ * δ))) = μ (z (lift p N γ)) + μ (z (lift p N δ)) := by
  rw [map_mul, hz, map_add, mu_rho_lift p N hμρ]

noncomputable def transfer : Additive (Gamma0 (N * p)) →+ K :=
  AddMonoidHom.mk' (fun g => μ (z (lift p N (Additive.toMul g))))
    (fun g h => transfer_add p N hμρ hz (Additive.toMul g) (Additive.toMul h))

@[scoped simp] theorem transfer_apply (γ : Gamma0 (N * p)) :
    transfer p N hμρ hz (Additive.ofMul γ) = μ (z (lift p N γ)) := rfl

include hμρ in

theorem mu_coboundary_lift (v : V) (γ : Gamma0 (N * p)) : μ (ρ (lift p N γ) v - v) = 0 := by
  rw [map_sub, mu_rho_lift p N hμρ, sub_self]

end Transfer

section Cosets

variable (p : ℕ) [Fact p.Prime] (N : ℕ) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p)

theorem lift_mem_heckeUpper_iff (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) (γ : Gamma0 (N * p)) :
    lift p N γ ∈ heckeUpper N ℓ ↔ γ ∈ heckeUpper (N * p) ℓ := by
  rw [mem_heckeUpper, mem_heckeUpper]
  show (ℓ : ℤ) ∣ (p : ℤ) * (γ : SL(2, ℤ)) 0 1 ↔ (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 0 1
  constructor
  · intro h
    have hcop : IsCoprime (ℓ : ℤ) (p : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact (Nat.coprime_primes hℓ Fact.out).mpr hℓp
    exact hcop.dvd_of_dvd_mul_left h
  · intro h
    exact h.mul_left _

def cosetMap : Gamma0 (N * p) ⧸ heckeUpper (N * p) ℓ → Gamma0 N ⧸ heckeUpper N ℓ :=
  Quotient.map' (lift p N) fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    rw [← map_inv, ← map_mul]
    exact (lift_mem_heckeUpper_iff p N ℓ hℓ hℓp _).mpr hab

theorem cosetMap_mk (γ : Gamma0 (N * p)) :
    cosetMap p N ℓ hℓ hℓp (γ : Gamma0 (N * p) ⧸ heckeUpper (N * p) ℓ) =
      ((lift p N γ : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ) := rfl

theorem cosetMap_smul (γ : Gamma0 (N * p)) (q : Gamma0 (N * p) ⧸ heckeUpper (N * p) ℓ) :
    cosetMap p N ℓ hℓ hℓp (γ • q) = lift p N γ • cosetMap p N ℓ hℓ hℓp q := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    show cosetMap p N ℓ hℓ hℓp ((γ * x : Gamma0 (N * p)) : _ ⧸ _) = _
    rw [cosetMap_mk, cosetMap_mk, map_mul]
    rfl

theorem cosetMap_injective : Function.Injective (cosetMap p N ℓ hℓ hℓp) := by
  intro a b
  induction a using QuotientGroup.induction_on with
  | H a =>
  induction b using QuotientGroup.induction_on with
  | H b =>
    intro h
    rw [cosetMap_mk, cosetMap_mk, QuotientGroup.eq, ← map_inv, ← map_mul,
      lift_mem_heckeUpper_iff p N ℓ hℓ hℓp] at h
    exact QuotientGroup.eq.mpr h

include hℓN in
theorem cosetMap_bijective : Function.Bijective (cosetMap p N ℓ hℓ hℓp) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : Finite (Gamma0 N ⧸ heckeUpper N ℓ) := Subgroup.finite_quotient_of_finiteIndex
  refine (cosetMap_injective p N ℓ hℓ hℓp).bijective_of_nat_card_le (le_of_eq ?_)
  have hℓNp : ¬ ℓ ∣ N * p := by
    intro h
    rcases (Nat.Prime.dvd_mul hℓ).mp h with h | h
    · exact hℓN h
    · exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ Fact.out).mp h)
  rw [← Subgroup.index_eq_card, ← Subgroup.index_eq_card, ModularCurve.index_heckeUpper hℓ hℓN,
    ModularCurve.index_heckeUpper hℓ hℓNp]

noncomputable def cosetEquiv : (Gamma0 (N * p) ⧸ heckeUpper (N * p) ℓ) ≃ (Gamma0 N ⧸ heckeUpper N ℓ) :=
  Equiv.ofBijective _ (cosetMap_bijective p N ℓ hℓ hℓN hℓp)

theorem cosetEquiv_apply (q : Gamma0 (N * p) ⧸ heckeUpper (N * p) ℓ) :
    cosetEquiv p N ℓ hℓ hℓN hℓp q = cosetMap p N ℓ hℓ hℓp q := rfl

noncomputable def sec (q : Gamma0 N ⧸ heckeUpper N ℓ) : Gamma0 N :=
  lift p N ((cosetEquiv p N ℓ hℓ hℓN hℓp).symm q).out

theorem sec_spec (q : Gamma0 N ⧸ heckeUpper N ℓ) :
    ((sec p N ℓ hℓ hℓN hℓp q : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ) = q := by
  rw [sec, ← cosetMap_mk p N ℓ hℓ hℓp, QuotientGroup.out_eq', ← cosetEquiv_apply p N ℓ hℓ hℓN hℓp,
    Equiv.apply_symm_apply]

theorem sec_cosetEquiv (q : Gamma0 (N * p) ⧸ heckeUpper (N * p) ℓ) :
    sec p N ℓ hℓ hℓN hℓp (cosetEquiv p N ℓ hℓ hℓN hℓp q) = lift p N q.out := by
  rw [sec, Equiv.symm_apply_apply]

noncomputable def tra (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ) : ↥(heckeUpper N ℓ) :=
  ⟨(sec p N ℓ hℓ hℓN hℓp (g • q))⁻¹ * (g * sec p N ℓ hℓ hℓN hℓp q), by
    refine QuotientGroup.eq.mp ?_
    rw [sec_spec]
    show g • q = ((g * sec p N ℓ hℓ hℓN hℓp q : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ)
    rw [show ((g * sec p N ℓ hℓ hℓN hℓp q : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ)
        = g • ((sec p N ℓ hℓ hℓN hℓp q : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ) from rfl, sec_spec]⟩

theorem sec_mul_tra (g : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ) :
    sec p N ℓ hℓ hℓN hℓp (g • q) * (tra p N ℓ hℓ hℓN hℓp g q : Gamma0 N) = g * sec p N ℓ hℓ hℓN hℓp q := by
  show sec p N ℓ hℓ hℓN hℓp (g • q) * ((sec p N ℓ hℓ hℓN hℓp (g • q))⁻¹ * (g * sec p N ℓ hℓ hℓN hℓp q)) = _
  rw [mul_inv_cancel_left]

theorem coe_tra_lift (γ : Gamma0 (N * p)) (q : Gamma0 (N * p) ⧸ heckeUpper (N * p) ℓ) :
    (tra p N ℓ hℓ hℓN hℓp (lift p N γ) (cosetEquiv p N ℓ hℓ hℓN hℓp q) : Gamma0 N) =
      lift p N (transferAux (heckeUpper (N * p) ℓ) γ q : Gamma0 (N * p)) := by
  show (sec p N ℓ hℓ hℓN hℓp (lift p N γ • cosetEquiv p N ℓ hℓ hℓN hℓp q))⁻¹ *
      (lift p N γ * sec p N ℓ hℓ hℓN hℓp (cosetEquiv p N ℓ hℓ hℓN hℓp q)) = _
  have h1 : lift p N γ • cosetEquiv p N ℓ hℓ hℓN hℓp q = cosetEquiv p N ℓ hℓ hℓN hℓp (γ • q) := by
    rw [cosetEquiv_apply, cosetEquiv_apply, cosetMap_smul]
  rw [h1, sec_cosetEquiv, sec_cosetEquiv, coe_transferAux, map_mul, map_mul, map_inv]

theorem heckeConj_lift [NeZero ℓ] (u : ↥(heckeUpper (N * p) ℓ))
    (hu : lift p N (u : Gamma0 (N * p)) ∈ heckeUpper N ℓ) :
    heckeConj N ℓ ⟨lift p N (u : Gamma0 (N * p)), hu⟩ =
      lift p N (heckeConj (N * p) ℓ u : Gamma0 (N * p)) := by
  refine Subtype.ext (Subtype.ext ?_)
  show heckeConjMat ℓ (liftMat p ((((u : Gamma0 (N * p)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)))
    = liftMat p (heckeConjMat ℓ ((((u : Gamma0 (N * p)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)))
  exact heckeConjMat_liftMat ((mem_heckeUpper _ _).mp u.2) (p_dvd_entry p N _)

end Cosets

section Hecke

variable (p : ℕ) [Fact p.Prime] (N : ℕ) {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable {ρ : Representation K (Gamma0 N) V} {μ : V →ₗ[K] K}
variable (hμρ : ∀ δ : Gamma0 N, (p : ℤ) ∣ (δ : SL(2, ℤ)) 0 1 → μ ∘ₗ ρ δ = μ)
variable {z : Gamma0 N → V} (hz : z ∈ coeffCocycles ρ)

theorem smul_heckeOperatorHom_transfer (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p)
    (a : V →ₗ[K] V) (c : K) (hμa : μ ∘ₗ a = c • μ)
    (ha : haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a)
    (lam : K) (T : coeffH1 ρ →ₗ[K] coeffH1 ρ)
    (hT : haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; IsCoeffHeckeOnH1 N ℓ ρ a T)
    (heig : T (coeffH1Mk ρ ⟨z, hz⟩) = lam • coeffH1Mk ρ ⟨z, hz⟩) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    c • heckeOperatorHom (N * p) ℓ K (transfer p N hμρ hz) = lam • transfer p N hμρ hz := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩

  obtain ⟨w, hw, hTw⟩ := hT ⟨z, hz⟩
  rw [hTw] at heig
  have hcob1 : (w : Gamma0 N → V) - lam • z ∈ coeffCoboundaries ρ := by
    have h := (Submodule.Quotient.eq _).mp (heig.trans (map_smul (coeffH1Mk ρ) lam ⟨z, hz⟩).symm)
    exact h

  have hcob2 := sum_repr_sub_coeffHeckeFun_mem_coeffCoboundaries N ℓ ρ a ha
    (sec p N ℓ hℓ hℓN hℓp) (tra p N ℓ hℓ hℓN hℓp) (sec_spec p N ℓ hℓ hℓN hℓp) (sec_mul_tra p N ℓ hℓ hℓN hℓp) hz
  rw [hw] at hcob1
  change coeffHeckeFun N ℓ ρ a z - lam • z ∈ _ at hcob1
  have hcob := (coeffCoboundaries ρ).add_mem hcob2 hcob1
  rw [sub_add_sub_cancel] at hcob
  obtain ⟨v, hv⟩ := (mem_coeffCoboundaries_iff _ _).mp hcob

  refine AddMonoidHom.ext fun g => ?_
  set γ := Additive.toMul g with hγdef
  have hg : g = Additive.ofMul γ := rfl
  rw [hg, AddMonoidHom.smul_apply, AddMonoidHom.smul_apply, transfer_apply, heckeOperatorHom_apply]
  letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  letI := (heckeUpper (N * p) ℓ).fintypeQuotientOfFiniteIndex
  have hkey := congrArg μ (congrFun hv (lift p N γ))
  rw [mu_coboundary_lift p N hμρ, Pi.sub_apply, map_sub, Pi.smul_apply, map_smul, map_sum] at hkey

  have hμa' : ∀ x : V, μ (a x) = c * μ x := fun x => by
    have := LinearMap.congr_fun hμa x
    simpa using this
  have hsummand : ∀ q : Gamma0 N ⧸ heckeUpper N ℓ,
      μ (ρ (sec p N ℓ hℓ hℓN hℓp (lift p N γ • q))
        (a (z (heckeConj N ℓ (tra p N ℓ hℓ hℓN hℓp (lift p N γ) q)))))
        = c * μ (z (heckeConj N ℓ (tra p N ℓ hℓ hℓN hℓp (lift p N γ) q))) := by
    intro q
    rw [sec, mu_rho_lift p N hμρ, hμa']
  simp only [hsummand] at hkey
  rw [← Finset.mul_sum] at hkey

  have hreindex : ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
      μ (z (heckeConj N ℓ (tra p N ℓ hℓ hℓN hℓp (lift p N γ) q)))
      = ∑ q : Gamma0 (N * p) ⧸ heckeUpper (N * p) ℓ,
          μ (z (lift p N (heckeConj (N * p) ℓ (transferAux (heckeUpper (N * p) ℓ) γ q)))) := by
    rw [← (cosetEquiv p N ℓ hℓ hℓN hℓp).sum_comp]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 2
    have hmem : lift p N (transferAux (heckeUpper (N * p) ℓ) γ q : Gamma0 (N * p)) ∈ heckeUpper N ℓ :=
      (lift_mem_heckeUpper_iff p N ℓ hℓ hℓp _).mpr (transferAux (heckeUpper (N * p) ℓ) γ q).2
    have htra : tra p N ℓ hℓ hℓN hℓp (lift p N γ) (cosetEquiv p N ℓ hℓ hℓN hℓp q)
        = ⟨lift p N (transferAux (heckeUpper (N * p) ℓ) γ q : Gamma0 (N * p)), hmem⟩ :=
      Subtype.ext (coe_tra_lift p N ℓ hℓ hℓN hℓp γ q)
    rw [htra, heckeConj_lift]
  rw [hreindex] at hkey

  have hkey' : c *
      ∑ q : Gamma0 (N * p) ⧸ heckeUpper (N * p) ℓ,
        μ (z (lift p N (heckeConj (N * p) ℓ (transferAux (heckeUpper (N * p) ℓ) γ q))))
      = lam * μ (z (lift p N γ)) := sub_eq_zero.mp hkey.symm
  simp only [transfer_apply, smul_eq_mul]
  exact hkey'

end Hecke

end FunTransfer
p2m_reactivate "P2MW.S_HeckeEis_exists_addMonoidHom_functional_cocycle_smul_heckeOperatorHom_mul_eq.FunTransfer"

open scoped MatrixGroups in
theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a : ℕ → (V →ₗ[K] V))
    (μ : V →ₗ[K] K) (c : ℕ → K)
    (hμρ : ∀ δ : CongruenceSubgroup.Gamma0 N, (p : ℤ) ∣ (δ : SL(2, ℤ)) 0 1 → μ ∘ₗ ρ δ = μ)
    (hμa : ∀ ℓ : ℕ, μ ∘ₗ a ℓ = c ℓ • μ)
    (z : CongruenceSubgroup.Gamma0 N → V) (hz : z ∈ HeckeEis.coeffCocycles ρ) :
    ∃ y : Additive ↥(CongruenceSubgroup.Gamma0 (N * p)) →+ K,
      (∀ (γ : CongruenceSubgroup.Gamma0 (N * p)) (δ : CongruenceSubgroup.Gamma0 N),
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * HeckeEis.alphaMat p
            = HeckeEis.alphaMat p * ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) →
        y (Additive.ofMul γ) = μ (z δ)) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ≠ p →
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
         ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
          a ℓ ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a ℓ) →
        ∀ (lam : K) (T : HeckeEis.coeffH1 ρ →ₗ[K] HeckeEis.coeffH1 ρ),
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; HeckeEis.IsCoeffHeckeOnH1 N ℓ ρ (a ℓ) T) →
        T (HeckeEis.coeffH1Mk ρ ⟨z, hz⟩) = lam • HeckeEis.coeffH1Mk ρ ⟨z, hz⟩ →
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
         c ℓ • HeckeEis.heckeOperatorHom (N * p) ℓ K y = lam • y) := by
  refine ⟨FunTransfer.transfer p N hμρ hz, fun γ δ h => ?_, fun ℓ hℓ hℓN hℓp ha lam T hT heig => ?_⟩
  · rw [FunTransfer.transfer_apply, FunTransfer.lift_eq_of_mul_alphaMat_eq p N γ δ h]
  · exact FunTransfer.smul_heckeOperatorHom_transfer p N hμρ hz ℓ hℓ hℓN hℓp (a ℓ) (c ℓ) (hμa ℓ) ha lam T hT
      heig

end S_HeckeEis_exists_addMonoidHom_functional_cocycle_smul_heckeOperatorHom_mul_eq
end P2MW
export P2MW.S_HeckeEis_exists_addMonoidHom_functional_cocycle_smul_heckeOperatorHom_mul_eq (solution)
