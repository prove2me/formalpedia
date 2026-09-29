-- Prove2me | solution 1 for HeckeEis.exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/0eeab1b4-b273-5c55-a4ef-13924d29cf0f

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_HeckeEis_Gamma0NebenRep
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCocycles
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries
import Theorems.Thm_HeckeEis_exists_addMonoidHom_functional_cocycle_smul_heckeOperatorHom_mul_eq
import Theorems.Thm_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_surjective
import Theorems.Thm_HeckeEis_isEigensystemH1_or_of_isEigensystemH1_of_injective
import Theorems.Thm_HeckeEis_isEigensystemH1_one_natCast_add_one
import Theorems.Thm_HeckeEis_exists_isEigensystemH1_one_natCast_mul_of_isEigensystemH1_one_of_three_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep

set_option autoImplicit false

namespace TwistMain

open CongruenceSubgroup HeckeEis
open scoped MatrixGroups

section Induced

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable (N ℓ : ℕ) [NeZero ℓ] (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)

def IsCompat : Prop :=
  ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a

noncomputable def heckeLin : (Gamma0 N → V) →ₗ[K] (Gamma0 N → V) where
  toFun := coeffHeckeFun N ℓ ρ a
  map_add' z w := by
    letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
    ext g
    simp only [coeffHeckeFun_apply, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c z := by
    letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
    ext g
    simp only [coeffHeckeFun_apply, Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]

variable {N ℓ ρ a}

noncomputable def heckeZ1 (ha : IsCompat N ℓ ρ a) : ↥(coeffCocycles ρ) →ₗ[K] ↥(coeffCocycles ρ) :=
  (heckeLin N ℓ ρ a).restrict fun _ hz => coeffHeckeFun_mem_coeffCocycles N ℓ ρ a ha hz

@[scoped simp] theorem coe_heckeZ1 (ha : IsCompat N ℓ ρ a) (z : ↥(coeffCocycles ρ)) :
    (heckeZ1 ha z : Gamma0 N → V) = coeffHeckeFun N ℓ ρ a z := rfl

noncomputable def heckeH1 (ha : IsCompat N ℓ ρ a) : coeffH1 ρ →ₗ[K] coeffH1 ρ :=
  ((coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype).mapQ
    ((coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype) (heckeZ1 ha)
    fun _ hz => coeffHeckeFun_mem_coeffCoboundaries N ℓ ρ a ha hz

theorem heckeH1_mk (ha : IsCompat N ℓ ρ a) (z : ↥(coeffCocycles ρ)) :
    heckeH1 ha (coeffH1Mk ρ z) = coeffH1Mk ρ (heckeZ1 ha z) := rfl

theorem isCoeffHeckeOnH1_heckeH1 (ha : IsCompat N ℓ ρ a) : IsCoeffHeckeOnH1 N ℓ ρ a (heckeH1 ha) :=
  fun z => ⟨heckeZ1 ha z, rfl, rfl⟩

end Induced

section Twist

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable (N : ℕ) (ρ : Representation K (Gamma0 N) V)

theorem coeffHeckeFun_smul (ℓ : ℕ) [NeZero ℓ] (c : K) (a : V →ₗ[K] V) (z : Gamma0 N → V) :
    coeffHeckeFun N ℓ ρ (c • a) z = c • coeffHeckeFun N ℓ ρ a z := by
  letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  ext g
  simp only [coeffHeckeFun_apply, Pi.smul_apply, LinearMap.smul_apply, map_smul, Finset.smul_sum]

theorem smul_isCoeffHeckeOnH1 (ℓ : ℕ) [NeZero ℓ] (c : K) (a : V →ₗ[K] V)
    {T : coeffH1 ρ →ₗ[K] coeffH1 ρ} (hT : IsCoeffHeckeOnH1 N ℓ ρ a T) :
    IsCoeffHeckeOnH1 N ℓ ρ (c • a) (c • T) := by
  intro z
  obtain ⟨w, hw, hTw⟩ := hT z
  refine ⟨c • w, ?_, ?_⟩
  · rw [Submodule.coe_smul, hw, coeffHeckeFun_smul]
  · rw [LinearMap.smul_apply, hTw, map_smul]

theorem isEigensystemH1_of_smul (a a' : ℕ → (V →ₗ[K] V)) (χ : ℕ → K) (S₀ : Set ℕ) (lam : ℕ → K)
    (haa' : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → a' ℓ = χ ℓ • a ℓ)
    (h : IsEigensystemH1 N ρ a S₀ lam) :
    IsEigensystemH1 N ρ a' S₀ (fun ℓ => χ ℓ * lam ℓ) := by
  obtain ⟨x, hx, heig⟩ := h
  refine ⟨x, hx, fun ℓ hℓ hℓN hℓS => ?_⟩
  obtain ⟨T, hT, hTx⟩ := heig ℓ hℓ hℓN hℓS
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  refine ⟨χ ℓ • T, ?_, ?_⟩
  · have := smul_isCoeffHeckeOnH1 N ρ ℓ (χ ℓ) (a ℓ) hT
    rw [← haa' ℓ hℓ hℓN hℓS] at this
    exact this
  · rw [LinearMap.smul_apply, hTx, smul_smul]

theorem isEigensystemH1_congr (a : ℕ → (V →ₗ[K] V)) (S₀ : Set ℕ) {lam lam' : ℕ → K}
    (hll : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → lam ℓ = lam' ℓ) (h : IsEigensystemH1 N ρ a S₀ lam) :
    IsEigensystemH1 N ρ a S₀ lam' := by
  obtain ⟨x, hx, heig⟩ := h
  refine ⟨x, hx, fun ℓ hℓ hℓN hℓS => ?_⟩
  obtain ⟨T, hT, hTx⟩ := heig ℓ hℓ hℓN hℓS
  exact ⟨T, hT, by rw [hTx, hll ℓ hℓ hℓN hℓS]⟩

theorem isEigensystemH1_mono (a : ℕ → (V →ₗ[K] V)) {S₀ S₁ : Set ℕ} (hS : S₀ ⊆ S₁) {lam : ℕ → K}
    (h : IsEigensystemH1 N ρ a S₀ lam) : IsEigensystemH1 N ρ a S₁ lam := by
  obtain ⟨x, hx, heig⟩ := h
  exact ⟨x, hx, fun ℓ hℓ hℓN hℓS => heig ℓ hℓ hℓN fun h' => hℓS (hS h')⟩

end Twist

section Entries

variable (p : ℕ) [Fact p.Prime] (M : ℕ) (hpM : p ∣ M)

def aP (γ : Gamma0 M) : ZMod p := (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod p)
def bP (γ : Gamma0 M) : ZMod p := (((γ : SL(2, ℤ)) 0 1 : ℤ) : ZMod p)
def dP (γ : Gamma0 M) : ZMod p := (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod p)

theorem entry_c_dvd (γ : Gamma0 M) : (M : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp γ.2)

include hpM in
theorem cP_eq_zero (γ : Gamma0 M) : ((((γ : SL(2, ℤ)) 1 0 : ℤ)) : ZMod p) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact (Int.natCast_dvd_natCast.mpr hpM).trans (entry_c_dvd M γ)

include hpM in

theorem aP_mul_dP (γ : Gamma0 M) : aP p M γ * dP p M γ = 1 := by
  have hdet := Matrix.det_fin_two ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
  rw [(γ : SL(2, ℤ)).2] at hdet
  have h := congrArg (fun x : ℤ => (x : ZMod p)) hdet
  simp only [Int.cast_one, Int.cast_sub, Int.cast_mul, cP_eq_zero p M hpM γ, mul_zero, sub_zero] at h
  exact h.symm

include hpM in
theorem dP_ne_zero (γ : Gamma0 M) : dP p M γ ≠ 0 := fun h => by
  have := aP_mul_dP p M hpM γ
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem aP_one : aP p M 1 = 1 := by simp [aP]
theorem bP_one : bP p M 1 = 0 := by simp [bP]
theorem dP_one : dP p M 1 = 1 := by simp [dP]

include hpM in
theorem dP_mul (γ γ' : Gamma0 M) : dP p M (γ * γ') = dP p M γ * dP p M γ' := by
  simp only [dP]
  rw [show (((γ * γ' : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ)
      = (γ : SL(2, ℤ)) 1 0 * (γ' : SL(2, ℤ)) 0 1 + (γ : SL(2, ℤ)) 1 1 * (γ' : SL(2, ℤ)) 1 1 from
      (Matrix.two_mul_expl ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (γ' : SL(2, ℤ))).2.2.2]
  push_cast
  rw [cP_eq_zero p M hpM γ, zero_mul, zero_add]

include hpM in
theorem aP_mul (γ γ' : Gamma0 M) : aP p M (γ * γ') = aP p M γ * aP p M γ' := by
  simp only [aP]
  rw [show (((γ * γ' : Gamma0 M) : SL(2, ℤ)) 0 0 : ℤ)
      = (γ : SL(2, ℤ)) 0 0 * (γ' : SL(2, ℤ)) 0 0 + (γ : SL(2, ℤ)) 0 1 * (γ' : SL(2, ℤ)) 1 0 from
      (Matrix.two_mul_expl ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (γ' : SL(2, ℤ))).1]
  push_cast
  rw [cP_eq_zero p M hpM γ', mul_zero, add_zero]

theorem bP_mul (γ γ' : Gamma0 M) : bP p M (γ * γ') = aP p M γ * bP p M γ' + bP p M γ * dP p M γ' := by
  simp only [aP, bP, dP]
  rw [show (((γ * γ' : Gamma0 M) : SL(2, ℤ)) 0 1 : ℤ)
      = (γ : SL(2, ℤ)) 0 0 * (γ' : SL(2, ℤ)) 0 1 + (γ : SL(2, ℤ)) 0 1 * (γ' : SL(2, ℤ)) 1 1 from
      (Matrix.two_mul_expl ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (γ' : SL(2, ℤ))).2.1]
  push_cast
  ring

include hpM in
theorem aP_inv (γ : Gamma0 M) : aP p M γ⁻¹ = dP p M γ := by
  simp only [aP, dP]
  rw [show ((γ⁻¹ : Gamma0 M) : SL(2, ℤ)) = (γ : SL(2, ℤ))⁻¹ from rfl, Matrix.SpecialLinearGroup.SL2_inv_expl]
  rfl

theorem bP_inv (γ : Gamma0 M) : bP p M γ⁻¹ = -bP p M γ := by
  simp only [bP]
  rw [show ((γ⁻¹ : Gamma0 M) : SL(2, ℤ)) = (γ : SL(2, ℤ))⁻¹ from rfl, Matrix.SpecialLinearGroup.SL2_inv_expl]
  show (((-((γ : SL(2, ℤ)) 0 1) : ℤ) : ZMod p)) = _
  push_cast
  rfl

include hpM in
theorem dP_inv (γ : Gamma0 M) : dP p M γ⁻¹ = aP p M γ := by
  simp only [aP, dP]
  rw [show ((γ⁻¹ : Gamma0 M) : SL(2, ℤ)) = (γ : SL(2, ℤ))⁻¹ from rfl, Matrix.SpecialLinearGroup.SL2_inv_expl]
  rfl

def Tg : Gamma0 M := ⟨ModularGroup.T, by rw [Gamma0_mem, ModularGroup.T]; simp⟩

theorem coe_Tg_zpow (n : ℤ) : (((Tg M ^ n : Gamma0 M) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, n; 0, 1] := by
  rw [show ((Tg M ^ n : Gamma0 M) : SL(2, ℤ)) = ModularGroup.T ^ n from rfl]
  exact ModularGroup.coe_T_zpow n

theorem aP_Tg_zpow (n : ℤ) : aP p M (Tg M ^ n) = 1 := by
  simp only [aP]
  rw [show ((Tg M ^ n : Gamma0 M) : SL(2, ℤ)) 0 0 = (!![(1 : ℤ), n; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) 0 0 from
    congrFun (congrFun (coe_Tg_zpow M n) 0) 0]
  simp

theorem bP_Tg_zpow (n : ℤ) : bP p M (Tg M ^ n) = (n : ZMod p) := by
  simp only [bP]
  rw [show ((Tg M ^ n : Gamma0 M) : SL(2, ℤ)) 0 1 = (!![(1 : ℤ), n; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) 0 1 from
    congrFun (congrFun (coe_Tg_zpow M n) 0) 1]
  simp

theorem dP_Tg_zpow (n : ℤ) : dP p M (Tg M ^ n) = 1 := by
  simp only [dP]
  rw [show ((Tg M ^ n : Gamma0 M) : SL(2, ℤ)) 1 1 = (!![(1 : ℤ), n; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) 1 1 from
    congrFun (congrFun (coe_Tg_zpow M n) 1) 1]
  simp

end Entries

section Neben

variable (p : ℕ) [Fact p.Prime] (M : ℕ) (hpM : p ∣ M) (κ : Type*) [CommRing κ] [CharP κ p]

noncomputable abbrev cst : ZMod p →+* κ := ZMod.castHom (dvd_refl p) κ

theorem gamma0NebenChar_eq (e : ℕ) (γ : Gamma0 M) :
    gamma0NebenChar p M hpM κ e γ = (cst p κ (dP p M γ)) ^ e := by
  rw [gamma0NebenChar_apply]
  congr 2
  rw [ZMod.castHom_apply, ZMod.cast_intCast hpM]
  rfl

include hpM in

theorem cst_dP_pow_sub_one (γ : Gamma0 M) : (cst p κ (dP p M γ)) ^ (p - 1) = 1 := by
  rw [← map_pow, ZMod.pow_card_sub_one_eq_one (dP_ne_zero p M hpM γ), map_one]

theorem gamma0NebenRep_eq_of_modEq {e e' : ℕ} (h : e ≡ e' [MOD (p - 1)]) :
    gamma0NebenRep p M hpM κ e = gamma0NebenRep p M hpM κ e' := by
  refine MonoidHom.ext fun γ => LinearMap.ext fun v => ?_
  rw [gamma0NebenRep_apply, gamma0NebenRep_apply, gamma0NebenChar_eq, gamma0NebenChar_eq]
  congr 1
  set u := cst p κ (dP p M γ)
  have hu : u ^ (p - 1) = 1 := cst_dP_pow_sub_one p M hpM κ γ
  rw [← Nat.mod_add_div e (p - 1), ← Nat.mod_add_div e' (p - 1), pow_add, pow_add, pow_mul, pow_mul, hu,
    one_pow, one_pow, mul_one, mul_one, h]

theorem gamma0NebenRep_eq_one_of_dvd {e : ℕ} (h : (p - 1) ∣ e) : gamma0NebenRep p M hpM κ e = 1 := by
  rw [gamma0NebenRep_eq_of_modEq p M hpM κ (e' := 0) ((Nat.modEq_zero_iff_dvd.mpr h)), gamma0NebenRep_zero]

theorem natCast_pow_sub_one {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) : ((ℓ : κ)) ^ (p - 1) = 1 := by
  have hℓ0 : (ℓ : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out hℓ).mp h).symm
  have := ZMod.pow_card_sub_one_eq_one hℓ0
  have h2 := congrArg (cst p κ) this
  rwa [map_pow, map_natCast, map_one] at h2

theorem natCast_pow_eq_one_of_dvd {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) {t : ℕ} (ht : (p - 1) ∣ t) :
    ((ℓ : κ)) ^ t = 1 := by
  obtain ⟨s, rfl⟩ := ht
  rw [pow_mul, natCast_pow_sub_one p κ hℓ hℓp, one_pow]

end Neben

section Trivial

variable (p : ℕ) [Fact p.Prime] (M : ℕ) (hpM : p ∣ M) (S₀ : Set ℕ) (e t : ℕ)
variable (κ : Type) [Field κ] [CharP κ p] (nu : ℕ → κ)

theorem trivial_case (he : (p - 1) ∣ e) (ht : (p - 1) ∣ t)
    (hocc : IsEigensystemH1 M (gamma0NebenRep p M hpM κ e) (fun _ => LinearMap.id) S₀ nu) :
    ∃ (M' : ℕ) (mu : ℕ → κ), M ∣ M' ∧ M' ∣ M * p ∧
      IsEigensystemH1 M' (1 : Representation κ (Gamma0 M') κ) (fun _ => LinearMap.id) (insert p S₀) mu ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ≠ p → ℓ ∉ S₀ → mu ℓ = (ℓ : κ) ^ t * nu ℓ := by
  refine ⟨M, fun ℓ => (ℓ : κ) ^ t * nu ℓ, dvd_rfl, dvd_mul_right M p, ?_, fun _ _ _ _ _ => rfl⟩
  rw [gamma0NebenRep_eq_one_of_dvd p M hpM κ he] at hocc
  refine isEigensystemH1_mono M _ _ (Set.subset_insert p S₀) (isEigensystemH1_congr M _ _ S₀ ?_ hocc)
  intro ℓ hℓ hℓM _
  have hℓp : ℓ ≠ p := fun h => hℓM (h ▸ hpM)
  rw [natCast_pow_eq_one_of_dvd p κ hℓ hℓp ht, one_mul]

end Trivial

section W

variable (p : ℕ) [Fact p.Prime] (M : ℕ) (hpM : p ∣ M) (κ : Type*) [CommRing κ] [CharP κ p]

def rhoFun (γ : Gamma0 M) : (ZMod p → κ) →ₗ[κ] (ZMod p → κ) where
  toFun f u := f (dP p M γ * (dP p M γ * u - bP p M γ))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem rhoFun_apply (γ : Gamma0 M) (f : ZMod p → κ) (u : ZMod p) :
    rhoFun p M κ γ f u = f (dP p M γ * (dP p M γ * u - bP p M γ)) := rfl

def rhoW : Representation κ (Gamma0 M) (ZMod p → κ) where
  toFun := rhoFun p M κ
  map_one' := by
    refine LinearMap.ext fun f => funext fun u => ?_
    rw [rhoFun_apply, dP_one, bP_one]
    simp
  map_mul' γ γ' := by
    refine LinearMap.ext fun f => funext fun u => ?_
    rw [Module.End.mul_apply, rhoFun_apply, rhoFun_apply, rhoFun_apply, dP_mul p M hpM, bP_mul]
    congr 1
    linear_combination (-(dP p M γ' * bP p M γ')) * aP_mul_dP p M hpM γ

@[scoped simp] theorem rhoW_apply (γ : Gamma0 M) (f : ZMod p → κ) (u : ZMod p) :
    rhoW p M hpM κ γ f u = f (dP p M γ * (dP p M γ * u - bP p M γ)) := rfl

def aW (ℓ : ℕ) : (ZMod p → κ) →ₗ[κ] (ZMod p → κ) where
  toFun f u := f ((ℓ : ZMod p)⁻¹ * u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem aW_apply (ℓ : ℕ) (f : ZMod p → κ) (u : ZMod p) : aW p κ ℓ f u = f ((ℓ : ZMod p)⁻¹ * u) := rfl

theorem aW_comm (ℓ ℓ' : ℕ) : aW p κ ℓ ∘ₗ aW p κ ℓ' = aW p κ ℓ' ∘ₗ aW p κ ℓ := by
  refine LinearMap.ext fun f => funext fun u => ?_
  simp only [LinearMap.comp_apply, aW_apply]
  ring_nf

theorem isCompat_W (ℓ : ℕ) [NeZero ℓ] (hℓp : (ℓ : ZMod p) ≠ 0) : IsCompat M ℓ (rhoW p M hpM κ) (aW p κ ℓ) := by
  intro u
  refine LinearMap.ext fun f => funext fun w => ?_
  simp only [LinearMap.comp_apply, aW_apply, rhoW_apply]

  have hd : dP p M (heckeConj M ℓ u) = dP p M (u : Gamma0 M) := rfl
  have hb : bP p M (heckeConj M ℓ u) = (ℓ : ZMod p)⁻¹ * bP p M (u : Gamma0 M) := by
    simp only [bP]
    show (((((u : Gamma0 M) : SL(2, ℤ)) 0 1 / (ℓ : ℤ) : ℤ)) : ZMod p) = _
    obtain ⟨k, hk⟩ := (mem_heckeUpper M ℓ).mp u.2
    rw [hk, Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr (NeZero.ne ℓ))]
    push_cast
    rw [← mul_assoc, inv_mul_cancel₀ hℓp, one_mul]
  rw [hd, hb]
  congr 1
  ring

def ev0 : (ZMod p → κ) →ₗ[κ] κ where
  toFun f := f 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem ev0_apply (f : ZMod p → κ) : ev0 p κ f = f 0 := rfl

theorem ev0_aW (ℓ : ℕ) : ev0 p κ ∘ₗ aW p κ ℓ = (1 : κ) • ev0 p κ := by
  refine LinearMap.ext fun f => ?_
  simp

theorem ev0_rhoW (δ : Gamma0 M) (hδ : (p : ℤ) ∣ (δ : SL(2, ℤ)) 0 1) :
    ev0 p κ ∘ₗ rhoW p M hpM κ δ = ev0 p κ := by
  refine LinearMap.ext fun f => ?_
  have hb : bP p M δ = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hδ
  simp [hb]

def pt (γ : Gamma0 M) : ZMod p := aP p M γ * bP p M γ

theorem cocycle_one {z : Gamma0 M → ZMod p → κ} (hz : z ∈ coeffCocycles (rhoW p M hpM κ)) : z 1 = 0 := by
  have h := hz 1 1
  rw [mul_one, map_one, Module.End.one_apply] at h
  have : z 1 + z 1 = z 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel this

theorem cocycle_inv {z : Gamma0 M → ZMod p → κ} (hz : z ∈ coeffCocycles (rhoW p M hpM κ)) (γ : Gamma0 M) :
    z γ⁻¹ = -(rhoW p M hpM κ γ⁻¹ (z γ)) := by
  have h := hz γ⁻¹ γ
  rw [inv_mul_cancel, cocycle_one p M hpM κ hz] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem mem_coeffCoboundaries_of_forall_apply_zero {z : Gamma0 M → ZMod p → κ}
    (hz : z ∈ coeffCocycles (rhoW p M hpM κ))
    (h0 : ∀ h : Gamma0 M, (p : ℤ) ∣ (h : SL(2, ℤ)) 0 1 → z h 0 = 0) :
    z ∈ coeffCoboundaries (rhoW p M hpM κ) := by

  let f : ZMod p → κ := fun u => z (Tg M ^ (u.val : ℤ)) u

  have hkey : ∀ γ : Gamma0 M, z γ (pt p M γ) = f (pt p M γ) := by
    intro γ
    set n : ℤ := ((pt p M γ).val : ℤ) with hn
    have hncast : ((n : ℤ) : ZMod p) = pt p M γ := by
      rw [hn, Int.cast_natCast, ZMod.natCast_zmod_val]
    set h : Gamma0 M := (Tg M ^ n)⁻¹ * γ with hh
    have hγ : γ = Tg M ^ n * h := by rw [hh, mul_inv_cancel_left]
    have hbh : bP p M h = 0 := by
      rw [hh, bP_mul, aP_inv p M hpM, bP_inv, dP_Tg_zpow, bP_Tg_zpow, hncast, pt, one_mul]
      linear_combination (-bP p M γ) * aP_mul_dP p M hpM γ
    have hzh : z h 0 = 0 := h0 h ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hbh)
    have h1 : z γ = z (Tg M ^ n) + rhoW p M hpM κ (Tg M ^ n) (z h) := by
      conv_lhs => rw [hγ]
      exact hz _ _
    rw [h1, Pi.add_apply, rhoW_apply, dP_Tg_zpow, bP_Tg_zpow, hncast, one_mul, one_mul, sub_self, hzh, add_zero]

  have hmove : ∀ (γ δ : Gamma0 M), pt p M (γ⁻¹ * δ) = dP p M γ * (dP p M γ * pt p M δ - bP p M γ) := by
    intro γ δ
    rw [pt, aP_mul p M hpM, bP_mul, aP_inv p M hpM, bP_inv, pt]
    have h1 := aP_mul_dP p M hpM δ
    linear_combination (-(dP p M γ * bP p M γ)) * h1
  have hback : ∀ (γ : Gamma0 M) (u : ZMod p),
      dP p M γ⁻¹ * (dP p M γ⁻¹ * (dP p M γ * (dP p M γ * u - bP p M γ)) - bP p M γ⁻¹) = u := by
    intro γ u
    rw [dP_inv p M hpM, bP_inv]
    have h1 := aP_mul_dP p M hpM γ
    linear_combination (aP p M γ * dP p M γ * u + u - aP p M γ * bP p M γ) * h1
  refine (mem_coeffCoboundaries_iff _ _).mpr ⟨-f, funext fun γ => funext fun u => ?_⟩

  set δ : Gamma0 M := Tg M ^ (u.val : ℤ) with hδ
  have hptδ : pt p M δ = u := by
    rw [pt, hδ, aP_Tg_zpow, bP_Tg_zpow, one_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hfu : f u = z δ u := rfl

  have hA : rhoW p M hpM κ γ f u = f (pt p M (γ⁻¹ * δ)) := by rw [rhoW_apply, hmove, hptδ]
  have hB : f (pt p M (γ⁻¹ * δ)) = z (γ⁻¹ * δ) (pt p M (γ⁻¹ * δ)) := (hkey _).symm
  have hC : z (γ⁻¹ * δ) (pt p M (γ⁻¹ * δ)) = -(z γ u) + z δ u := by
    rw [hz γ⁻¹ δ, Pi.add_apply, cocycle_inv p M hpM κ hz γ, Pi.neg_apply, rhoW_apply, rhoW_apply, hmove, hptδ]
    simp only [hback]
  show (rhoW p M hpM κ γ (-f)) u - (-f) u = z γ u
  rw [map_neg, Pi.neg_apply, hA, hB, hC, Pi.neg_apply, hfu]
  ring

end W

section Flag

variable (p : ℕ) [Fact p.Prime] (M : ℕ) (hpM : p ∣ M) (κ : Type*) [Field κ] [CharP κ p]

noncomputable def mono (j : ℕ) : ZMod p → κ := fun u => (cst p κ u) ^ j

@[scoped simp] theorem mono_apply (j : ℕ) (u : ZMod p) : mono p κ j u = (cst p κ u) ^ j := rfl

theorem linearIndependent_mono : LinearIndependent κ (fun j : Fin p => mono p κ j.val) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  set P : Polynomial κ := ∑ i : Fin p, Polynomial.C (g i) * Polynomial.X ^ (i : ℕ) with hP
  have hdeg : P.degree < p := Polynomial.degree_sum_fin_lt g
  have hnat : P.natDegree < Fintype.card (ZMod p) := by
    rw [ZMod.card]
    by_cases hP0 : P = 0
    · rw [hP0, Polynomial.natDegree_zero]; exact (Fact.out : p.Prime).pos
    · exact (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hdeg
  have heval : ∀ u : ZMod p, P.eval (cst p κ u) = 0 := by
    intro u
    have h := congrFun hg u
    simp only [Finset.sum_apply, Pi.smul_apply, mono_apply, smul_eq_mul, Pi.zero_apply] at h
    rw [hP, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact h
  have hP0 : P = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P (cst p κ).injective heval hnat
  have hcoeff : P.coeff j = g j := by
    rw [hP, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [if_neg]
      exact fun h => hij (Fin.ext h.symm)
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [← hcoeff, hP0, Polynomial.coeff_zero]

theorem affine_pow_eq_sum (x y : κ) (n : ℕ) :
    (fun u : ZMod p => (x * cst p κ u + y) ^ n)
      = ∑ m ∈ Finset.range (n + 1), (x ^ m * y ^ (n - m) * (n.choose m : κ)) • mono p κ m := by
  funext u
  rw [add_pow, Finset.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Pi.smul_apply, mono_apply, smul_eq_mul, mul_pow]
  ring

private theorem _root_.TwistMain.span_mono : ⊤ ≤ Submodule.span κ (Set.range (fun j : Fin p => mono p κ j.val)) := by
  classical
  intro f _
  set S := Submodule.span κ (Set.range (fun j : Fin p => mono p κ j.val)) with hS
  have hmono : ∀ m : ℕ, m < p → mono p κ m ∈ S := fun m hm => Submodule.subset_span ⟨⟨m, hm⟩, rfl⟩
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).one_le

  have hind : ∀ v : ZMod p, (fun u : ZMod p => if u = v then (1 : κ) else 0) ∈ S := by
    intro v
    have heq : (fun u : ZMod p => if u = v then (1 : κ) else 0)
        = mono p κ 0 - (fun u : ZMod p => (1 * cst p κ u + (-(cst p κ v))) ^ (p - 1)) := by
      funext u
      simp only [Pi.sub_apply, mono_apply, pow_zero, one_mul]
      by_cases huv : u = v
      · rw [if_pos huv, huv, add_neg_cancel, zero_pow (Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt),
          sub_zero]
      · rw [if_neg huv, ← sub_eq_add_neg, ← map_sub, ← map_pow,
          ZMod.pow_card_sub_one_eq_one (sub_ne_zero.mpr huv), map_one, sub_self]
    rw [heq, affine_pow_eq_sum]
    refine Submodule.sub_mem _ (hmono 0 (Fact.out : p.Prime).pos) (Submodule.sum_mem _ fun m hm => ?_)
    refine Submodule.smul_mem _ _ (hmono m ?_)
    rw [hp1] at hm
    exact Finset.mem_range.mp hm
  have hf : f = ∑ v : ZMod p, f v • (fun u : ZMod p => if u = v then (1 : κ) else 0) := by
    funext u
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  rw [hf]
  exact Submodule.sum_mem _ fun v _ => Submodule.smul_mem _ _ (hind v)

p2m_export "TwistMain" "span_mono"

noncomputable def basisW : Module.Basis (Fin p) κ (ZMod p → κ) :=
  Module.Basis.mk (linearIndependent_mono p κ) (span_mono p κ)

theorem basisW_apply (i : Fin p) : basisW p κ i = mono p κ i.val := by
  rw [basisW, Module.Basis.coe_mk]

noncomputable def Wk (k : ℕ) : Submodule κ (ZMod p → κ) :=
  Submodule.span κ (basisW p κ '' {i : Fin p | i.val ≤ k})

theorem mem_Wk_iff {k : ℕ} {f : ZMod p → κ} :
    f ∈ Wk p κ k ↔ ∀ i : Fin p, (basisW p κ).repr f i ≠ 0 → i.val ≤ k := by
  rw [Wk, Module.Basis.mem_span_image]
  constructor
  · intro h i hi
    exact h (Finsupp.mem_support_iff.mpr hi)
  · intro h i hi
    exact h i (Finsupp.mem_support_iff.mp hi)

theorem basisW_mem_Wk {k : ℕ} {i : Fin p} (hi : i.val ≤ k) : basisW p κ i ∈ Wk p κ k :=
  Submodule.subset_span ⟨i, hi, rfl⟩

theorem mono_mem_Wk {k m : ℕ} (hm : m ≤ k) (hmp : m < p) : mono p κ m ∈ Wk p κ k := by
  rw [← basisW_apply p κ ⟨m, hmp⟩]
  exact basisW_mem_Wk p κ hm

theorem Wk_mono {k k' : ℕ} (h : k ≤ k') : Wk p κ k ≤ Wk p κ k' :=
  Submodule.span_mono (Set.image_mono fun _ hi => le_trans hi h)

theorem Wk_eq_top {k : ℕ} (hk : p - 1 ≤ k) : Wk p κ k = ⊤ := by
  rw [Wk, show {i : Fin p | i.val ≤ k} = Set.univ from
    Set.eq_univ_of_forall fun i => le_trans (Nat.le_sub_one_of_lt i.2) hk, Set.image_univ]
  exact (basisW p κ).span_eq

theorem sum_smul_mono_mem_Wk {k n : ℕ} (hn : n ≤ k) (hkp : k < p) (c : ℕ → κ) :
    ∑ m ∈ Finset.range (n + 1), c m • mono p κ m ∈ Wk p κ k :=
  Submodule.sum_mem _ fun m hm =>
    Submodule.smul_mem _ _ (mono_mem_Wk p κ (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) hn)
      (lt_of_le_of_lt (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) hn) hkp))

theorem rhoW_mono (γ : Gamma0 M) (n : ℕ) :
    rhoW p M hpM κ γ (mono p κ n)
      = ∑ m ∈ Finset.range (n + 1),
          ((cst p κ (dP p M γ)) ^ (2 * m) * (cst p κ (-(dP p M γ * bP p M γ))) ^ (n - m) * (n.choose m : κ))
            • mono p κ m := by
  have h : rhoW p M hpM κ γ (mono p κ n)
      = fun u : ZMod p => (cst p κ (dP p M γ) ^ 2 * cst p κ u + cst p κ (-(dP p M γ * bP p M γ))) ^ n := by
    funext u
    rw [rhoW_apply, mono_apply]
    congr 1
    simp only [map_mul, map_sub, map_neg]
    ring
  rw [h, affine_pow_eq_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← pow_mul]

theorem aW_mono (ℓ n : ℕ) : aW p κ ℓ (mono p κ n) = (cst p κ ((ℓ : ZMod p)⁻¹)) ^ n • mono p κ n := by
  funext u
  simp only [aW_apply, mono_apply, Pi.smul_apply, smul_eq_mul, map_mul, mul_pow]

theorem rhoW_Tinv_mono (n : ℕ) :
    rhoW p M hpM κ (Tg M)⁻¹ (mono p κ n) = ∑ m ∈ Finset.range (n + 1), ((n.choose m : κ)) • mono p κ m := by
  have h : rhoW p M hpM κ (Tg M)⁻¹ (mono p κ n) = fun u : ZMod p => (1 * cst p κ u + 1) ^ n := by
    funext u
    rw [rhoW_apply, mono_apply, dP_inv p M hpM, bP_inv, show Tg M = Tg M ^ (1 : ℤ) from (zpow_one _).symm,
      aP_Tg_zpow, bP_Tg_zpow]
    simp
  rw [h, affine_pow_eq_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp

theorem rhoW_mem_Wk {k : ℕ} (hkp : k < p) (γ : Gamma0 M) {f : ZMod p → κ} (hf : f ∈ Wk p κ k) :
    rhoW p M hpM κ γ f ∈ Wk p κ k := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    rw [basisW_apply, rhoW_mono p M hpM κ γ i.val]
    exact sum_smul_mono_mem_Wk p κ hi hkp _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem aW_mem_Wk {k : ℕ} (ℓ : ℕ) {f : ZMod p → κ} (hf : f ∈ Wk p κ k) : aW p κ ℓ f ∈ Wk p κ k := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    rw [basisW_apply, aW_mono]
    exact Submodule.smul_mem _ _ (mono_mem_Wk p κ hi i.2)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

noncomputable def coordW (k : Fin p) : (ZMod p → κ) →ₗ[κ] κ := (basisW p κ).coord k

theorem coordW_apply (k : Fin p) (f : ZMod p → κ) : coordW p κ k f = (basisW p κ).repr f k := rfl

theorem coordW_mono (k : Fin p) {m : ℕ} (hm : m < p) : coordW p κ k (mono p κ m) = if m = k.val then 1 else 0 := by
  rw [coordW_apply, ← basisW_apply p κ ⟨m, hm⟩, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases h : m = k.val
  · rw [if_pos h, if_pos (Fin.ext h)]
  · rw [if_neg h, if_neg (fun h' => h (congrArg Fin.val h'))]

theorem coordW_eq_zero_of_mem_Wk {j : ℕ} {k : Fin p} (hjk : j < k.val) {f : ZMod p → κ} (hf : f ∈ Wk p κ j) :
    coordW p κ k f = 0 := by
  by_contra h
  exact absurd ((mem_Wk_iff p κ).mp hf k h) (not_le.mpr hjk)

theorem coordW_sum_range (k : Fin p) {n : ℕ} (hn : n ≤ k.val) (c : ℕ → κ) :
    coordW p κ k (∑ m ∈ Finset.range (n + 1), c m • mono p κ m) = if n = k.val then c n else 0 := by
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  have hval : ∀ m ∈ Finset.range (n + 1), c m * coordW p κ k (mono p κ m) = if m = k.val then c m else 0 := by
    intro m hm
    have hmp : m < p := lt_of_le_of_lt (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) hn) k.2
    rw [coordW_mono p κ k hmp]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hval, Finset.sum_ite_eq']
  by_cases h : n = k.val
  · rw [if_pos h, if_pos (Finset.mem_range.mpr (by omega)), h]
  · rw [if_neg h, if_neg]
    intro hmem
    have := Finset.mem_range.mp hmem
    omega

theorem coordW_rhoW (k : Fin p) (γ : Gamma0 M) {f : ZMod p → κ} (hf : f ∈ Wk p κ k.val) :
    coordW p κ k (rhoW p M hpM κ γ f) = (cst p κ (dP p M γ)) ^ (2 * k.val) * coordW p κ k f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    rw [basisW_apply, rhoW_mono p M hpM κ γ i.val, coordW_sum_range p κ k hi, coordW_mono p κ k i.2]
    by_cases h : i.val = k.val
    · rw [if_pos h, if_pos h, h, Nat.sub_self, pow_zero, Nat.choose_self]; simp
    · rw [if_neg h, if_neg h, mul_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, map_add, mul_add]
  | smul c x _ hx => rw [map_smul, map_smul, hx, map_smul, smul_eq_mul, smul_eq_mul, mul_left_comm]

theorem coordW_aW (k : Fin p) (ℓ : ℕ) {f : ZMod p → κ} (hf : f ∈ Wk p κ k.val) :
    coordW p κ k (aW p κ ℓ f) = (cst p κ ((ℓ : ZMod p)⁻¹)) ^ k.val * coordW p κ k f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    rw [basisW_apply, aW_mono, map_smul, coordW_mono p κ k i.2, smul_eq_mul]
    by_cases h : i.val = k.val
    · rw [if_pos h, h]
    · rw [if_neg h, mul_zero, mul_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, map_add, mul_add]
  | smul c x _ hx => rw [map_smul, map_smul, hx, map_smul, smul_eq_mul, smul_eq_mul, mul_left_comm]

theorem exists_sub_smul_mem_Wk_of_Tinv {k : ℕ} (hk : k + 1 < p) {f : ZMod p → κ}
    (hf : rhoW p M hpM κ (Tg M)⁻¹ f - f ∈ Wk p κ k) :
    ∃ r : κ, f - r • mono p κ (k + 1) ∈ Wk p κ k := by
  classical
  set B := basisW p κ with hB
  set r : Fin p → κ := fun i => B.repr f i with hr
  have hfsum : f = ∑ i : Fin p, r i • B i := (B.sum_repr f).symm

  have hΔB : ∀ i : Fin p, rhoW p M hpM κ (Tg M)⁻¹ (B i) - B i
      = ∑ m ∈ Finset.range i.val, ((i.val.choose m : κ)) • mono p κ m := by
    intro i
    rw [hB, basisW_apply, rhoW_Tinv_mono, Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_smul,
      add_sub_cancel_right]
  have hcoordΔ : ∀ j : Fin p, coordW p κ j (rhoW p M hpM κ (Tg M)⁻¹ f - f)
      = ∑ i : Fin p, if j.val < i.val then r i * (i.val.choose j.val : κ) else 0 := by
    intro j
    conv_lhs => rw [hfsum]
    rw [map_sum, ← Finset.sum_sub_distrib, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ← smul_sub, map_smul, hΔB, smul_eq_mul, map_sum]
    simp only [map_smul, smul_eq_mul]
    by_cases hji : j.val < i.val
    · rw [if_pos hji]
      have hval : ∀ m ∈ Finset.range i.val, (i.val.choose m : κ) * coordW p κ j (mono p κ m)
          = if m = j.val then (i.val.choose m : κ) else 0 := by
        intro m hm
        rw [coordW_mono p κ j (lt_trans (Finset.mem_range.mp hm) i.2)]
        split_ifs <;> simp
      rw [Finset.sum_congr rfl hval, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hji)]
    · rw [if_neg hji]
      have hval : ∀ m ∈ Finset.range i.val, (i.val.choose m : κ) * coordW p κ j (mono p κ m) = 0 := by
        intro m hm
        rw [coordW_mono p κ j (lt_trans (Finset.mem_range.mp hm) i.2), if_neg, mul_zero]
        intro hmj
        exact hji (hmj ▸ Finset.mem_range.mp hm)
      rw [Finset.sum_congr rfl hval, Finset.sum_const_zero, mul_zero]

  have hvan : ∀ i : Fin p, k + 1 < i.val → r i = 0 := by
    by_contra hcon
    push_neg at hcon
    set S : Finset (Fin p) := Finset.univ.filter fun i => k + 1 < i.val ∧ r i ≠ 0 with hS
    have hSne : S.Nonempty := by
      obtain ⟨i, hi, hri⟩ := hcon
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, hri⟩⟩
    set i₁ := S.max' hSne with hi₁
    have hi₁S : i₁ ∈ S := Finset.max'_mem S hSne
    obtain ⟨-, hi₁k, hri₁⟩ := Finset.mem_filter.mp hi₁S
    have hmax : ∀ i : Fin p, i₁ < i → k + 1 < i.val → r i = 0 := by
      intro i hi hik
      by_contra hri
      have : i ≤ i₁ := Finset.le_max' S i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hik, hri⟩)
      exact absurd hi (not_lt.mpr this)
    have hjp : i₁.val - 1 < p := lt_of_le_of_lt (Nat.sub_le _ _) i₁.2
    set j : Fin p := ⟨i₁.val - 1, hjp⟩ with hj
    have hjk : k < j.val := by change k < i₁.val - 1; omega
    have hzero : coordW p κ j (rhoW p M hpM κ (Tg M)⁻¹ f - f) = 0 := coordW_eq_zero_of_mem_Wk p κ hjk hf
    rw [hcoordΔ j, Finset.sum_eq_single i₁] at hzero
    · rw [if_pos (by change i₁.val - 1 < i₁.val; omega)] at hzero
      have hchoose : (i₁.val.choose j.val : κ) = (i₁.val : κ) := by
        have hn : i₁.val = j.val + 1 := by change i₁.val = (i₁.val - 1) + 1; omega
        rw [hn, Nat.choose_succ_self_right]
      rw [hchoose] at hzero
      rcases mul_eq_zero.mp hzero with h | h
      · exact hri₁ h
      · rw [CharP.cast_eq_zero_iff κ p] at h
        have := Nat.le_of_dvd (by omega) h
        exact absurd this (not_le.mpr i₁.2)
    · intro i _ hne
      by_cases hlt : j.val < i.val
      · rw [if_pos hlt]
        change i₁.val - 1 < i.val at hlt
        have hne' : i.val ≠ i₁.val := fun h => hne (Fin.ext h)
        have hgt : i₁ < i := by rw [Fin.lt_def]; omega
        rw [hmax i hgt (by omega), zero_mul]
      · rw [if_neg hlt]
    · intro h; exact absurd (Finset.mem_univ i₁) h
  refine ⟨if h : k + 1 < p then r ⟨k + 1, h⟩ else 0, ?_⟩
  rw [dif_pos hk]
  rw [(mem_Wk_iff p κ)]
  intro i hi
  by_contra hik
  push_neg at hik
  apply hi
  rw [map_sub, map_smul, ← basisW_apply p κ ⟨k + 1, hk⟩, B.repr_self, Finsupp.sub_apply, Finsupp.smul_apply,
    Finsupp.single_apply]
  by_cases hieq : (⟨k + 1, hk⟩ : Fin p) = i
  · rw [if_pos hieq, smul_eq_mul, mul_one, ← hieq, sub_self]
  · rw [if_neg hieq, smul_zero, sub_zero]
    have hik' : k + 1 < i.val := lt_of_le_of_ne hik fun h => hieq (Fin.ext h)
    exact hvan i hik'

theorem exists_sub_smul_mem_Wk {k : ℕ} (hk : k + 1 < p) {f : ZMod p → κ}
    (hf : ∀ γ : Gamma0 M, rhoW p M hpM κ γ f - f ∈ Wk p κ k) :
    ∃ r : κ, f - r • mono p κ (k + 1) ∈ Wk p κ k :=
  exists_sub_smul_mem_Wk_of_Tinv p M hpM κ hk (hf _)

end Flag

section Generic

variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M)

include hpM in

theorem exists_dP_eq (u₀ : (ZMod p)ˣ) : ∃ γ : Gamma0 M, dP p M γ = u₀ := by
  have hp : p.Prime := Fact.out
  set M₀ := ordCompl[p] M with hM₀
  have hco : p.Coprime M₀ := Nat.coprime_ordCompl hp (NeZero.ne M)
  set d₀ : ℕ := (u₀ : ZMod p).val with hd₀
  obtain ⟨d, hdp, hdM₀⟩ := Nat.chineseRemainder hco d₀ 1

  have hd_cast : (d : ZMod p) = (u₀ : ZMod p) := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hdp, hd₀, ZMod.natCast_zmod_val]
  have hdp' : Nat.Coprime d p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have : (d : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff d p).mpr h
    rw [hd_cast] at this
    exact u₀.ne_zero this
  have hdM₀' : Nat.Coprime d M₀ := by
    rw [Nat.Coprime, hdM₀.gcd_eq, Nat.gcd_one_left]
  have hdM : Nat.Coprime d M := by
    rw [← Nat.ordProj_mul_ordCompl_eq_self M p]
    exact (hdp'.pow_right _).mul_right hdM₀'

  have hbez : ((d : ℤ)) * Int.gcdA d M + (M : ℤ) * Int.gcdB d M = 1 := by
    have h := Int.gcd_eq_gcd_ab (d : ℤ) (M : ℤ)
    rw [Int.gcd_natCast_natCast, hdM, Nat.cast_one] at h
    exact h.symm
  set A : Matrix (Fin 2) (Fin 2) ℤ := !![Int.gcdA d M, -Int.gcdB d M; (M : ℤ), (d : ℤ)] with hA
  have hdet : A.det = 1 := by
    rw [hA, Matrix.det_fin_two_of]
    linear_combination hbez
  refine ⟨⟨⟨A, hdet⟩, ?_⟩, ?_⟩
  · rw [Gamma0_mem]
    show (((M : ℤ)) : ZMod M) = 0
    simp
  · show (((d : ℤ)) : ZMod p) = _
    rw [Int.cast_natCast, hd_cast]

include hpM in

theorem sub_one_dvd_of_forall_pow_eq_one (n : ℕ) (h : ∀ γ : Gamma0 M, (dP p M γ) ^ n = 1) : (p - 1) ∣ n := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have horder : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  obtain ⟨γ, hγ⟩ := exists_dP_eq p M hpM g
  have hgn : g ^ n = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, ← hγ, h γ, Units.val_one]
  rw [← horder]
  exact orderOf_dvd_of_pow_eq_one hgn

end Generic

section Layer

variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (κ : Type) [Field κ] [CharP κ p] (S₀ : Set ℕ)

noncomputable def cW (j ℓ : ℕ) : κ := (cst p κ ((ℓ : ZMod p)⁻¹)) ^ j

noncomputable def rhoWk {j : ℕ} (hj : j < p) : Representation κ (Gamma0 M) ↥(Wk p κ j) where
  toFun γ := (rhoW p M hpM κ γ).restrict fun _ hf => rhoW_mem_Wk p M hpM κ hj γ hf
  map_one' := LinearMap.ext fun f => Subtype.ext (by simp)
  map_mul' γ γ' := LinearMap.ext fun f => Subtype.ext (by simp)

@[scoped simp] theorem coe_rhoWk {j : ℕ} (hj : j < p) (γ : Gamma0 M) (f : ↥(Wk p κ j)) :
    ((rhoWk p M hpM κ hj γ f : ↥(Wk p κ j)) : ZMod p → κ) = rhoW p M hpM κ γ f := rfl

noncomputable def aWk (j ℓ : ℕ) : ↥(Wk p κ j) →ₗ[κ] ↥(Wk p κ j) :=
  (aW p κ ℓ).restrict fun _ hf => aW_mem_Wk p κ ℓ hf

@[scoped simp] theorem coe_aWk (j ℓ : ℕ) (f : ↥(Wk p κ j)) : ((aWk p κ j ℓ f : ↥(Wk p κ j)) : ZMod p → κ) = aW p κ ℓ f := rfl

include hpM in
theorem natCast_zmod_ne_zero {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) : (ℓ : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  exact hℓM (((Nat.prime_dvd_prime_iff_eq Fact.out hℓ).mp h) ▸ hpM)

theorem isCompat_Wk {j : ℕ} (hj : j < p) (ℓ : ℕ) [NeZero ℓ] (hℓ0 : (ℓ : ZMod p) ≠ 0) :
    IsCompat M ℓ (rhoWk p M hpM κ hj) (aWk p κ j ℓ) := by
  intro u
  refine LinearMap.ext fun f => Subtype.ext ?_
  exact LinearMap.congr_fun (isCompat_W p M hpM κ ℓ hℓ0 u) (f : ZMod p → κ)

theorem cW_pow_sub_one {ℓ : ℕ} (hℓ0 : (ℓ : ZMod p) ≠ 0) : cW p κ (p - 1) ℓ = 1 := by
  rw [cW, ← map_pow, ZMod.pow_card_sub_one_eq_one (inv_ne_zero hℓ0), map_one]

theorem cW_zero (ℓ : ℕ) : cW p κ 0 ℓ = 1 := pow_zero _

theorem layer (h6 : (6 : κ) ≠ 0) {j : ℕ} (hj : j < p) (τ : ℕ → κ)
    (hτ : IsEigensystemH1 M (gamma0NebenRep p M hpM κ (2 * j)) (fun ℓ => cW p κ j ℓ • LinearMap.id) S₀ τ) :
    IsEigensystemH1 M (rhoW p M hpM κ) (aW p κ) S₀ τ ∨
      (j + 1 < p ∧ (p - 1) ∣ 2 * (j + 1) ∧
        ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S₀ → τ ℓ = ((ℓ : κ) + 1) * cW p κ (j + 1) ℓ) := by
  have haW : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S₀ →
      ∀ u : ↥(heckeUpper M ℓ), aW p κ ℓ ∘ₗ rhoW p M hpM κ (heckeConj M ℓ u)
        = rhoW p M hpM κ (u : Gamma0 M) ∘ₗ aW p κ ℓ :=
    fun ℓ _ hℓ hℓM _ => isCompat_W p M hpM κ ℓ (natCast_zmod_ne_zero p M hpM hℓ hℓM)
  have haWk : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S₀ →
      ∀ u : ↥(heckeUpper M ℓ), aWk p κ j ℓ ∘ₗ rhoWk p M hpM κ hj (heckeConj M ℓ u)
        = rhoWk p M hpM κ hj (u : Gamma0 M) ∘ₗ aWk p κ j ℓ :=
    fun ℓ _ hℓ hℓM _ => isCompat_Wk p M hpM κ hj ℓ (natCast_zmod_ne_zero p M hpM hℓ hℓM)
  have hcommW : ∀ ℓ ℓ' : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S₀ → ℓ'.Prime → ¬ ℓ' ∣ M → ℓ' ∉ S₀ →
      aW p κ ℓ ∘ₗ aW p κ ℓ' = aW p κ ℓ' ∘ₗ aW p κ ℓ := fun ℓ ℓ' _ _ _ _ _ _ => aW_comm p κ ℓ ℓ'
  have hcommWk : ∀ ℓ ℓ' : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S₀ → ℓ'.Prime → ¬ ℓ' ∣ M → ℓ' ∉ S₀ →
      aWk p κ j ℓ ∘ₗ aWk p κ j ℓ' = aWk p κ j ℓ' ∘ₗ aWk p κ j ℓ := by
    intro ℓ ℓ' _ _ _ _ _ _
    refine LinearMap.ext fun f => Subtype.ext ?_
    exact LinearMap.congr_fun (aW_comm p κ ℓ ℓ') (f : ZMod p → κ)

  set jf : Fin p := ⟨j, hj⟩ with hjf
  set π : ↥(Wk p κ j) →ₗ[κ] κ := coordW p κ jf ∘ₗ (Wk p κ j).subtype with hπ
  have hπρ : ∀ γ : Gamma0 M, π ∘ₗ rhoWk p M hpM κ hj γ = gamma0NebenRep p M hpM κ (2 * j) γ ∘ₗ π := by
    intro γ
    refine LinearMap.ext fun f => ?_
    change coordW p κ jf (rhoW p M hpM κ γ f) = gamma0NebenRep p M hpM κ (2 * j) γ (coordW p κ jf f)
    rw [gamma0NebenRep_apply, gamma0NebenChar_eq, coordW_rhoW p M hpM κ jf γ f.2]
  have hπa : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S₀ → π ∘ₗ aWk p κ j ℓ = (cW p κ j ℓ • LinearMap.id) ∘ₗ π := by
    intro ℓ _ _ _
    refine LinearMap.ext fun f => ?_
    change coordW p κ jf (aW p κ ℓ f) = cW p κ j ℓ • coordW p κ jf f
    rw [coordW_aW p κ jf ℓ f.2, cW, smul_eq_mul]
  have hπsurj : Function.Surjective π := by
    intro r
    refine ⟨r • ⟨mono p κ j, mono_mem_Wk p κ le_rfl hj⟩, ?_⟩
    rw [map_smul]
    change r • coordW p κ jf (mono p κ j) = r
    rw [coordW_mono p κ jf hj, if_pos rfl, smul_eq_mul, mul_one]
  have hpull : IsEigensystemH1 M (rhoWk p M hpM κ hj) (aWk p κ j) S₀ τ :=
    HeckeEis.isEigensystemH1_of_isEigensystemH1_of_surjective M h6 S₀ (rhoWk p M hpM κ hj)
      (gamma0NebenRep p M hpM κ (2 * j)) (aWk p κ j) (fun ℓ => cW p κ j ℓ • LinearMap.id) haWk hcommWk π hπρ
      hπa hπsurj τ hτ
  by_cases hj1 : j + 1 < p
  ·
    set ι : ↥(Wk p κ j) →ₗ[κ] (ZMod p → κ) := (Wk p κ j).subtype with hι
    have hrange : LinearMap.range ι = Wk p κ j := Submodule.range_subtype _
    have hιρ : ∀ γ : Gamma0 M, ι ∘ₗ rhoWk p M hpM κ hj γ = rhoW p M hpM κ γ ∘ₗ ι :=
      fun γ => LinearMap.ext fun _ => rfl
    have hιa : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S₀ → ι ∘ₗ aWk p κ j ℓ = aW p κ ℓ ∘ₗ ι :=
      fun ℓ _ _ _ => LinearMap.ext fun _ => rfl
    have hinj : Function.Injective ι := Subtype.val_injective
    have hq₀ : ∀ v : ZMod p → κ, (∀ g : Gamma0 M, rhoW p M hpM κ g v - v ∈ LinearMap.range ι) →
        ∃ r : κ, v - r • mono p κ (j + 1) ∈ LinearMap.range ι := by
      intro v hv
      rw [hrange] at hv ⊢
      exact exists_sub_smul_mem_Wk p M hpM κ hj1 hv
    have hc : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S₀ →
        aW p κ ℓ (mono p κ (j + 1)) - cW p κ (j + 1) ℓ • mono p κ (j + 1) ∈ LinearMap.range ι := by
      intro ℓ _ _ _
      rw [aW_mono, cW, sub_self]
      exact Submodule.zero_mem _
    rcases HeckeEis.isEigensystemH1_or_of_isEigensystemH1_of_injective M S₀ (rhoWk p M hpM κ hj)
        (rhoW p M hpM κ) (aWk p κ j) (aW p κ) haW ι hιρ hιa hinj (mono p κ (j + 1)) hq₀
        (cW p κ (j + 1)) hc τ hpull with hW | ⟨hinv, heis⟩
    · exact Or.inl hW
    · refine Or.inr ⟨hj1, ?_, heis⟩

      apply sub_one_dvd_of_forall_pow_eq_one p M hpM
      intro γ
      have hmem := hinv γ
      rw [hrange] at hmem
      set jf' : Fin p := ⟨j + 1, hj1⟩ with hjf'
      have h0 : coordW p κ jf' (rhoW p M hpM κ γ (mono p κ (j + 1)) - mono p κ (j + 1)) = 0 :=
        coordW_eq_zero_of_mem_Wk p κ (Nat.lt_succ_self j) hmem
      rw [map_sub, coordW_rhoW p M hpM κ jf' γ (mono_mem_Wk p κ le_rfl hj1), coordW_mono p κ jf' hj1,
        if_pos rfl, mul_one, sub_eq_zero, ← map_pow] at h0
      exact (cst p κ).injective (h0.trans (map_one _).symm)
  ·
    left
    have hjp : p - 1 ≤ j := by omega
    have htop : Wk p κ j = ⊤ := Wk_eq_top p κ hjp
    set e : ↥(Wk p κ j) ≃ₗ[κ] (ZMod p → κ) := LinearEquiv.ofTop (Wk p κ j) htop with he
    set π' : (ZMod p → κ) →ₗ[κ] ↥(Wk p κ j) := (e.symm : (ZMod p → κ) →ₗ[κ] ↥(Wk p κ j)) with hπ'
    have hπ'ρ : ∀ γ : Gamma0 M, π' ∘ₗ rhoW p M hpM κ γ = rhoWk p M hpM κ hj γ ∘ₗ π' :=
      fun γ => LinearMap.ext fun f => Subtype.ext rfl
    have hπ'a : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S₀ → π' ∘ₗ aW p κ ℓ = aWk p κ j ℓ ∘ₗ π' :=
      fun ℓ _ _ _ => LinearMap.ext fun f => Subtype.ext rfl
    exact HeckeEis.isEigensystemH1_of_isEigensystemH1_of_surjective M h6 S₀ (rhoW p M hpM κ)
      (rhoWk p M hpM κ hj) (aW p κ) (aWk p κ j) haW hcommW π' hπ'ρ hπ'a e.symm.surjective τ hpull

theorem final {τ mu : ℕ → κ} (hτ : IsEigensystemH1 M (rhoW p M hpM κ) (aW p κ) S₀ τ)
    (hmu : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S₀ → τ ℓ = mu ℓ) :
    IsEigensystemH1 (M * p) (1 : Representation κ (Gamma0 (M * p)) κ) (fun _ => LinearMap.id) (insert p S₀) mu := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨x, hx, heig⟩ := hτ
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective _ x
  obtain ⟨y, hy1, hy2⟩ := HeckeEis.exists_addMonoidHom_functional_cocycle_smul_heckeOperatorHom_mul_eq p M
    (rhoW p M hpM κ) (aW p κ) (ev0 p κ) (fun _ => (1 : κ)) (ev0_rhoW p M hpM κ) (ev0_aW p κ)
    (z : Gamma0 M → ZMod p → κ) z.2

  have hy0 : y ≠ 0 := by
    intro hy
    apply hx
    rw [coeffH1Mk_eq_zero_iff]
    refine mem_coeffCoboundaries_of_forall_apply_zero p M hpM κ z.2 fun h hh => ?_

    let u : ↥(heckeUpper M p) := ⟨h, (mem_heckeUpper M p).mpr hh⟩
    have hmem : heckeConjSL M p u ∈ Gamma0 (M * p) := by
      rw [Gamma0_mem]
      show (((heckeConjMat p ((h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 : ℤ) : ZMod (M * p)) = 0
      rw [heckeConjMat_apply_one_zero, ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      exact mul_dvd_mul_right (entry_c_dvd M h) _
    have hrel := hy1 ⟨heckeConjSL M p u, hmem⟩ h (heckeConjMat_mul_alphaMat hh)
    rw [hy, AddMonoidHom.zero_apply] at hrel
    exact hrel.symm

  let zy : Gamma0 (M * p) → κ := fun g => y (Additive.ofMul g)
  have hzy : zy ∈ coeffCocycles (1 : Representation κ (Gamma0 (M * p)) κ) := by
    intro g h
    change y (Additive.ofMul (g * h)) = y (Additive.ofMul g) + y (Additive.ofMul h)
    rw [ofMul_mul, map_add]
  refine ⟨coeffH1Mk _ ⟨zy, hzy⟩, ?_, fun ℓ hℓ hℓMp hℓS => ?_⟩
  · intro h0
    rw [coeffH1Mk_eq_zero_iff] at h0
    obtain ⟨v, hv⟩ := (mem_coeffCoboundaries_iff _ _).mp h0
    apply hy0
    refine AddMonoidHom.ext fun g => ?_
    have := congrFun hv (Additive.toMul g)
    simp only [MonoidHom.one_apply, Module.End.one_apply, sub_self] at this
    change y (Additive.ofMul (Additive.toMul g)) = 0
    exact this.symm
  · haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hℓM : ¬ ℓ ∣ M := fun h => hℓMp (h.mul_right p)
    have hℓp : ℓ ≠ p := fun h => hℓMp (h ▸ dvd_mul_left p M)
    have hℓS' : ℓ ∉ S₀ := fun h => hℓS (Set.mem_insert_of_mem p h)
    have hcompat : IsCompat (M * p) ℓ (1 : Representation κ (Gamma0 (M * p)) κ) LinearMap.id := by
      intro u; simp
    refine ⟨heckeH1 hcompat, isCoeffHeckeOnH1_heckeH1 hcompat, ?_⟩

    obtain ⟨T, hT, hTx⟩ := heig ℓ hℓ hℓM hℓS'
    have hTy : heckeOperatorHom (M * p) ℓ κ y = τ ℓ • y := by
      have h := hy2 ℓ hℓ hℓM hℓp (isCompat_W p M hpM κ ℓ (natCast_zmod_ne_zero p M hpM hℓ hℓM)) (τ ℓ) T hT hTx
      rwa [one_smul] at h
    rw [heckeH1_mk, ← map_smul]
    congr 1
    refine Subtype.ext (funext fun g => ?_)
    change coeffHeckeFun (M * p) ℓ (1 : Representation κ (Gamma0 (M * p)) κ) LinearMap.id
        (fun h => y (Additive.ofMul h)) g = mu ℓ * y (Additive.ofMul g)
    rw [coeffHeckeFun_trivial, hTy, AddMonoidHom.smul_apply, smul_eq_mul, hmu ℓ hℓ hℓM hℓS']

theorem main5 (hp5 : 5 ≤ p) (e t : ℕ) (het : (p - 1) ∣ e + 2 * t) (nu : ℕ → κ)
    (hocc : IsEigensystemH1 M (gamma0NebenRep p M hpM κ e) (fun _ => LinearMap.id) S₀ nu) :
    IsEigensystemH1 (M * p) (1 : Representation κ (Gamma0 (M * p)) κ) (fun _ => LinearMap.id) (insert p S₀)
      (fun ℓ => (ℓ : κ) ^ t * nu ℓ) := by
  have hp : p.Prime := Fact.out
  have hp1 : 0 < p - 1 := by omega
  have h6 : (6 : κ) ≠ 0 := by
    intro h
    rw [show (6 : κ) = ((6 : ℕ) : κ) by norm_num, CharP.cast_eq_zero_iff κ p] at h
    have h23 : p ∣ 2 * 3 := h
    rcases (Nat.Prime.dvd_mul hp).mp h23 with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) h2; omega
    · have := Nat.le_of_dvd (by norm_num) h3; omega
  have hM2 : 2 ≤ M := le_trans hp.two_le (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hpM)

  set k : ℕ := ((p - 2) * t) % (p - 1) with hkdef
  have hk : k < p - 1 := Nat.mod_lt _ hp1
  have hkp : k < p := by omega
  have hkt : (p - 1) ∣ k + t := by
    have h1 : k ≡ (p - 2) * t [MOD (p - 1)] := Nat.mod_modEq _ _
    have h2 : k + t ≡ (p - 2) * t + t [MOD (p - 1)] := h1.add_right t
    rw [show (p - 2) * t + t = (p - 1) * t by rw [show p - 1 = (p - 2) + 1 by omega, Nat.add_mul, one_mul]] at h2
    exact (Nat.modEq_zero_iff_dvd.mp (h2.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _))))
  have hek : e ≡ 2 * k [MOD (p - 1)] := by
    have h1 : e + 2 * t ≡ 0 [MOD (p - 1)] := Nat.modEq_zero_iff_dvd.mpr het
    have h2 : 2 * k + 2 * t ≡ 0 [MOD (p - 1)] := by
      rw [← mul_add]; exact Nat.modEq_zero_iff_dvd.mpr (hkt.mul_left 2)
    exact Nat.ModEq.add_right_cancel' (2 * t) (h1.trans h2.symm)

  set σ : ℕ → κ := fun ℓ => cW p κ k ℓ * nu ℓ with hσdef
  have hσ : IsEigensystemH1 M (gamma0NebenRep p M hpM κ (2 * k)) (fun ℓ => cW p κ k ℓ • LinearMap.id) S₀ σ := by
    rw [← gamma0NebenRep_eq_of_modEq p M hpM κ hek]
    exact isEigensystemH1_of_smul M _ (fun _ => LinearMap.id) _ (cW p κ k) S₀ nu (fun _ _ _ _ => rfl) hocc
  have hgood : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S₀ → σ ℓ = (ℓ : κ) ^ t * nu ℓ := by
    intro ℓ hℓ hℓM _
    have hℓp : ℓ ≠ p := fun h => hℓM (h ▸ hpM)
    have hℓ0 : (ℓ : κ) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff κ p]
      exact fun h => hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp h).symm
    change cW p κ k ℓ * nu ℓ = _
    congr 1
    rw [cW, map_inv₀, map_natCast, inv_pow]
    have h1 : ((ℓ : κ)) ^ (k + t) = 1 := natCast_pow_eq_one_of_dvd p κ hℓ hℓp hkt
    rw [pow_add] at h1
    exact inv_eq_of_mul_eq_one_right h1

  have hE := HeckeEis.isEigensystemH1_one_natCast_add_one M hM2 κ S₀
  rcases layer p M hpM κ S₀ h6 hkp σ hσ with hW | ⟨hk1, hdvd, heis⟩
  · exact final p M hpM κ S₀ hW hgood
  ·
    obtain ⟨m, hm⟩ := hdvd
    have hm0 : m ≠ 0 := by rintro rfl; omega
    have hm2 : m ≤ 2 := by
      by_contra h
      have : (p - 1) * 3 ≤ (p - 1) * m := Nat.mul_le_mul_left _ (by omega)
      omega
    have hcases : m = 1 ∨ m = 2 := by omega
    rcases hcases with rfl | rfl
    ·
      set j₀ := k + 1 with hj₀
      have hdvd0 : (p - 1) ∣ 2 * j₀ := ⟨1, hm⟩
      set τ₁ : ℕ → κ := fun ℓ => cW p κ j₀ ℓ * ((ℓ : κ) + 1) with hτ₁
      have h1 : IsEigensystemH1 M (gamma0NebenRep p M hpM κ (2 * j₀)) (fun ℓ => cW p κ j₀ ℓ • LinearMap.id)
          S₀ τ₁ := by
        rw [gamma0NebenRep_eq_one_of_dvd p M hpM κ hdvd0]
        exact isEigensystemH1_of_smul M _ (fun _ => LinearMap.id) _ (cW p κ j₀) S₀ _ (fun _ _ _ _ => rfl) hE
      rcases layer p M hpM κ S₀ h6 hk1 τ₁ h1 with hW1 | ⟨_, hdvd1, _⟩
      · refine final p M hpM κ S₀ hW1 fun ℓ hℓ hℓM hℓS => ?_
        rw [← hgood ℓ hℓ hℓM hℓS, heis ℓ hℓ hℓM hℓS]
        change cW p κ j₀ ℓ * ((ℓ : κ) + 1) = ((ℓ : κ) + 1) * cW p κ (k + 1) ℓ
        rw [mul_comm]
      · exfalso
        have h2 : (p - 1) ∣ 2 := by
          have : 2 * (j₀ + 1) = (p - 1) + 2 := by omega
          rw [this] at hdvd1
          exact (Nat.dvd_add_right (dvd_refl _)).mp hdvd1
        have := Nat.le_of_dvd (by norm_num) h2
        omega
    ·
      have hkp1 : k + 1 = p - 1 := by omega
      set τ₀ : ℕ → κ := fun ℓ => cW p κ 0 ℓ * ((ℓ : κ) + 1) with hτ₀
      have h0 : IsEigensystemH1 M (gamma0NebenRep p M hpM κ (2 * 0)) (fun ℓ => cW p κ 0 ℓ • LinearMap.id)
          S₀ τ₀ := by
        rw [Nat.mul_zero, gamma0NebenRep_zero]
        exact isEigensystemH1_of_smul M _ (fun _ => LinearMap.id) _ (cW p κ 0) S₀ _ (fun _ _ _ _ => rfl) hE
      rcases layer p M hpM κ S₀ h6 hp.pos τ₀ h0 with hW0 | ⟨_, hdvd0, _⟩
      · refine final p M hpM κ S₀ hW0 fun ℓ hℓ hℓM hℓS => ?_
        rw [← hgood ℓ hℓ hℓM hℓS, heis ℓ hℓ hℓM hℓS]
        change cW p κ 0 ℓ * ((ℓ : κ) + 1) = ((ℓ : κ) + 1) * cW p κ (k + 1) ℓ
        rw [cW_zero, one_mul, hkp1, cW_pow_sub_one p κ (natCast_zmod_ne_zero p M hpM hℓ hℓM), mul_one]
      · exfalso
        have := Nat.le_of_dvd (by norm_num) hdvd0
        omega

end Layer

end TwistMain
p2m_reactivate "P2MW.S_HeckeEis_exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep.TwistMain"

open scoped MatrixGroups in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (S₀ : Set ℕ) (e t : ℕ)
    (het : (p - 1) ∣ e + 2 * t)
    (κ : Type) [Field κ] [CharP κ p] (nu : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 M (HeckeEis.gamma0NebenRep p M hpM κ e)
      (fun _ => LinearMap.id) S₀ nu) :
    ∃ (M' : ℕ) (mu : ℕ → κ), M ∣ M' ∧ M' ∣ M * p ∧
      HeckeEis.IsEigensystemH1 M' (1 : Representation κ (CongruenceSubgroup.Gamma0 M') κ)
        (fun _ => LinearMap.id) (insert p S₀) mu ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ≠ p → ℓ ∉ S₀ → mu ℓ = (ℓ : κ) ^ t * nu ℓ := by
  have hp : p.Prime := Fact.out
  by_cases htriv : (p - 1) ∣ e ∧ (p - 1) ∣ t
  · exact TwistMain.trivial_case p M hpM S₀ e t κ nu htriv.1 htriv.2 hocc
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact htriv ⟨one_dvd _, one_dvd _⟩
  by_cases hp3 : p = 3
  · subst hp3
    have he : (3 - 1) ∣ e := by
      have h2 : 2 ∣ e + 2 * t := het
      omega
    have ht : ¬ 2 ∣ t := fun h => htriv ⟨he, h⟩
    rw [TwistMain.gamma0NebenRep_eq_one_of_dvd 3 M hpM κ he] at hocc
    obtain ⟨M', hMM', hM'3, hocc3⟩ :=
      HeckeEis.exists_isEigensystemH1_one_natCast_mul_of_isEigensystemH1_one_of_three_dvd M hpM S₀ κ nu hocc
    refine ⟨M', fun ℓ => (ℓ : κ) ^ t * nu ℓ, hMM', hM'3, ?_, fun _ _ _ _ _ => rfl⟩
    refine TwistMain.isEigensystemH1_congr M' _ _ _ (fun ℓ hℓ hℓM' hℓS => ?_) hocc3
    have hℓ3 : ℓ ≠ 3 := fun h => hℓS (h ▸ Set.mem_insert 3 S₀)
    obtain ⟨s, rfl⟩ : Odd t := Nat.not_even_iff_odd.mp fun h => ht (even_iff_two_dvd.mp h)
    change (ℓ : κ) * nu ℓ = (ℓ : κ) ^ (2 * s + 1) * nu ℓ
    rw [pow_succ, pow_mul, TwistMain.natCast_pow_sub_one 3 κ hℓ hℓ3, one_pow, one_mul]
  · have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
    exact ⟨M * p, fun ℓ => (ℓ : κ) ^ t * nu ℓ, dvd_mul_right M p, dvd_rfl,
      TwistMain.main5 p M hpM κ S₀ hp5 e t het nu hocc, fun _ _ _ _ _ => rfl⟩

end S_HeckeEis_exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep
end P2MW
export P2MW.S_HeckeEis_exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep (solution)
