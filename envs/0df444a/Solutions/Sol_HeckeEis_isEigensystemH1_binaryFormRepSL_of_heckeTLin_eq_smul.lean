-- Prove2me | solution 1 for HeckeEis.isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/1cf6da2c-669b-5629-85e9-fb0ed7c96b4d

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_HeckeEis_EichlerIntegral
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCocycles
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries
import Theorems.Thm_HeckeEis_binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj
import Theorems.Thm_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries
import Theorems.Thm_HeckeEis_exists_coeffH1_map_ringHom_binaryFormRepSL
import Theorems.Thm_HeckeEis_span_coeffCocycles_binaryFormRepSL_map_intCast_eq_top
import Theorems.Thm_HeckeEis_exists_injective_baseChange_coeffH1_binaryFormRepSL
import Theorems.Thm_HeckeEis_modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero
import Theorems.Thm_HeckeEis_coeffH1Mk_cocycle_heckeTLin_modularForm
import Theorems.Thm_HeckeEis_exists_isEichlerIntegral
import Theorems.Thm_HeckeEis_isEquivariantPrimitiveWith_of_isEichlerIntegral
import Theorems.Thm_Module_exists_ne_zero_forall_baseChange_eq_smul_of_algHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul

set_option autoImplicit false

namespace ESModP

open CongruenceSubgroup HeckeEis ModularFormClass
open scoped MatrixGroups TensorProduct

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

@[scoped simp] theorem heckeLin_apply (z : Gamma0 N → V) : heckeLin N ℓ ρ a z = coeffHeckeFun N ℓ ρ a z := rfl

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

theorem unique_of_isCoeffHeckeOnH1 {T T' : coeffH1 ρ →ₗ[K] coeffH1 ρ} (hT : IsCoeffHeckeOnH1 N ℓ ρ a T)
    (hT' : IsCoeffHeckeOnH1 N ℓ ρ a T') : T = T' := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective ρ x
  obtain ⟨w, hw, hTw⟩ := hT z
  obtain ⟨w', hw', hTw'⟩ := hT' z
  rw [hTw, hTw']
  congr 1
  exact Subtype.ext (hw.trans hw'.symm)

theorem eq_heckeH1_of_isCoeffHeckeOnH1 (ha : IsCompat N ℓ ρ a) {T : coeffH1 ρ →ₗ[K] coeffH1 ρ}
    (hT : IsCoeffHeckeOnH1 N ℓ ρ a T) : T = heckeH1 ha :=
  unique_of_isCoeffHeckeOnH1 hT (isCoeffHeckeOnH1_heckeH1 ha)

theorem coeffH1Mk_eq_iff (z w : ↥(coeffCocycles ρ)) :
    coeffH1Mk ρ z = coeffH1Mk ρ w ↔ (z : Gamma0 N → V) - w ∈ coeffCoboundaries ρ :=
  (Submodule.Quotient.eq _).trans Submodule.mem_comap

theorem heckeH1_comm {ℓ ℓ' : ℕ} [NeZero ℓ] [NeZero ℓ'] (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (hℓN : ¬ ℓ ∣ N) (hℓ'N : ¬ ℓ' ∣ N) (hne : ℓ ≠ ℓ') {a a' : V →ₗ[K] V}
    (ha : IsCompat N ℓ ρ a) (ha' : IsCompat N ℓ' ρ a') (hcomm : a ∘ₗ a' = a' ∘ₗ a) (x : coeffH1 ρ) :
    heckeH1 ha (heckeH1 ha' x) = heckeH1 ha' (heckeH1 ha x) := by
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective ρ x
  rw [heckeH1_mk, heckeH1_mk, heckeH1_mk, heckeH1_mk, coeffH1Mk_eq_iff]
  simp only [coe_heckeZ1]
  haveI : NeZero (ℓ * ℓ') := ⟨mul_ne_zero (NeZero.ne ℓ) (NeZero.ne ℓ')⟩
  have hℓℓ' : ¬ ℓ ∣ ℓ' := fun h => hne ((Nat.prime_dvd_prime_iff_eq hℓ hℓ').mp h)
  have hℓ'ℓ : ¬ ℓ' ∣ ℓ := fun h => hne ((Nat.prime_dvd_prime_iff_eq hℓ' hℓ).mp h).symm
  have h1 := coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries N ℓ ℓ' (ℓ * ℓ')
    hℓ hℓN hℓℓ' rfl ρ a a' ha ha' z.2
  have h2 := coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries N ℓ' ℓ (ℓ * ℓ')
    hℓ' hℓ'N hℓ'ℓ (Nat.mul_comm ℓ ℓ') ρ a' a ha' ha z.2
  rw [← hcomm] at h2
  have h3 := (coeffCoboundaries ρ).sub_mem h1 h2
  convert h3 using 1
  abel

end Induced

section Sym

variable (R : Type) [CommRing R] (N : ℕ) (n : ℕ)

noncomputable abbrev ρSym : Representation R (Gamma0 N) ↥(BinaryForm R n) :=
  (binaryFormRepSL R n).comp (Gamma0 N).subtype

def dMat (ℓ : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![(ℓ : ℤ), 0; 0, 1]

theorem dMat_comm (ℓ ℓ' : ℕ) : dMat ℓ * dMat ℓ' = dMat ℓ' * dMat ℓ := by
  simp only [dMat, Matrix.mul_fin_two, mul_zero, add_zero, zero_add, mul_one, mul_comm]

theorem binaryFormAlphaAdj_eq (ℓ : ℕ) : binaryFormAlphaAdj R n ℓ = binaryFormRep R n (dMat ℓ) := rfl

theorem isCompat_sym (ℓ : ℕ) [NeZero ℓ] : IsCompat N ℓ (ρSym R N n) (binaryFormAlphaAdj R n ℓ) :=
  fun u => binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj R n N ℓ u

theorem alpha_comm (ℓ ℓ' : ℕ) :
    binaryFormAlphaAdj R n ℓ ∘ₗ binaryFormAlphaAdj R n ℓ' =
      binaryFormAlphaAdj R n ℓ' ∘ₗ binaryFormAlphaAdj R n ℓ := by
  rw [binaryFormAlphaAdj_eq, binaryFormAlphaAdj_eq]
  change binaryFormRep R n (dMat ℓ) * binaryFormRep R n (dMat ℓ') =
    binaryFormRep R n (dMat ℓ') * binaryFormRep R n (dMat ℓ)
  rw [← map_mul, ← map_mul, dMat_comm]

abbrev H1 : Type := coeffH1 (ρSym R N n)

noncomputable def TH (ℓ : ℕ) [NeZero ℓ] : H1 R N n →ₗ[R] H1 R N n :=
  heckeH1 (isCompat_sym R N n ℓ)

theorem isCoeffHeckeOnH1_TH (ℓ : ℕ) [NeZero ℓ] :
    IsCoeffHeckeOnH1 N ℓ (ρSym R N n) (binaryFormAlphaAdj R n ℓ) (TH R N n ℓ) :=
  isCoeffHeckeOnH1_heckeH1 _

theorem TH_comm {ℓ ℓ' : ℕ} [NeZero ℓ] [NeZero ℓ'] (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (hℓN : ¬ ℓ ∣ N) (hℓ'N : ¬ ℓ' ∣ N) : Commute (TH R N n ℓ) (TH R N n ℓ') := by
  by_cases hne : ℓ = ℓ'
  · subst hne; exact Commute.refl _
  refine LinearMap.ext fun x => ?_
  exact heckeH1_comm hℓ hℓ' hℓN hℓ'N hne (isCompat_sym R N n ℓ) (isCompat_sym R N n ℓ')
    (alpha_comm R n ℓ ℓ') x

end Sym

section FiniteGen

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

theorem cocycle_apply_eq_zero_of_closure {G : Type*} [Group G] (ρ : Representation K G V)
    (z : ↥(coeffCocycles ρ)) (S : Set G) (hS : ∀ s ∈ S, (z : G → V) s = 0)
    (g : G) (hg : g ∈ Subgroup.closure S) : (z : G → V) g = 0 := by
  have hz := z.2
  have h1 : (z : G → V) 1 = 0 := by
    have h := hz 1 1
    rw [mul_one, map_one, Module.End.one_apply] at h
    have : (z : G → V) 1 + (z : G → V) 1 = (z : G → V) 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact h1
  | mul x y _ _ ihx ihy => rw [hz x y, ihx, ihy, map_zero, zero_add]
  | inv x _ ih =>
    have h := hz x x⁻¹
    rw [mul_inv_cancel, h1, ih, zero_add] at h
    have h2 : ρ x⁻¹ (ρ x ((z : G → V) x⁻¹)) = 0 := by rw [← h, map_zero]
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h2

theorem moduleFinite_coeffH1 (N : ℕ) [NeZero N] [IsNoetherianRing K] [Module.Finite K V]
    (ρ : Representation K (Gamma0 N) V) : Module.Finite K (coeffH1 ρ) := by
  haveI hSL : Group.FG SL(2, ℤ) :=
    Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators,
      Set.toFinite _⟩
  have hΓ : Group.FG (Gamma0 N) := inferInstance
  obtain ⟨S, hS⟩ := hΓ.out
  let ev : ↥(coeffCocycles ρ) →ₗ[K] (↥S → V) :=
    { toFun := fun z s => (z : Gamma0 N → V) s
      map_add' := fun z w => by ext s; rfl
      map_smul' := fun c z => by ext s; rfl }
  have hev : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    refine Subtype.ext (funext fun g => ?_)
    have hg : g ∈ Subgroup.closure (S : Set (Gamma0 N)) := by rw [hS]; trivial
    exact cocycle_apply_eq_zero_of_closure ρ z S (fun s hs => congrFun hz ⟨s, hs⟩) g hg
  haveI : Module.Finite K ↥(coeffCocycles ρ) := Module.Finite.of_injective ev hev
  exact Module.Finite.of_surjective (coeffH1Mk ρ) (coeffH1Mk_surjective ρ)

scoped instance moduleFinite_binaryForm [IsNoetherianRing K] (n : ℕ) : Module.Finite K ↥(BinaryForm K n) := by
  have hle : BinaryForm K n ≤ MvPolynomial.restrictTotalDegree (Fin 2) K n := fun φ hφ =>
    (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
      ((MvPolynomial.mem_homogeneousSubmodule n φ).mp hφ).totalDegree_le
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

end FiniteGen

section Words

variable {ι : Type}

noncomputable abbrev ev {A : Type*} [Ring A] (t : ι → A) : FreeAlgebra ℤ ι →ₐ[ℤ] A :=
  FreeAlgebra.lift ℤ t

theorem ev_algebraMap {A : Type*} [Ring A] (t : ι → A) (r : ℤ) :
    ev t (algebraMap ℤ (FreeAlgebra ℤ ι) r) = (r : A) := by
  rw [AlgHom.commutes, algebraMap_int_eq, eq_intCast]

theorem map_ev_apply {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    {A B : Type*} [Ring A] [Ring B] [Module A X] [Module B Y]
    (t : ι → A) (t' : ι → B) (Φ : X →+ Y) (hΦ : ∀ i x, Φ (t i • x) = t' i • Φ x)
    (w : FreeAlgebra ℤ ι) (x : X) : Φ (ev t w • x) = ev t' w • Φ x := by
  induction w using FreeAlgebra.induction generalizing x with
  | grade0 r => rw [ev_algebraMap, ev_algebraMap, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_zsmul]
  | grade1 i => rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply, hΦ]
  | mul a b iha ihb => rw [map_mul, map_mul, mul_smul, mul_smul, iha, ihb]
  | add a b iha ihb => rw [map_add, map_add, add_smul, add_smul, map_add, iha, ihb]

theorem ringHom_map_ev {A B : Type*} [Ring A] [Ring B] (ψ : A →+* B) (t : ι → A) (w : FreeAlgebra ℤ ι) :
    ψ (ev t w) = ev (fun i => ψ (t i)) w := by
  induction w using FreeAlgebra.induction with
  | grade0 r => rw [ev_algebraMap, ev_algebraMap, map_intCast]
  | grade1 i => rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]
  | mul a b iha ihb => rw [map_mul, map_mul, map_mul, iha, ihb]
  | add a b iha ihb => rw [map_add, map_add, map_add, iha, ihb]

theorem ev_apply_eigenvector {S : Type*} [CommRing S] {X : Type*} [AddCommGroup X] [Module S X]
    (t : ι → Module.End S X) (χ : ι → S) (x : X) (hx : ∀ i, t i x = χ i • x)
    (w : FreeAlgebra ℤ ι) : ev t w x = ev χ w • x := by
  induction w using FreeAlgebra.induction with
  | grade0 r => rw [ev_algebraMap, ev_algebraMap, Module.End.intCast_apply, Int.cast_smul_eq_zsmul]
  | grade1 i => rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply, hx]
  | mul a b iha ihb =>
    rw [map_mul, map_mul, Module.End.mul_apply, ihb, map_smul, iha, smul_smul, mul_comm]
  | add a b iha ihb => rw [map_add, map_add, LinearMap.add_apply, iha, ihb, add_smul]

end Words

section Coeff

variable (N n : ℕ)

structure IsCoeffMap {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    (Φ : H1 R N n →+ H1 R' N n) : Prop where
  mk_spec : ∀ z : ↥(coeffCocycles (ρSym R N n)), ∃ w : ↥(coeffCocycles (ρSym R' N n)),
    (∀ g : Gamma0 N, ((w : Gamma0 N → ↥(BinaryForm R' n)) g : MvPolynomial (Fin 2) R') =
      MvPolynomial.map φ (((z : Gamma0 N → ↥(BinaryForm R n)) g : MvPolynomial (Fin 2) R))) ∧
    Φ (coeffH1Mk _ z) = coeffH1Mk _ w
  smul : ∀ (c : R) (x : H1 R N n), Φ (c • x) = φ c • Φ x
  hecke : ∀ (ℓ : ℕ) [NeZero ℓ] (x : H1 R N n), Φ (TH R N n ℓ x) = TH R' N n ℓ (Φ x)

theorem exists_isCoeffMap {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') :
    ∃ Φ : H1 R N n →+ H1 R' N n, IsCoeffMap N n φ Φ := by
  obtain ⟨Φ, h1, h2, h3, -, -⟩ := exists_coeffH1_map_ringHom_binaryFormRepSL φ n N
  exact ⟨Φ, ⟨h1, h2, fun ℓ _ x => h3 ℓ (TH R N n ℓ) (TH R' N n ℓ) (isCoeffHeckeOnH1_TH R N n ℓ)
    (isCoeffHeckeOnH1_TH R' N n ℓ) x⟩⟩

variable {N n}

theorem IsCoeffMap.apply_mk_eq {R R' : Type} [CommRing R] [CommRing R'] {φ : R →+* R'}
    {Φ : H1 R N n →+ H1 R' N n} (hΦ : IsCoeffMap N n φ Φ) (z : ↥(coeffCocycles (ρSym R N n)))
    (w : ↥(coeffCocycles (ρSym R' N n)))
    (hw : ∀ g : Gamma0 N, ((w : Gamma0 N → ↥(BinaryForm R' n)) g : MvPolynomial (Fin 2) R') =
      MvPolynomial.map φ (((z : Gamma0 N → ↥(BinaryForm R n)) g : MvPolynomial (Fin 2) R))) :
    Φ (coeffH1Mk _ z) = coeffH1Mk _ w := by
  obtain ⟨w', hw', hΦz⟩ := hΦ.mk_spec z
  rw [hΦz]
  congr 1
  exact Subtype.ext (funext fun g => Subtype.ext ((hw' g).trans (hw g).symm))

theorem IsCoeffMap.eq_zero_of_forall_apply_eq_zero [NeZero N] {K : Type} [Field K] [CharZero K]
    {Φ : H1 ℤ N n →+ H1 K N n} (hΦ : IsCoeffMap N n (Int.castRingHom K) Φ)
    (A : Module.End K (H1 K N n)) (hA : ∀ x : H1 ℤ N n, A (Φ x) = 0) : A = 0 := by
  have hspan := span_coeffCocycles_binaryFormRepSL_map_intCast_eq_top K n N
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective _ x
  have hz : z ∈ Submodule.span K
      {w : ↥(coeffCocycles (ρSym K N n)) | ∃ z₀ : ↥(coeffCocycles (ρSym ℤ N n)), ∀ g : Gamma0 N,
        ((w : Gamma0 N → ↥(BinaryForm K n)) g : MvPolynomial (Fin 2) K) =
          MvPolynomial.map (Int.castRingHom K) (((z₀ : Gamma0 N → ↥(BinaryForm ℤ n)) g : MvPolynomial (Fin 2) ℤ))} := by
    rw [hspan]; exact Submodule.mem_top
  rw [LinearMap.zero_apply]
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨z₀, hz₀⟩ := hw
    rw [← hΦ.apply_mk_eq z₀ w hz₀]
    exact hA _
  | zero => rw [map_zero, map_zero]
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, map_smul, ha, smul_zero]

end Coeff

section Eichler

open UpperHalfPlane
open scoped ModularForm Manifold

variable {n : ℕ}

theorem isEichlerIntegral_smul {f : ℍ → ℂ} {F : ℍ → ↥(BinaryForm ℂ n)} (hF : IsEichlerIntegral n f F)
    (c : ℂ) : IsEichlerIntegral n (c • f) (c • F) := by
  intro d τ
  have h := (hF d τ).const_mul c
  simp only [Pi.smul_apply, Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul] at h ⊢
  convert h using 1
  · rfl
  · rfl
  ring

variable {K : Type*} [CommRing K] {Γ : Subgroup SL(2, ℤ)} {V : Type*} [AddCommGroup V] [Module K V]

theorem isEquivariantPrimitiveWith_smul {ρ : Representation K Γ V} {F : ℍ → V}
    (hF : IsEquivariantPrimitiveWith ρ F) (c : K) : IsEquivariantPrimitiveWith ρ (c • F) := fun γ => by
  obtain ⟨v, hv⟩ := hF γ
  exact ⟨c • v, fun τ => by rw [Pi.smul_apply, Pi.smul_apply, map_smul, ← smul_sub, hv τ]⟩

theorem cocycle_smul {ρ : Representation K Γ V} {F : ℍ → V} (hF : IsEquivariantPrimitiveWith ρ F) (c : K) :
    (isEquivariantPrimitiveWith_smul hF c).cocycle = c • hF.cocycle := by
  funext γ
  change (c • F) ((γ : SL(2, ℤ)) • I) - ρ γ ((c • F) I) = c • (F ((γ : SL(2, ℤ)) • I) - ρ γ (F I))
  rw [Pi.smul_apply, Pi.smul_apply, map_smul, smul_sub]

end Eichler

section Main

open scoped ModularForm Manifold

variable (N : ℕ) (S₀ : Set ℕ)

def Good (ℓ : ℕ) : Prop := ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ S₀

abbrev GoodPrime : Type := {ℓ : ℕ // Good N S₀ ℓ}

scoped instance neZero_goodPrime (i : GoodPrime N S₀) : NeZero (i : ℕ) := ⟨i.2.1.ne_zero⟩

variable (n : ℕ)

noncomputable def tH (R : Type) [CommRing R] : GoodPrime N S₀ → Module.End R (H1 R N n) :=
  fun i => TH R N n (i : ℕ)

theorem tH_comm (R : Type) [CommRing R] (i j : GoodPrime N S₀) : Commute (tH N S₀ n R i) (tH N S₀ n R j) :=
  TH_comm R N n i.2.1 j.2.1 i.2.2.1 j.2.2.1

abbrev wt : ℤ := (n : ℤ) + 2

abbrev MF : Type := ModularForm (Gamma0 N) (wt n)

noncomputable def tM : GoodPrime N S₀ → Module.End ℂ (MF N n) :=
  fun i => ModularForm.heckeTLin (wt n) i.2.1 i.2.2.1

variable {N S₀ n}

theorem IsCoeffMap.map_ev {R R' : Type} [CommRing R] [CommRing R'] {φ : R →+* R'}
    {Φ : H1 R N n →+ H1 R' N n} (hΦ : IsCoeffMap N n φ Φ) (w : FreeAlgebra ℤ (GoodPrime N S₀))
    (x : H1 R N n) : Φ (ev (tH N S₀ n R) w x) = ev (tH N S₀ n R') w (Φ x) :=
  map_ev_apply (tH N S₀ n R) (tH N S₀ n R') Φ (fun i y => hΦ.hecke i y) w x

theorem exists_eigenclass_of_eigenform [NeZero N] (χ : GoodPrime N S₀ → ℂ) (g : MF N n) (hg0 : g ≠ 0)
    (hg : ∀ i : GoodPrime N S₀, tM N S₀ n i g = χ i • g) :
    ∃ x : H1 ℂ N n, x ≠ 0 ∧ ∀ i : GoodPrime N S₀, tH N S₀ n ℂ i x = χ i • x := by
  obtain ⟨F₀, hEI⟩ := exists_isEichlerIntegral n (ModularFormClass.holo g)
  have hslash : ∀ γ ∈ Gamma0 N, (⇑g ∣[((n : ℤ) + 2)] γ) = ⇑g := by
    intro γ hγ
    have := SlashInvariantForm.slash_action_eqn g ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)
      (Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩)
    rw [ModularForm.SL_slash]
    exact this
  have hF₀ : IsEquivariantPrimitiveWith (ρSym ℂ N n) F₀ :=
    isEquivariantPrimitiveWith_of_isEichlerIntegral hEI hslash
  refine ⟨coeffH1Mk (ρSym ℂ N n) ⟨hF₀.cocycle, hF₀.cocycle_mem_coeffCocycles⟩, fun h => hg0 ?_, fun i => ?_⟩
  · exact modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero N n g F₀ hEI hF₀ h
  · have hgi : ModularForm.heckeTLin (wt n) i.2.1 i.2.2.1 g = χ i • g := hg i
    have hEI' : IsEichlerIntegral n ⇑(ModularForm.heckeTLin (wt n) i.2.1 i.2.2.1 g) (χ i • F₀) := by
      rw [hgi, ModularForm.IsGLPos.coe_smul]
      exact isEichlerIntegral_smul hEI (χ i)
    have h := coeffH1Mk_cocycle_heckeTLin_modularForm N n i.2.1 i.2.2.1 (TH ℂ N n i)
      (isCoeffHeckeOnH1_TH ℂ N n i) g F₀ hEI hF₀ (χ i • F₀) hEI' (isEquivariantPrimitiveWith_smul hF₀ (χ i))
    change TH ℂ N n i _ = _
    rw [h, ← map_smul]
    congr 1
    exact Subtype.ext (cocycle_smul hF₀ (χ i))

theorem ev_eq_zero_of_eigenform [NeZero N] (a : GoodPrime N S₀ → integralClosure ℤ ℂ) (g : MF N n) (hg0 : g ≠ 0)
    (hg : ∀ i : GoodPrime N S₀, tM N S₀ n i g = ((a i : integralClosure ℤ ℂ) : ℂ) • g)
    {κ : Type*} [Ring κ] (φ : integralClosure ℤ ℂ →+* κ)
    (w : FreeAlgebra ℤ (GoodPrime N S₀)) (hw : ev (tH N S₀ n ℤ) w = 0) :
    ev (fun i : GoodPrime N S₀ => φ (a i)) w = 0 := by

  obtain ⟨Φc, hΦc⟩ := exists_isCoeffMap N n (Int.castRingHom ℂ)
  have hC : ev (tH N S₀ n ℂ) w = 0 :=
    hΦc.eq_zero_of_forall_apply_eq_zero _ fun x => by rw [← hΦc.map_ev, hw, LinearMap.zero_apply, map_zero]

  obtain ⟨x, hx0, hx⟩ := exists_eigenclass_of_eigenform (fun i => ((a i : integralClosure ℤ ℂ) : ℂ)) g hg0 hg
  have h1 := ev_apply_eigenvector (tH N S₀ n ℂ) (fun i => ((a i : integralClosure ℤ ℂ) : ℂ)) x hx w
  rw [hC, LinearMap.zero_apply] at h1
  have hχ : ev (fun i => ((a i : integralClosure ℤ ℂ) : ℂ)) w = 0 := (smul_eq_zero.mp h1.symm).resolve_right hx0

  have h2 : ((ev a w : integralClosure ℤ ℂ) : ℂ) = ev (fun i => ((a i : integralClosure ℤ ℂ) : ℂ)) w :=
    ringHom_map_ev (algebraMap (integralClosure ℤ ℂ) ℂ) a w
  have h3 : ev a w = 0 := by
    rw [hχ] at h2
    exact_mod_cast h2

  rw [← ringHom_map_ev φ a w, h3, map_zero]

theorem exists_algHom_adjoin {ι : Type} {M : Type*} [AddCommGroup M] (t : ι → Module.End ℤ M)
    {F : Type} [Field F] (lam : ι → F)
    (hker : ∀ w : FreeAlgebra ℤ ι, ev t w = 0 → ev lam w = 0) :
    ∃ χ : ↥(Algebra.adjoin ℤ (Set.range t)) →ₐ[ℤ] F,
      ∀ i : ι, χ ⟨t i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ = lam i := by
  set B := Algebra.adjoin ℤ (Set.range t) with hBdef
  have hB : B = (ev t).range := Algebra.adjoin_range_eq_range_freeAlgebra_lift ℤ (X := ι) t
  let f : FreeAlgebra ℤ ι →ₐ[ℤ] ↥(ev t).range := (ev t).rangeRestrict
  have hf : Function.Surjective f := AlgHom.rangeRestrict_surjective _
  have hkerle : RingHom.ker (f : FreeAlgebra ℤ ι →+* ↥(ev t).range) ≤
      RingHom.ker (ev lam : FreeAlgebra ℤ ι →+* F) := by
    intro w hw
    rw [RingHom.mem_ker] at hw ⊢
    exact hker w (congrArg Subtype.val hw)
  let χ₀ : ↥(ev t).range →+* F :=
    RingHom.liftOfRightInverse (f : FreeAlgebra ℤ ι →+* _) (Function.surjInv hf)
      (Function.rightInverse_surjInv hf) ⟨_, hkerle⟩
  have hχ₀ : ∀ w, χ₀ (f w) = ev lam w := fun w =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ ⟨_, hkerle⟩ w
  let e : ↥B ≃ₐ[ℤ] ↥(ev t).range := Subalgebra.equivOfEq _ _ hB
  refine ⟨{ toRingHom := χ₀.comp (e : ↥B →+* ↥(ev t).range), commutes' := fun r => ?_ }, fun i => ?_⟩
  · simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe,
      eq_intCast, map_intCast]
  · change χ₀ (e ⟨t i, _⟩) = lam i
    have he : e ⟨t i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ = f (FreeAlgebra.ι ℤ i) := by
      apply Subtype.ext
      change t i = ev t (FreeAlgebra.ι ℤ i)
      rw [FreeAlgebra.lift_ι_apply]
    rw [he, hχ₀, FreeAlgebra.lift_ι_apply]

theorem exists_eigenclass_of_baseChange {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [CharP F p]
    (lam : GoodPrime N S₀ → F) (y : F ⊗[ℤ] H1 ℤ N n) (hy0 : y ≠ 0)
    (hy : ∀ i : GoodPrime N S₀, (tH N S₀ n ℤ i).baseChange F y = lam i • y) :
    ∃ x : H1 F N n, x ≠ 0 ∧ ∀ i : GoodPrime N S₀, tH N S₀ n F i x = lam i • x := by
  obtain ⟨Φ, hinj, hΦ⟩ := exists_injective_baseChange_coeffH1_binaryFormRepSL p F n N
  obtain ⟨ΦF, hΦF⟩ := exists_isCoeffMap N n (Int.castRingHom F)

  have htmul : ∀ (c : F) (x : H1 ℤ N n), Φ (c ⊗ₜ x) = c • ΦF x := by
    intro c x
    obtain ⟨z, rfl⟩ := coeffH1Mk_surjective _ x
    obtain ⟨w, hw, hΦw⟩ := hΦ c z
    obtain ⟨w₀, hw₀, hΦFz⟩ := hΦF.mk_spec z
    rw [hΦw, hΦFz, ← map_smul]
    congr 1
    refine Subtype.ext (funext fun g => Subtype.ext ?_)
    rw [hw g, Submodule.coe_smul, Pi.smul_apply, Submodule.coe_smul, hw₀ g]

  have hhecke : ∀ (i : GoodPrime N S₀) (y : F ⊗[ℤ] H1 ℤ N n),
      Φ ((tH N S₀ n ℤ i).baseChange F y) = tH N S₀ n F i (Φ y) := by
    intro i y
    induction y using TensorProduct.induction_on with
    | zero =>
      have h0 : (LinearMap.baseChange F (tH N S₀ n ℤ i)) (0 : F ⊗[ℤ] H1 ℤ N n) = (0 : F ⊗[ℤ] H1 ℤ N n) :=
        map_zero _
      rw [h0, map_zero, map_zero]
    | tmul c x =>
      change Φ (c ⊗ₜ[ℤ] ((tH N S₀ n ℤ i) x)) = _
      rw [htmul, htmul, map_smul]
      congr 1
      exact hΦF.hecke i x
    | add a b ha hb =>
      have hab : (LinearMap.baseChange F (tH N S₀ n ℤ i)) (a + b) =
          ((LinearMap.baseChange F (tH N S₀ n ℤ i)) a : F ⊗[ℤ] H1 ℤ N n) +
            ((LinearMap.baseChange F (tH N S₀ n ℤ i)) b : F ⊗[ℤ] H1 ℤ N n) :=
        map_add _ _ _
      rw [hab]
      erw [map_add Φ]
      rw [ha, hb, ← map_add]
      congr 1
      exact (map_add Φ a b).symm
  refine ⟨Φ y, fun h => hy0 (hinj (by rw [h, map_zero])), fun i => ?_⟩
  rw [← hhecke, hy i, map_smul]

end Main

end ESModP
p2m_reactivate "P2MW.S_HeckeEis_isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul.ESModP"

open ESModP CongruenceSubgroup HeckeEis in
open scoped TensorProduct in

theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S : Set ℕ) (n : ℕ) (k : ℤ) (hk : (n : ℤ) + 2 = k)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hf : f ≠ 0)
    (a : ℕ → integralClosure ℤ ℂ)
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S →
      ModularForm.heckeTLin k hℓ hℓN f = ((a ℓ : integralClosure ℤ ℂ) : ℂ) • f)
    (κ : Type) [Field κ] [CharP κ p] (φ : integralClosure ℤ ℂ →+* κ) :
    HeckeEis.IsEigensystemH1 N
      ((HeckeEis.binaryFormRepSL κ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj κ n ℓ) S (fun ℓ => φ (a ℓ)) := by
  subst hk

  have hker := fun w hw => ev_eq_zero_of_eigenform (fun i : GoodPrime N S => a i) f hf
    (fun i => heig i i.2.1 i.2.2.1 i.2.2.2) φ w hw

  obtain ⟨χ, hχ⟩ := exists_algHom_adjoin (tH N S n ℤ) (fun i : GoodPrime N S => φ (a i)) hker

  haveI := moduleFinite_coeffH1 N (ρSym ℤ N n)
  obtain ⟨y', hy'0, hy'⟩ :=
    Module.exists_ne_zero_forall_baseChange_eq_smul_of_algHom (tH N S n ℤ) (tH_comm N S n ℤ) χ
  have hy'' : ∀ i : GoodPrime N S, (tH N S n ℤ i).baseChange κ y' = φ (a i) • y' := fun i => by
    rw [hy' i]
    exact congrArg (fun c : κ => c • y') (hχ i)

  obtain ⟨x, hx0, hx⟩ := exists_eigenclass_of_baseChange (fun i : GoodPrime N S => φ (a i)) y' hy'0 hy''
  refine ⟨x, hx0, fun ℓ hℓ hℓN hℓS => ?_⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  exact ⟨TH κ N n ℓ, isCoeffHeckeOnH1_TH κ N n ℓ, hx ⟨ℓ, hℓ, hℓN, hℓS⟩⟩

end S_HeckeEis_isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul
end P2MW
export P2MW.S_HeckeEis_isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul (solution)
