-- Prove2me | solution 1 for ModPForms.exists_isEigensystemH1_binaryFormRepSL_of_isModPEigen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/e29515d9-bea7-5b8c-9fcb-e4ab4b0db049

import Mathlib
import Definitions.Def_CuspForm_ModPForms
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
import Theorems.Thm_ModularForm_finiteDimensional_Gamma0
import Theorems.Thm_ModularForm_heckeTLin_comm
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
import Theorems.Thm_Module_exists_ne_zero_forall_baseChange_eq_smul_of_algHom
import Theorems.Thm_Module_End_isNilpotent_of_mem_adjoin_of_forall_eigenvector_apply_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_exists_isEigensystemH1_binaryFormRepSL_of_isModPEigen

set_option autoImplicit false

namespace C1ES

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
  simp only [dMat, Matrix.mul_fin_two]
  congr 1 <;> ring

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

theorem TH_mk (ℓ : ℕ) [NeZero ℓ] (z : ↥(coeffCocycles (ρSym R N n))) :
    TH R N n ℓ (coeffH1Mk _ z) = coeffH1Mk _ (heckeZ1 (isCompat_sym R N n ℓ) z) := rfl

theorem eq_TH {ℓ : ℕ} [NeZero ℓ] {T : H1 R N n →ₗ[R] H1 R N n}
    (hT : IsCoeffHeckeOnH1 N ℓ (ρSym R N n) (binaryFormAlphaAdj R n ℓ) T) : T = TH R N n ℓ :=
  eq_heckeH1_of_isCoeffHeckeOnH1 _ hT

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

theorem ev_apply_eigenvector {S : Type*} [CommRing S] {X : Type*} [AddCommGroup X] [Module S X]
    (t : ι → Module.End S X) (χ : ι → S) (x : X) (hx : ∀ i, t i x = χ i • x)
    (w : FreeAlgebra ℤ ι) : ev t w x = ev χ w • x := by
  induction w using FreeAlgebra.induction with
  | grade0 r => rw [ev_algebraMap, ev_algebraMap, Module.End.intCast_apply, Int.cast_smul_eq_zsmul]
  | grade1 i => rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply, hx]
  | mul a b iha ihb =>
    rw [map_mul, map_mul, Module.End.mul_apply, ihb, map_smul, iha, smul_smul, mul_comm]
  | add a b iha ihb => rw [map_add, map_add, LinearMap.add_apply, iha, ihb, add_smul]

theorem ev_mem_adjoin {S : Type*} [CommRing S] {A : Type*} [Ring A] [Algebra S A] (t : ι → A)
    (w : FreeAlgebra ℤ ι) : ev t w ∈ Algebra.adjoin S (Set.range t) := by
  induction w using FreeAlgebra.induction with
  | grade0 r => rw [ev_algebraMap]; exact Subalgebra.intCast_mem _ r
  | grade1 i => rw [FreeAlgebra.lift_ι_apply]; exact Algebra.subset_adjoin ⟨i, rfl⟩
  | mul a b iha ihb => rw [map_mul]; exact Subalgebra.mul_mem _ iha ihb
  | add a b iha ihb => rw [map_add]; exact Subalgebra.add_mem _ iha ihb

theorem baseChange_ev {S : Type*} [CommRing S] (A : Type*) [CommRing A] [Algebra S A]
    {X : Type*} [AddCommGroup X] [Module S X] (t : ι → Module.End S X) (w : FreeAlgebra ℤ ι) :
    (ev t w).baseChange A = ev (fun i => (t i).baseChange A) w := by
  induction w using FreeAlgebra.induction with
  | grade0 r =>
    rw [ev_algebraMap, ev_algebraMap]
    exact map_intCast (Module.End.baseChangeHom S A X) r
  | grade1 i => rw [FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]
  | mul a b iha ihb => rw [map_mul, map_mul, LinearMap.baseChange_mul, iha, ihb]
  | add a b iha ihb => rw [map_add, map_add, LinearMap.baseChange_add, iha, ihb]

end Words

section Coeff

theorem map_binarySubst {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R')
    (M : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) R) :
    MvPolynomial.map φ (binarySubst R M P) = binarySubst R' M (MvPolynomial.map φ P) := by
  have h : (MvPolynomial.map φ).comp (binarySubst R M : MvPolynomial (Fin 2) R →+* MvPolynomial (Fin 2) R) =
      (binarySubst R' M : MvPolynomial (Fin 2) R' →+* MvPolynomial (Fin 2) R').comp (MvPolynomial.map φ) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, RingHom.coe_coe, binarySubst_C, MvPolynomial.map_C]
    · simp only [RingHom.comp_apply, RingHom.coe_coe, binarySubst_X, MvPolynomial.map_X, map_sum,
        map_mul, map_intCast]
  exact congrFun (congrArg DFunLike.coe h) P

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

section Lattice

variable (N : ℕ) (k : ℤ)

abbrev MF : Type := ModularForm (Gamma0 N) k

theorem one_mem_strictPeriods :
    (1 : ℝ) ∈ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

noncomputable def qCoeffLin (m : ℕ) : MF N k →ₗ[ℂ] ℂ where
  toFun f := qCoeff f m
  map_add' f g := by
    change (UpperHalfPlane.qExpansion 1 ⇑(f + g)).coeff m = _
    rw [ModularForm.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods N) f g, map_add]
    rfl
  map_smul' c f := by
    change (UpperHalfPlane.qExpansion 1 ⇑(c • f)).coeff m = _
    rw [ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N) c f,
      map_smul]
    rfl

@[scoped simp] theorem qCoeffLin_apply (m : ℕ) (f : MF N k) : qCoeffLin N k m f = qCoeff f m := rfl

theorem eq_zero_of_forall_qCoeff (f : MF N k) (h : ∀ m, qCoeff f m = 0) : f = 0 :=
  ModularFormClass.eq_of_forall_qCoeff_eq (one_mem_strictPeriods N) fun m => by
    rw [h m, ← qCoeffLin_apply N k m (0 : MF N k), map_zero]

noncomputable def intFormsAdd : AddSubgroup (MF N k) where
  carrier := {f | ∀ m : ℕ, ∃ z : ℤ, qCoeff f m = (z : ℂ)}
  zero_mem' m := ⟨0, by rw [Int.cast_zero, ← qCoeffLin_apply, map_zero]⟩
  add_mem' {f g} hf hg m := by
    obtain ⟨a, ha⟩ := hf m
    obtain ⟨b, hb⟩ := hg m
    exact ⟨a + b, by rw [← qCoeffLin_apply, map_add, qCoeffLin_apply, qCoeffLin_apply, ha, hb,
      Int.cast_add]⟩
  neg_mem' {f} hf m := by
    obtain ⟨a, ha⟩ := hf m
    exact ⟨-a, by rw [← qCoeffLin_apply, map_neg, qCoeffLin_apply, ha, Int.cast_neg]⟩

noncomputable def intForms : Submodule ℤ (MF N k) := (intFormsAdd N k).toIntSubmodule

theorem mem_intForms (f : MF N k) : f ∈ intForms N k ↔ ∀ m : ℕ, ∃ z : ℤ, qCoeff f m = (z : ℂ) :=
  Iff.rfl

variable {N k}

noncomputable def zc (f : ↥(intForms N k)) (m : ℕ) : ℤ := (f.2 m).choose

theorem zc_spec (f : ↥(intForms N k)) (m : ℕ) : (zc f m : ℂ) = qCoeff (f : MF N k) m :=
  ((f.2 m).choose_spec).symm

theorem zc_add (f g : ↥(intForms N k)) (m : ℕ) : zc (f + g) m = zc f m + zc g m := by
  apply Int.cast_injective (α := ℂ)
  rw [Int.cast_add, zc_spec, zc_spec, zc_spec, Submodule.coe_add, ← qCoeffLin_apply, map_add]
  rfl

variable (N k)

noncomputable def zcHom : ↥(intForms N k) →+ (ℕ → ℤ) where
  toFun := zc
  map_zero' := funext fun m => Int.cast_injective (α := ℂ) (by
    rw [zc_spec, Submodule.coe_zero, Pi.zero_apply, Int.cast_zero, ← qCoeffLin_apply, map_zero])
  map_add' f g := funext fun m => zc_add f g m

theorem zcHom_apply (f : ↥(intForms N k)) (m : ℕ) : zcHom N k f m = zc f m := rfl

theorem zcHom_injective : Function.Injective (zcHom N k) := by
  intro f g h
  apply Subtype.ext
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_qCoeff N k _ fun m => ?_
  have hm := congrFun h m
  rw [zcHom_apply, zcHom_apply] at hm
  change qCoeff (⇑((f : MF N k) - (g : MF N k))) m = 0
  rw [← qCoeffLin_apply, map_sub, qCoeffLin_apply, qCoeffLin_apply, ← zc_spec, ← zc_spec, hm, sub_self]

theorem zc_zsmul (d : ℤ) (f : ↥(intForms N k)) (m : ℕ) : zc (d • f) m = d * zc f m := by
  have h := congrFun (map_zsmul (zcHom N k) d f) m
  rwa [zcHom_apply, Pi.smul_apply, zcHom_apply, smul_eq_mul] at h

theorem exists_finset_ker_eq_bot [NeZero N] :
    ∃ s : Finset ℕ, ∀ f : MF N k, (∀ m ∈ s, qCoeff f m = 0) → f = 0 := by
  haveI : FiniteDimensional ℂ (MF N k) := ModularForm.finiteDimensional_Gamma0 N k
  let K : Finset ℕ → Submodule ℂ (MF N k) := fun s => ⨅ m ∈ s, LinearMap.ker (qCoeffLin N k m)
  obtain ⟨W, ⟨s₀, rfl⟩, hmin⟩ := WellFounded.has_min (IsWellFounded.wf (r := (· < ·)))
    (Set.range K) ⟨K ∅, ∅, rfl⟩
  refine ⟨s₀, fun f hf => ?_⟩
  have hfK : f ∈ K s₀ := by
    simp only [K, Submodule.mem_iInf, LinearMap.mem_ker, qCoeffLin_apply]
    exact hf
  have hle : ∀ m, K s₀ ≤ LinearMap.ker (qCoeffLin N k m) := by
    intro m
    by_contra hnot
    have hlt : K (insert m s₀) < K s₀ := by
      refine lt_of_le_of_ne ?_ ?_
      · exact biInf_mono (by intro i hi; exact Finset.mem_insert_of_mem hi)
      · intro heq
        apply hnot
        rw [← heq]
        exact biInf_le _ (Finset.mem_insert_self m s₀)
    exact hmin _ ⟨_, rfl⟩ hlt
  refine eq_zero_of_forall_qCoeff N k f fun m => ?_
  have := hle m hfK
  rwa [LinearMap.mem_ker, qCoeffLin_apply] at this

theorem exists_basis_intForms [NeZero N] :
    ∃ r : ℕ, Nonempty (Module.Basis (Fin r) ℤ ↥(intForms N k)) := by
  obtain ⟨s, hs⟩ := exists_finset_ker_eq_bot N k

  let ev : ↥(intForms N k) →ₗ[ℤ] (↥s → ℤ) :=
    { toFun := fun f i => zc f i
      map_add' := fun f g => funext fun i => zc_add f g i
      map_smul' := fun d f => funext fun i => by
        rw [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, zc_zsmul] }
  have hev : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    apply Subtype.ext
    refine hs _ fun m hm => ?_
    rw [← zc_spec, show zc f m = 0 from congrFun hf ⟨m, hm⟩, Int.cast_zero]
  obtain ⟨r, b⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ↥s) (LinearMap.range ev)
  exact ⟨r, ⟨b.map (LinearEquiv.ofInjective ev hev).symm⟩⟩

def zcHecke (k : ℤ) (ℓ : ℕ) (a : ℕ → ℤ) (m : ℕ) : ℤ :=
  a (m * ℓ) + if ℓ ∣ m then (ℓ : ℤ) ^ (k - 1).toNat * a (m / ℓ) else 0

theorem cast_zcHecke {S : Type*} [DivisionRing S] [CharZero S] {k : ℤ} (hk : 1 ≤ k) (ℓ : ℕ) (a : ℕ → ℤ) (m : ℕ) :
    (zcHecke k ℓ a m : S) = (a (m * ℓ) : S) + if ℓ ∣ m then (ℓ : S) ^ (k - 1) * (a (m / ℓ) : S) else 0 := by
  have hk' : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
  unfold zcHecke
  split_ifs with h
  · push_cast
    rw [← zpow_natCast, hk']
  · push_cast; rfl

variable {N k} in
theorem qCoeff_heckeTLin (hk : 1 ≤ k) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (f : ↥(intForms N k)) (m : ℕ) :
    qCoeff (ModularForm.heckeTLin k hℓ hℓN (f : MF N k)) m = (zcHecke k ℓ (zc f) m : ℂ) := by
  rw [ModularForm.coe_heckeTLin_apply, ModularFormClass.qCoeff_heckeT (f : MF N k)
    (one_mem_strictPeriods N) hℓ.ne_zero m, ModularForm.coeffHeckeT_apply, cast_zcHecke hk]
  simp only [← zc_spec]

theorem heckeTLin_mem_intForms (hk : 1 ≤ k) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (f : ↥(intForms N k)) : ModularForm.heckeTLin k hℓ hℓN (f : MF N k) ∈ intForms N k :=
  fun m => ⟨zcHecke k ℓ (zc f) m, qCoeff_heckeTLin hk hℓ hℓN f m⟩

noncomputable def TL (hk : 1 ≤ k) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    ↥(intForms N k) →ₗ[ℤ] ↥(intForms N k) :=
  ((ModularForm.heckeTLin k hℓ hℓN).toAddMonoidHom.toIntLinearMap).restrict
    fun f hf => heckeTLin_mem_intForms N k hk hℓ hℓN ⟨f, hf⟩

@[scoped simp] theorem coe_TL (hk : 1 ≤ k) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (f : ↥(intForms N k)) :
    ((TL N k hk hℓ hℓN f : ↥(intForms N k)) : MF N k) = ModularForm.heckeTLin k hℓ hℓN (f : MF N k) := rfl

theorem zc_TL (hk : 1 ≤ k) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (f : ↥(intForms N k)) (m : ℕ) :
    zc (TL N k hk hℓ hℓN f) m = zcHecke k ℓ (zc f) m := by
  apply Int.cast_injective (α := ℂ)
  rw [zc_spec, coe_TL, qCoeff_heckeTLin hk hℓ hℓN f m]

theorem TL_comm (hk : 1 ≤ k) {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓ' : ℓ'.Prime)
    (hℓ'N : ¬ ℓ' ∣ N) : Commute (TL N k hk hℓ hℓN) (TL N k hk hℓ' hℓ'N) := by
  refine LinearMap.ext fun f => Subtype.ext ?_
  change ModularForm.heckeTLin k hℓ hℓN (ModularForm.heckeTLin k hℓ' hℓ'N (f : MF N k)) =
    ModularForm.heckeTLin k hℓ' hℓ'N (ModularForm.heckeTLin k hℓ hℓN (f : MF N k))
  exact congrFun (congrArg DFunLike.coe (ModularForm.heckeTLin_comm k hℓ hℓN hℓ' hℓ'N).eq) (f : MF N k)

variable (F : Type) [Field F]

noncomputable def redL : ↥(intForms N k) →ₗ[ℤ] PowerSeries F :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun f => PowerSeries.mk fun m => ((zc f m : ℤ) : F)
      map_zero' := by
        ext m
        rw [PowerSeries.coeff_mk, map_zero, show zc 0 m = 0 from congrFun (map_zero (zcHom N k)) m,
          Int.cast_zero]
      map_add' := fun f g => by
        ext m
        simp only [PowerSeries.coeff_mk, map_add, zc_add, Int.cast_add] }

@[scoped simp] theorem coeff_redL (f : ↥(intForms N k)) (m : ℕ) :
    PowerSeries.coeff m (redL N k F f) = ((zc f m : ℤ) : F) := by
  simp [redL, PowerSeries.coeff_mk]

noncomputable def red : F ⊗[ℤ] ↥(intForms N k) →ₗ[F] PowerSeries F :=
  (redL N k F).liftBaseChange F

@[scoped simp] theorem red_tmul (c : F) (f : ↥(intForms N k)) : red N k F (c ⊗ₜ f) = c • redL N k F f :=
  LinearMap.liftBaseChange_tmul F _ c f

theorem red_mem_modPMod (y : F ⊗[ℤ] ↥(intForms N k)) : red N k F y ∈ ModPForms.modPMod N k F := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul c f =>
    rw [red_tmul]
    refine Submodule.smul_mem _ c (Submodule.subset_span ⟨(f : MF N k), zc f, fun m => (zc_spec f m).symm, ?_⟩)
    rfl
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

theorem heckePS_add (ℓ : ℕ) (φ ψ : PowerSeries F) :
    ModPForms.heckePS k ℓ (φ + ψ) = ModPForms.heckePS k ℓ φ + ModPForms.heckePS k ℓ ψ := by
  ext m
  simp only [ModPForms.heckePS, PowerSeries.coeff_mk, map_add]
  split_ifs <;> ring

theorem heckePS_smul (ℓ : ℕ) (c : F) (φ : PowerSeries F) :
    ModPForms.heckePS k ℓ (c • φ) = c • ModPForms.heckePS k ℓ φ := by
  ext m
  simp only [ModPForms.heckePS, PowerSeries.coeff_mk, map_smul, smul_eq_mul]
  split_ifs <;> ring

theorem red_baseChange_TL (hk : 1 ≤ k) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (y : F ⊗[ℤ] ↥(intForms N k)) :
    red N k F ((TL N k hk hℓ hℓN).baseChange F y) = ModPForms.heckePS k ℓ (red N k F y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; ext m; simp [ModPForms.heckePS, PowerSeries.coeff_mk]
  | tmul c f =>
    rw [LinearMap.baseChange_tmul, red_tmul, red_tmul, heckePS_smul]
    congr 1
    ext m
    rw [coeff_redL, zc_TL]
    simp only [ModPForms.heckePS, PowerSeries.coeff_mk, coeff_redL, zcHecke]
    have hk' : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
    split_ifs with h
    · push_cast; rw [← zpow_natCast, hk']
    · push_cast; rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, heckePS_add]

theorem exists_red_eq_of_mem_modPMod {φ : PowerSeries F} (hφ : φ ∈ ModPForms.modPMod N k F) :
    ∃ y : F ⊗[ℤ] ↥(intForms N k), red N k F y = φ := by
  induction hφ using Submodule.span_induction with
  | mem ψ hψ =>
    obtain ⟨f, a, hfa, rfl⟩ := hψ
    have hf : (f : MF N k) ∈ intForms N k := fun m => ⟨a m, hfa m⟩
    refine ⟨1 ⊗ₜ ⟨f, hf⟩, ?_⟩
    rw [red_tmul, one_smul]
    ext m
    rw [coeff_redL, PowerSeries.coeff_mk]
    congr 1
    apply Int.cast_injective (α := ℂ)
    rw [zc_spec]
    exact hfa m
  | zero => exact ⟨0, map_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨y, rfl⟩ := ha
    obtain ⟨y', rfl⟩ := hb
    exact ⟨y + y', map_add _ _ _⟩
  | smul c a _ ha =>
    obtain ⟨y, rfl⟩ := ha
    exact ⟨c • y, map_smul _ _ _⟩

variable {F}

theorem exists_smul_eq_of_forall_dvd {p : ℕ} (hp : p ≠ 0) (g : ↥(intForms N k))
    (hg : ∀ m, (p : ℤ) ∣ zc g m) : ∃ g' : ↥(intForms N k), (p : ℤ) • g' = g := by
  choose q hq using hg
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  refine ⟨⟨(p : ℂ)⁻¹ • (g : MF N k), fun m => ⟨q m, ?_⟩⟩, Subtype.ext ?_⟩
  · rw [← qCoeffLin_apply, map_smul, qCoeffLin_apply, ← zc_spec, hq m, smul_eq_mul]
    push_cast
    field_simp
  · rw [SetLike.val_smul, ← Int.cast_smul_eq_zsmul ℂ, smul_smul, Int.cast_natCast,
      mul_inv_cancel₀ hp', one_smul]

theorem dvd_of_sum_smul_redL_eq_zero {p : ℕ} [Fact p.Prime] [CharP F p] {r : ℕ}
    (b : Module.Basis (Fin r) ℤ ↥(intForms N k)) (d : Fin r → ℤ)
    (hd : ∑ i, ((d i : ℤ) : F) • redL N k F (b i) = 0) (i : Fin r) : (p : ℤ) ∣ d i := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set g : ↥(intForms N k) := ∑ i, d i • b i with hg
  have hredg : redL N k F g = 0 := by
    rw [hg, map_sum]
    simp only [map_zsmul]
    simpa only [Int.cast_smul_eq_zsmul] using hd
  have hdvd : ∀ m, (p : ℤ) ∣ zc g m := fun m => by
    have := congrArg (PowerSeries.coeff m) hredg
    rw [coeff_redL, map_zero] at this
    exact (CharP.intCast_eq_zero_iff F p _).mp this
  obtain ⟨g', hg'⟩ := exists_smul_eq_of_forall_dvd N k hp g hdvd
  have hrepr : b.equivFun g = d := by
    rw [hg, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
  have := congrFun hrepr i
  rw [← hg', map_zsmul, Pi.smul_apply, smul_eq_mul] at this
  exact ⟨_, this.symm⟩

theorem linearIndependent_redL {p : ℕ} [Fact p.Prime] [CharP F p] {r : ℕ}
    (b : Module.Basis (Fin r) ℤ ↥(intForms N k)) :
    LinearIndependent F (fun i => redL N k F (b i)) := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  let e := Module.Free.chooseBasis (ZMod p) F
  rw [Fintype.linearIndependent_iff]
  intro c hc i

  refine e.ext_elem fun j => ?_
  rw [map_zero, Finsupp.zero_apply]

  let d : Fin r → ℤ := fun i' => ((e.repr (c i') j).val : ℤ)
  have hdcast : ∀ i', ((d i' : ℤ) : ZMod p) = e.repr (c i') j := fun i' => by
    simp only [d, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hrel : ∑ i', ((d i' : ℤ) : F) • redL N k F (b i') = 0 := by
    ext m
    have hm := congrArg (PowerSeries.coeff m) hc
    simp only [map_sum, map_smul, coeff_redL, smul_eq_mul, map_zero] at hm ⊢

    have hm' : ∑ i', ((zc (b i') m : ℤ) : ZMod p) • c i' = 0 := by
      rw [← hm]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [Algebra.smul_def, map_intCast, mul_comm]
    have hj := congrArg (fun x : F => e.repr x j) hm'
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, map_zero, Finsupp.zero_apply] at hj
    have : (∑ i', ((d i' : ℤ) : F) * ((zc (b i') m : ℤ) : F)) =
        algebraMap (ZMod p) F (∑ i', ((zc (b i') m : ℤ) : ZMod p) * e.repr (c i') j) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [map_mul, map_intCast, ← hdcast, map_intCast, mul_comm]
    rw [this, hj, map_zero]
  have hdiv := dvd_of_sum_smul_redL_eq_zero N k b d hrel i
  rw [← hdcast, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdiv]

theorem red_injective [NeZero N] {p : ℕ} [Fact p.Prime] [CharP F p] :
    Function.Injective (red N k F) := by
  obtain ⟨r, ⟨b⟩⟩ := exists_basis_intForms N k
  have hli := linearIndependent_redL N k (F := F) b
  let B := Algebra.TensorProduct.basis F b
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  rw [← B.sum_equivFun y] at hy
  simp only [map_sum, map_smul, B, Algebra.TensorProduct.basis_apply, red_tmul, one_smul] at hy
  have h0 := (Fintype.linearIndependent_iff.mp hli) _ hy
  rw [← B.sum_equivFun y]
  exact Finset.sum_eq_zero fun i _ => by rw [h0 i, zero_smul]

end Lattice

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

theorem one_le_wt : 1 ≤ wt n := by unfold wt; omega

noncomputable def tL : GoodPrime N S₀ → Module.End ℤ ↥(intForms N (wt n)) :=
  fun i => TL N (wt n) (one_le_wt n) i.2.1 i.2.2.1

noncomputable def tM : GoodPrime N S₀ → Module.End ℂ (MF N (wt n)) :=
  fun i => ModularForm.heckeTLin (wt n) i.2.1 i.2.2.1

theorem tM_comm (i j : GoodPrime N S₀) : Commute (tM N S₀ n i) (tM N S₀ n j) :=
  ModularForm.heckeTLin_comm (wt n) i.2.1 i.2.2.1 j.2.1 j.2.2.1

variable {N S₀ n}

theorem IsCoeffMap.map_ev {R R' : Type} [CommRing R] [CommRing R'] {φ : R →+* R'}
    {Φ : H1 R N n →+ H1 R' N n} (hΦ : IsCoeffMap N n φ Φ) (w : FreeAlgebra ℤ (GoodPrime N S₀))
    (x : H1 R N n) : Φ (ev (tH N S₀ n R) w x) = ev (tH N S₀ n R') w (Φ x) :=
  map_ev_apply (tH N S₀ n R) (tH N S₀ n R') Φ (fun i y => hΦ.hecke i y) w x

theorem exists_eigenclass_of_eigenform [NeZero N] (χ : GoodPrime N S₀ → ℂ) (g : MF N (wt n)) (hg0 : g ≠ 0)
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

theorem ev_lam_eq_zero [NeZero N] {F : Type} [Field F] (lam : ℕ → F)
    (y : F ⊗[ℤ] ↥(intForms N (wt n))) (hy0 : y ≠ 0)
    (heig : ∀ i : GoodPrime N S₀, (tL N S₀ n i).baseChange F y = lam i • y)
    (w : FreeAlgebra ℤ (GoodPrime N S₀)) (hw : ev (tH N S₀ n ℤ) w = 0) :
    ev (fun i : GoodPrime N S₀ => lam i) w = 0 := by

  obtain ⟨Φc, hΦc⟩ := exists_isCoeffMap N n (Int.castRingHom ℂ)
  have hC : ev (tH N S₀ n ℂ) w = 0 :=
    hΦc.eq_zero_of_forall_apply_eq_zero _ fun x => by rw [← hΦc.map_ev, hw, LinearMap.zero_apply, map_zero]

  have hnil : IsNilpotent (ev (tM N S₀ n) w) := by
    haveI : FiniteDimensional ℂ (MF N (wt n)) := ModularForm.finiteDimensional_Gamma0 N (wt n)
    refine Module.End.isNilpotent_of_mem_adjoin_of_forall_eigenvector_apply_eq_zero (tM N S₀ n)
      (tM_comm N S₀ n) _ (ev_mem_adjoin _ w) fun χ g hg0 hg => ?_
    obtain ⟨x, hx0, hx⟩ := exists_eigenclass_of_eigenform χ g hg0 hg
    have h1 := ev_apply_eigenvector (tH N S₀ n ℂ) χ x hx w
    rw [hC, LinearMap.zero_apply] at h1
    have hχ : ev χ w = 0 := (smul_eq_zero.mp h1.symm).resolve_right hx0
    rw [ev_apply_eigenvector (tM N S₀ n) χ g hg w, hχ, zero_smul]
  obtain ⟨m, hm⟩ := hnil

  have hL : ev (tL N S₀ n) (w ^ m) = 0 := by
    refine LinearMap.ext fun f => Subtype.ext ?_
    have hm' : ev (tM N S₀ n) (w ^ m) = 0 := by rw [map_pow, hm]
    have h := map_ev_apply (tL N S₀ n) (tM N S₀ n) (intForms N (wt n)).subtype.toAddMonoidHom
      (fun i x => rfl) (w ^ m) f
    rw [hm'] at h
    simpa using h

  have h4 : ev (fun i : GoodPrime N S₀ => (tL N S₀ n i).baseChange F) (w ^ m) y = 0 := by
    rw [← baseChange_ev, hL, LinearMap.baseChange_zero, LinearMap.zero_apply]
  have h5 := ev_apply_eigenvector (fun i : GoodPrime N S₀ => (tL N S₀ n i).baseChange F)
    (fun i => lam i) y heig (w ^ m)
  rw [h4, map_pow] at h5
  have hpow : ev (fun i : GoodPrime N S₀ => lam i) w ^ m = 0 := by
    by_contra hc
    apply hy0
    rw [← one_smul F y, ← inv_mul_cancel₀ hc, mul_smul, ← h5, smul_zero]
  exact IsNilpotent.eq_zero ⟨m, hpow⟩

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

variable (N S₀ n)

theorem moduleFinite_H1_int [NeZero N] : Module.Finite ℤ (H1 ℤ N n) :=
  moduleFinite_coeffH1 N (ρSym ℤ N n)

end Main

end C1ES
p2m_reactivate "P2MW.S_ModPForms_exists_isEigensystemH1_binaryFormRepSL_of_isModPEigen.C1ES"

open C1ES CongruenceSubgroup HeckeEis in
open scoped TensorProduct in

theorem solution (p : ℕ) (hp : p.Prime)
    (N' : ℕ) [NeZero N'] (hpN' : ¬ p ∣ N')
    (S₀ : Set ℕ) (hS₀fin : S₀.Finite) (hS₀p : p ∈ S₀) (F : Type) [Field F] [CharP F p]
    (k : ℤ) (hk : 2 ≤ k) (φ : PowerSeries F) (lam : ℕ → F)
    (hφ : φ ∈ ModPForms.modPMod N' k F) (heig : ModPForms.IsModPEigen N' S₀ k φ lam) :
    ∃ j : ℕ, HeckeEis.IsEigensystemH1 N'
      ((HeckeEis.binaryFormRepSL F (k - 2).toNat).comp (CongruenceSubgroup.Gamma0 N').subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj F (k - 2).toNat ℓ) S₀ (fun ℓ => (ℓ : F) ^ j * lam ℓ) := by
  haveI : Fact p.Prime := ⟨hp⟩

  set n : ℕ := (k - 2).toNat with hn
  have hkn : k = wt n := by unfold wt; omega
  rw [hkn] at hφ heig
  obtain ⟨hφ0, hφeig⟩ := heig

  obtain ⟨y, rfl⟩ := exists_red_eq_of_mem_modPMod N' (wt n) F hφ
  have hy0 : y ≠ 0 := fun h => hφ0 (by rw [h, map_zero])
  have hyeig : ∀ i : GoodPrime N' S₀, (tL N' S₀ n i).baseChange F y = lam i • y := fun i => by
    apply red_injective N' (wt n) (F := F)
    rw [map_smul, ← hφeig i i.2.1 i.2.2.1 i.2.2.2]
    exact red_baseChange_TL N' (wt n) F (one_le_wt n) i.2.1 i.2.2.1 y

  have hker := fun w hw => ev_lam_eq_zero lam y hy0 hyeig w hw
  obtain ⟨χ, hχ⟩ := exists_algHom_adjoin (tH N' S₀ n ℤ) (fun i : GoodPrime N' S₀ => lam i) hker

  haveI := moduleFinite_coeffH1 N' (ρSym ℤ N' n)
  obtain ⟨y', hy'0, hy'⟩ :=
    Module.exists_ne_zero_forall_baseChange_eq_smul_of_algHom (tH N' S₀ n ℤ) (tH_comm N' S₀ n ℤ) χ
  have hy'' : ∀ i : GoodPrime N' S₀, (tH N' S₀ n ℤ i).baseChange F y' = lam i • y' := fun i => by
    rw [hy' i]
    exact congrArg (fun c : F => c • y') (hχ i)

  obtain ⟨x, hx0, hx⟩ := exists_eigenclass_of_baseChange (fun i : GoodPrime N' S₀ => lam i) y' hy'0 hy''
  refine ⟨0, x, hx0, fun ℓ hℓ hℓN hℓS => ?_⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  refine ⟨TH F N' n ℓ, isCoeffHeckeOnH1_TH F N' n ℓ, ?_⟩
  dsimp only
  rw [pow_zero, one_mul]
  exact hx ⟨ℓ, hℓ, hℓN, hℓS⟩

end S_ModPForms_exists_isEigensystemH1_binaryFormRepSL_of_isModPEigen
end P2MW
export P2MW.S_ModPForms_exists_isEigensystemH1_binaryFormRepSL_of_isModPEigen (solution)
