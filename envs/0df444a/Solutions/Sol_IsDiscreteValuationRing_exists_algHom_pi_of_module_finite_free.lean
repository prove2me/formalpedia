-- Prove2me | solution 1 for IsDiscreteValuationRing.exists_algHom_pi_of_module_finite_free
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/3e53c9ba-62a6-570c-b770-8e71de2e8192

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.FreeModule.Basic
import Theorems.Thm_IsLocalRing_isAdicComplete_of_module_finite
import Theorems.Thm_IsLocalRing_of_isDomain_of_moduleFinite_of_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_exists_algHom_pi_of_module_finite_free

set_option autoImplicit false
set_option linter.unusedSectionVars false

section R3

open IsLocalRing

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
  [CharZero 𝒪]
  {T : Type} [CommRing T] [IsReduced T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]

private theorem eq_zero_or_eq_zero_of_smul_eq_zero_of_free {x : 𝒪} {t : T} (h : x • t = 0) :
    x = 0 ∨ t = 0 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    let b := Module.Free.chooseBasis 𝒪 T
    have hrepr : b.repr (x • t) = 0 := by rw [h, map_zero]
    rw [map_smul] at hrepr
    have ht : b.repr t = 0 := by
      ext i
      have hi := DFunLike.congr_fun hrepr i
      rw [Finsupp.smul_apply, smul_eq_mul] at hi
      simpa using (mul_eq_zero.mp hi).resolve_left hx
    exact b.repr.map_eq_zero_iff.mp ht

private theorem algebraMap_quotient_injective_of_mem_minimalPrimes
    (P : Ideal T) (hP : P ∈ minimalPrimes T) :
    Function.Injective (algebraMap 𝒪 (T ⧸ P)) := by
  haveI : P.IsPrime := hP.1.1
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  have hmem : algebraMap 𝒪 T x ∈ P := by
    rw [IsScalarTower.algebraMap_apply 𝒪 T (T ⧸ P)] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mp hx
  have hnzd : algebraMap 𝒪 T x ∈ nonZeroDivisors T := by
    rw [mem_nonZeroDivisors_iff_right]
    intro t ht
    have hsmul : x • t = 0 := by rw [Algebra.smul_def, mul_comm]; exact ht
    exact (eq_zero_or_eq_zero_of_smul_eq_zero_of_free hsmul).resolve_left hx0
  exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hmem hP hnzd

variable (𝒪) in

private abbrev IntClosure (P : Ideal T) [P.IsPrime] : Type :=
  integralClosure 𝒪 (FractionRing (T ⧸ P))

section PerPrime

variable (P : Ideal T) [P.IsPrime]
  (hinj : Function.Injective (algebraMap 𝒪 (T ⧸ P)))

include hinj in

private theorem moduleFinite_intClosure : Module.Finite 𝒪 (IntClosure 𝒪 P) := by
  haveI : FaithfulSMul 𝒪 (T ⧸ P) := (faithfulSMul_iff_algebraMap_injective 𝒪 (T ⧸ P)).mpr hinj
  haveI : Module.Finite 𝒪 (T ⧸ P) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ 𝒪 P).toLinearMap
      (Ideal.Quotient.mkₐ_surjective 𝒪 P)
  haveI : CharZero (T ⧸ P) := charZero_of_injective_algebraMap hinj
  haveI : CharZero (FractionRing 𝒪) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 (FractionRing 𝒪))
  haveI : Module.IsTorsionFree 𝒪 (T ⧸ P) :=
    Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  letI : Algebra (FractionRing 𝒪) (FractionRing (T ⧸ P)) := FractionRing.liftAlgebra _ _
  haveI : IsScalarTower 𝒪 (FractionRing 𝒪) (FractionRing (T ⧸ P)) :=
    FractionRing.isScalarTower_liftAlgebra _ _
  exact IsIntegralClosure.finite 𝒪 (FractionRing 𝒪) (FractionRing (T ⧸ P)) (IntClosure 𝒪 P)

include hinj in
private theorem algebraMap_intClosure_injective :
    Function.Injective (algebraMap 𝒪 (IntClosure 𝒪 P)) := by
  have h1 : Function.Injective (algebraMap 𝒪 (FractionRing (T ⧸ P))) := by
    rw [IsScalarTower.algebraMap_eq 𝒪 (T ⧸ P) (FractionRing (T ⧸ P))]
    exact (IsFractionRing.injective (T ⧸ P) (FractionRing (T ⧸ P))).comp hinj
  intro x y hxy
  apply h1
  rw [IsScalarTower.algebraMap_apply 𝒪 (IntClosure 𝒪 P) (FractionRing (T ⧸ P)),
    IsScalarTower.algebraMap_apply 𝒪 (IntClosure 𝒪 P) (FractionRing (T ⧸ P)), hxy]

include hinj in
private theorem charZero_intClosure : CharZero (IntClosure 𝒪 P) :=
  charZero_of_injective_algebraMap (algebraMap_intClosure_injective P hinj)

include hinj in

private theorem isDedekindDomain_intClosure : IsDedekindDomain (IntClosure 𝒪 P) := by
  haveI : FaithfulSMul 𝒪 (T ⧸ P) := (faithfulSMul_iff_algebraMap_injective 𝒪 (T ⧸ P)).mpr hinj
  haveI : Module.Finite 𝒪 (T ⧸ P) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ 𝒪 P).toLinearMap
      (Ideal.Quotient.mkₐ_surjective 𝒪 P)
  haveI : CharZero (T ⧸ P) := charZero_of_injective_algebraMap hinj
  haveI : CharZero (FractionRing 𝒪) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 (FractionRing 𝒪))
  haveI : Module.IsTorsionFree 𝒪 (T ⧸ P) :=
    Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  letI : Algebra (FractionRing 𝒪) (FractionRing (T ⧸ P)) := FractionRing.liftAlgebra _ _
  haveI : IsScalarTower 𝒪 (FractionRing 𝒪) (FractionRing (T ⧸ P)) :=
    FractionRing.isScalarTower_liftAlgebra _ _
  exact IsIntegralClosure.isDedekindDomain 𝒪 (FractionRing 𝒪) (FractionRing (T ⧸ P))
    (IntClosure 𝒪 P)

include hinj in
private theorem isDVR_intClosure [IsLocalRing (IntClosure 𝒪 P)] :
    IsDiscreteValuationRing (IntClosure 𝒪 P) := by
  haveI : IsDedekindDomain (IntClosure 𝒪 P) := isDedekindDomain_intClosure P hinj
  refine ⟨?_⟩
  intro hbot
  have hfieldR : IsField (IntClosure 𝒪 P) := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot
  have hfield𝒪 : IsField 𝒪 :=
    isField_of_isIntegral_of_isField (algebraMap_intClosure_injective P hinj) hfieldR
  exact IsDiscreteValuationRing.not_a_field 𝒪 (IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield𝒪)

include hinj in
private theorem isLocalHom_intClosure [IsLocalRing (IntClosure 𝒪 P)] :
    IsLocalHom (algebraMap 𝒪 (IntClosure 𝒪 P)) := by
  haveI : FaithfulSMul 𝒪 (IntClosure 𝒪 P) :=
    (faithfulSMul_iff_algebraMap_injective 𝒪 (IntClosure 𝒪 P)).mpr
      (algebraMap_intClosure_injective P hinj)
  exact Algebra.IsIntegral.isLocalHom 𝒪 (IntClosure 𝒪 P)

include hinj in

private theorem isAdicComplete_intClosure [IsLocalRing (IntClosure 𝒪 P)] :
    IsAdicComplete (IsLocalRing.maximalIdeal (IntClosure 𝒪 P)) (IntClosure 𝒪 P) := by
  haveI := moduleFinite_intClosure P hinj
  haveI := isLocalHom_intClosure P hinj
  exact IsLocalRing.isAdicComplete_of_module_finite (𝒪 := 𝒪)

include hinj in

private theorem finite_residueField_intClosure [IsLocalRing (IntClosure 𝒪 P)] :
    Finite (IsLocalRing.ResidueField (IntClosure 𝒪 P)) := by
  haveI := moduleFinite_intClosure P hinj
  haveI := isLocalHom_intClosure P hinj
  exact IsLocalRing.ResidueField.finite_of_finite (R := 𝒪) ‹_›

private noncomputable def toIntClosure : T →ₐ[𝒪] IntClosure 𝒪 P :=
  AlgHom.codRestrict
    ((IsScalarTower.toAlgHom 𝒪 (T ⧸ P) (FractionRing (T ⧸ P))).comp (Ideal.Quotient.mkₐ 𝒪 P))
    (integralClosure 𝒪 (FractionRing (T ⧸ P)))
    (fun t => (Algebra.IsIntegral.isIntegral (R := 𝒪) t).map
      ((IsScalarTower.toAlgHom 𝒪 (T ⧸ P) (FractionRing (T ⧸ P))).comp (Ideal.Quotient.mkₐ 𝒪 P)))

private theorem toIntClosure_eq_zero_iff {t : T} :
    toIntClosure (𝒪 := 𝒪) P t = 0 ↔ t ∈ P := by
  constructor
  · intro h
    have hval : algebraMap (T ⧸ P) (FractionRing (T ⧸ P)) (Ideal.Quotient.mk P t) = 0 := by
      have := congrArg (Subtype.val) h
      simpa [toIntClosure] using this
    have hmk : Ideal.Quotient.mk P t = 0 :=
      (map_eq_zero_iff _ (IsFractionRing.injective (T ⧸ P) (FractionRing (T ⧸ P)))).mp hval
    exact Ideal.Quotient.eq_zero_iff_mem.mp hmk
  · intro h
    apply Subtype.ext
    show algebraMap (T ⧸ P) (FractionRing (T ⧸ P)) (Ideal.Quotient.mk P t) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

end PerPrime

private theorem exists_embedding_into_dvrs_finite_of_local
    (hloc : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra 𝒪 D] [Module.Finite 𝒪 D],
      IsLocalRing D) :
    ∃ (n : ℕ) (R : Fin n → Type) (_ : ∀ j, CommRing (R j)) (_ : ∀ j, IsDomain (R j))
      (_ : ∀ j, IsDiscreteValuationRing (R j))
      (_ : ∀ j, IsAdicComplete (IsLocalRing.maximalIdeal (R j)) (R j))
      (_ : ∀ j, Finite (IsLocalRing.ResidueField (R j))) (_ : ∀ j, CharZero (R j))
      (_ : ∀ j, Algebra 𝒪 (R j)) (_ : ∀ j, Module.Finite 𝒪 (R j))
      (_ : ∀ j, IsLocalHom (algebraMap 𝒪 (R j)))
      (ι : T →ₐ[𝒪] ((j : Fin n) → R j)),
      Function.Injective ι := by
  haveI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing 𝒪 T
  have hfin : (minimalPrimes T).Finite := minimalPrimes.finite_of_isNoetherianRing T
  haveI := hfin.fintype
  let e : Fin (Fintype.card (minimalPrimes T)) ≃ (minimalPrimes T) := (Fintype.equivFin _).symm
  haveI hprime : ∀ j, ((e j : Ideal T)).IsPrime := fun j => (e j).2.1.1
  have hinj : ∀ j, Function.Injective (algebraMap 𝒪 (T ⧸ (e j : Ideal T))) := fun j =>
    algebraMap_quotient_injective_of_mem_minimalPrimes _ (e j).2
  haveI hlocal : ∀ j, IsLocalRing (IntClosure 𝒪 (e j : Ideal T)) := fun j => by
    haveI := moduleFinite_intClosure (𝒪 := 𝒪) (e j : Ideal T) (hinj j)
    exact hloc _
  refine ⟨_, fun j => IntClosure 𝒪 (e j : Ideal T),
    fun j => inferInstance,
    fun j => inferInstance,
    fun j => isDVR_intClosure _ (hinj j),
    fun j => isAdicComplete_intClosure _ (hinj j),
    fun j => finite_residueField_intClosure _ (hinj j),
    fun j => charZero_intClosure _ (hinj j),
    fun j => inferInstance,
    fun j => moduleFinite_intClosure _ (hinj j),
    fun j => isLocalHom_intClosure _ (hinj j),
    Pi.algHom _ _ (fun j => toIntClosure (e j : Ideal T)),
    ?_⟩
  rw [injective_iff_map_eq_zero]
  intro t ht
  have hmem : ∀ p ∈ minimalPrimes T, t ∈ p := by
    intro p hp
    have hj := congr_fun ht (e.symm ⟨p, hp⟩)
    have hzero : toIntClosure (𝒪 := 𝒪) (e (e.symm ⟨p, hp⟩) : Ideal T) t = 0 := hj
    have hP : t ∈ (e (e.symm ⟨p, hp⟩) : Ideal T) :=
      (toIntClosure_eq_zero_iff _).mp hzero
    have : (e (e.symm ⟨p, hp⟩) : Ideal T) = p := by rw [e.apply_symm_apply]
    exact this ▸ hP
  have hsinf : t ∈ sInf ((⊥ : Ideal T).minimalPrimes) :=
    Submodule.mem_sInf.mpr (fun p hp => hmem p hp)
  rw [Ideal.sInf_minimalPrimes, ← Ideal.zero_eq_bot, ← nilradical, nilradical_eq_zero,
    Ideal.zero_eq_bot] at hsinf
  exact (Ideal.mem_bot).mp hsinf

private theorem exists_embedding_into_dvrs_of_local
    (hloc : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra 𝒪 D] [Module.Finite 𝒪 D],
      IsLocalRing D) :
    ∃ (n : ℕ) (R : Fin n → Type) (_ : ∀ j, CommRing (R j)) (_ : ∀ j, IsDomain (R j))
      (_ : ∀ j, IsDiscreteValuationRing (R j))
      (_ : ∀ j, IsAdicComplete (IsLocalRing.maximalIdeal (R j)) (R j))
      (_ : ∀ j, Finite (IsLocalRing.ResidueField (R j))) (_ : ∀ j, CharZero (R j))
      (_ : ∀ j, Algebra 𝒪 (R j)) (_ : ∀ j, IsLocalHom (algebraMap 𝒪 (R j)))
      (ι : T →ₐ[𝒪] ((j : Fin n) → R j)),
      Function.Injective ι := by
  obtain ⟨n, R, h1, h2, h3, h4, h5, h6, h7, _, h9, ι, hι⟩ :=
    exists_embedding_into_dvrs_finite_of_local (T := T) hloc
  exact ⟨n, R, h1, h2, h3, h4, h5, h6, h7, h9, ι, hι⟩

private theorem exists_embedding_into_dvrs_of_local' [Nontrivial T]
    (hloc : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra 𝒪 D] [Module.Finite 𝒪 D],
      IsLocalRing D) :
    ∃ (n : ℕ) (_ : NeZero n) (R : Fin n → Type) (_ : ∀ j, CommRing (R j))
      (_ : ∀ j, IsDomain (R j)) (_ : ∀ j, IsDiscreteValuationRing (R j))
      (_ : ∀ j, IsAdicComplete (IsLocalRing.maximalIdeal (R j)) (R j))
      (_ : ∀ j, Finite (IsLocalRing.ResidueField (R j))) (_ : ∀ j, CharZero (R j))
      (_ : ∀ j, Algebra 𝒪 (R j)) (_ : ∀ j, Module.Finite 𝒪 (R j))
      (_ : ∀ j, IsLocalHom (algebraMap 𝒪 (R j)))
      (ι : T →ₐ[𝒪] ((j : Fin n) → R j)),
      Function.Injective ι := by
  obtain ⟨n, R, h1, h2, h3, h4, h5, h6, h7, h8, h9, ι, hι⟩ :=
    exists_embedding_into_dvrs_finite_of_local (T := T) hloc
  have hn : n ≠ 0 := by
    rintro rfl
    have h10 : ι 1 = ι 0 := funext fun j => j.elim0
    exact one_ne_zero (hι h10)
  exact ⟨n, ⟨hn⟩, R, h1, h2, h3, h4, h5, h6, h7, h8, h9, ι, hι⟩

private theorem exists_embedding_into_dvrs :
    ∃ (n : ℕ) (R : Fin n → Type) (_ : ∀ j, CommRing (R j)) (_ : ∀ j, IsDomain (R j))
      (_ : ∀ j, IsDiscreteValuationRing (R j))
      (_ : ∀ j, IsAdicComplete (IsLocalRing.maximalIdeal (R j)) (R j))
      (_ : ∀ j, Finite (IsLocalRing.ResidueField (R j))) (_ : ∀ j, CharZero (R j))
      (_ : ∀ j, Algebra 𝒪 (R j)) (_ : ∀ j, IsLocalHom (algebraMap 𝒪 (R j)))
      (ι : T →ₐ[𝒪] ((j : Fin n) → R j)),
      Function.Injective ι :=
  exists_embedding_into_dvrs_of_local
    (fun D _ _ _ _ => IsLocalRing.of_isDomain_of_moduleFinite_of_isAdicComplete 𝒪 D)

end R3

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪]
    (T : Type) [CommRing T] [IsReduced T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T] :
    ∃ (n : ℕ) (R : Fin n → Type) (_ : ∀ j, CommRing (R j)) (_ : ∀ j, IsDomain (R j))
      (_ : ∀ j, IsDiscreteValuationRing (R j))
      (_ : ∀ j, IsAdicComplete (IsLocalRing.maximalIdeal (R j)) (R j))
      (_ : ∀ j, Finite (IsLocalRing.ResidueField (R j))) (_ : ∀ j, CharZero (R j))
      (_ : ∀ j, Algebra 𝒪 (R j)) (_ : ∀ j, IsLocalHom (algebraMap 𝒪 (R j)))
      (ι : T →ₐ[𝒪] ((j : Fin n) → R j)),
      Function.Injective ι :=
  exists_embedding_into_dvrs (𝒪 := 𝒪) (T := T)

end S_IsDiscreteValuationRing_exists_algHom_pi_of_module_finite_free
end P2MW
export P2MW.S_IsDiscreteValuationRing_exists_algHom_pi_of_module_finite_free (solution)
