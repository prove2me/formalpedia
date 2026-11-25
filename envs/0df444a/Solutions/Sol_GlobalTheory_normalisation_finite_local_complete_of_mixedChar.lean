-- Prove2me | solution 1 for GlobalTheory.normalisation_finite_local_complete_of_mixedChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:56:27.012721+00:00
-- url     : https://prove2.me/submissions/d429a06f-0807-48c5-834c-d0d9b98ced53

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_BetaAtSymm
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CohenStructureFiniteOverNormalCompleteSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralClosureFiniteLocalCompleteMixedChar
import Theorems.Thm_GlobalTheory_finite_normalisation_of_finite_over_normal
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero
import Theorems.Thm_GlobalTheory_CohenStructure_exists_finite_injective_of_isAdicComplete
import Theorems.Thm_GlobalTheory_FormalIsogeny_FiniteReduction_map
import Theorems.Thm_GlobalTheory_FormalIsogeny_isAdicComplete_maximalIdeal_of_finite
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X


section
open IsLocalRing
namespace GlobalTheory
open IsLocalRing in
private theorem isPrecomplete_of_finite_module {R M : Type*} [CommRing R] {I : Ideal R} [hR : IsPrecomplete I R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin (R := R) (M := M)
  have hpow : ∀ n, (I ^ n • ⊤ : Submodule R R) = I ^ n := fun n => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have key : ∀ n (x : M), x ∈ (I ^ n • ⊤ : Submodule R M) →
      ∃ c : Fin k → R, (∀ j, c j ∈ I ^ n) ∧ ∑ j, c j • g j = x := by
    intro n x hx
    rw [← hg, Submodule.mem_ideal_smul_span_iff_exists_sum] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨a, ha, by simp [Finsupp.sum_fintype]⟩
  refine ⟨fun {f} hf => ?_⟩
  have hd : ∀ n, f (n + 1) - f n ∈ (I ^ n • ⊤ : Submodule R M) := fun n => by
    have := (hf (Nat.le_succ n))
    rw [SModEq.sub_mem] at this
    simpa using neg_mem this
  choose c hcI hcsum using fun n => key n _ (hd n)
  have hs : ∀ j, ∃ a : R, ∀ n, (∑ i ∈ Finset.range n, c i j) ≡ a [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro j
    refine hR.prec' _ fun {m n} hmn => ?_
    rw [SModEq.sub_mem, hpow]
    have : ∑ i ∈ Finset.range m, c i j - ∑ i ∈ Finset.range n, c i j =
        -∑ i ∈ Finset.Ico m n, c i j := by
      rw [← Finset.sum_range_add_sum_Ico _ hmn]; ring
    rw [this]
    exact neg_mem (Ideal.sum_mem _ fun i hi =>
      Ideal.pow_le_pow_right (Finset.mem_Ico.1 hi).1 (hcI i j))
  choose a ha using hs
  refine ⟨f 0 + ∑ j, a j • g j, fun n => ?_⟩
  have hfn : f n = f 0 + ∑ j, (∑ i ∈ Finset.range n, c i j) • g j := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Finset.sum_range_succ, add_smul, Finset.sum_add_distrib, hcsum n]
      rw [← add_assoc, ← ih]
      abel
  rw [SModEq.sub_mem, hfn, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [← sub_smul]
  have := (SModEq.sub_mem.1 (ha j n))
  rw [hpow] at this
  exact Submodule.smul_mem_smul this Submodule.mem_top
open IsLocalRing in
open Polynomial in
private theorem isLocalRing_of_finite_domain_over_complete (S C : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [IsAdicComplete (maximalIdeal S) S] [CommRing C] [IsDomain C] [Algebra S C]
    [Module.Finite S C] : IsLocalRing C := by
  set I : Ideal C := (maximalIdeal S).map (algebraMap S C) with hI
  haveI : IsPrecomplete (maximalIdeal S) C := isPrecomplete_of_finite_module
  haveI : IsAdicComplete (maximalIdeal S) C := {}
  haveI : IsAdicComplete I C := (IsAdicComplete.map_algebraMap_iff _ _).2 inferInstance
  have hIM : ∀ M : Ideal C, M.IsMaximal → I ≤ M := by
    intro M hM
    rw [hI, Ideal.map_le_iff_le_comap]
    exact (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := S) M)).ge
  haveI : IsArtinianRing (C ⧸ I) := by
    letI := Ideal.Quotient.field (maximalIdeal S)
    haveI : Module.Finite (S ⧸ maximalIdeal S) (C ⧸ I) :=
      Module.Finite.of_restrictScalars_finite S _ _
    exact IsArtinianRing.of_finite (S ⧸ maximalIdeal S) _
  refine IsLocalRing.of_unique_max_ideal ?_
  obtain ⟨M₁, hM₁⟩ := Ideal.exists_maximal C
  refine ⟨M₁, hM₁, fun M₂ hM₂ => ?_⟩
  by_contra hne
  obtain ⟨x, hx₂, hx₁⟩ : ∃ x ∈ M₂, x ∉ M₁ := by
    by_contra! h
    exact hne (hM₂.eq_of_le hM₁.ne_top h)
  set u := Ideal.Quotient.mk I x with hu
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes (R := C ⧸ I) (M := C ⧸ I)
    ⟨fun n => OrderDual.toDual (Ideal.span {u ^ n}),
      fun a b hab => Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow u hab)⟩
  set m := N + 1 with hmdef
  have hm : u ^ m ∈ Ideal.span {u ^ (m + 1)} := by
    have h₁ := hN m (by omega)
    have h₂ := hN (m + 1) (by omega)
    have : Ideal.span {u ^ m} = Ideal.span {u ^ (m + 1)} := by
      exact congrArg OrderDual.ofDual (h₁.symm.trans h₂)
    rw [← this]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 hm
  have hpow : ∀ j, u ^ m = u ^ (m + j) * v ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [ih, pow_add u m j, ← hv]
      ring
  have he : (u ^ m * v ^ m) * (u ^ m * v ^ m) = u ^ m * v ^ m := by
    calc (u ^ m * v ^ m) * (u ^ m * v ^ m) = (u ^ (m + m) * v ^ m) * v ^ m := by ring
      _ = u ^ m * v ^ m := by rw [← hpow m]
  have hue : u ^ m = u ^ m * (u ^ m * v ^ m) := by
    calc u ^ m = u ^ (m + m) * v ^ m := hpow m
      _ = u ^ m * (u ^ m * v ^ m) := by ring
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective v
  set a₀ := x ^ m * y ^ m with ha₀def
  have hmk : Ideal.Quotient.mk I a₀ = u ^ m * Ideal.Quotient.mk I y ^ m := by
    simp [ha₀def, hu]
  have hmon : (X ^ 2 - X : C[X]).Monic := by monicity!
  have heval : (X ^ 2 - X : C[X]).eval a₀ ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [eval_sub, eval_pow, eval_X, map_sub, map_pow, hmk]
    rw [sq, he, sub_self]
  have hder : (derivative (X ^ 2 - X : C[X])).eval a₀ = 2 * a₀ - 1 := by
    simp only [derivative_sub, derivative_X_pow, derivative_X, eval_sub, eval_mul, eval_C,
      eval_pow, eval_X, eval_one]
    norm_num
  have hunit : IsUnit (Ideal.Quotient.mk I ((derivative (X ^ 2 - X : C[X])).eval a₀)) := by
    rw [hder, map_sub, map_mul, hmk, map_one, map_ofNat]
    exact (Units.mkOfMulEqOne _ (2 * (u ^ m * Ideal.Quotient.mk I y ^ m) - 1)
      (by linear_combination 4 * he)).isUnit
  obtain ⟨a, ha, haa₀⟩ := HenselianRing.is_henselian (I := I) _ hmon a₀ heval hunit
  have ha' : a * (a - 1) = 0 := by
    have : a ^ 2 - a = 0 := by simpa using ha
    linear_combination this
  have hx₂m : a₀ ∈ M₂ := M₂.mul_mem_right _ (M₂.pow_mem_of_mem hx₂ m (by omega))
  rcases mul_eq_zero.1 ha' with h0 | h1
  · subst h0
    have ha₀I : a₀ ∈ I := by simpa using neg_mem haa₀
    have hxm : x ^ m - x ^ m * a₀ ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hmk, map_pow, ← hu, ← hue,
        sub_self]
    have : x ^ m ∈ M₁ := by
      have h := hIM M₁ hM₁ hxm
      have h' := M₁.mul_mem_left (x ^ m) (hIM M₁ hM₁ ha₀I)
      simpa using M₁.add_mem h h'
    exact hx₁ (hM₁.isPrime.mem_of_pow_mem m this)
  · have h1' : a = 1 := sub_eq_zero.1 h1
    subst h1'
    have : (1 : C) ∈ M₂ := by
      have h := hIM M₂ hM₂ haa₀
      simpa using M₂.add_mem h hx₂m
    exact hM₂.ne_top ((Ideal.eq_top_iff_one _).2 this)
end GlobalTheory
end

set_option autoImplicit false
open IsLocalRing
open GlobalTheory
open IsLocalRing
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [CharZero S] (p : ℕ), p.Prime →
      (p : S) ∈ maximalIdeal S → IsNoetherianRing S → IsAdicComplete (maximalIdeal S) S →
      Module.Finite S (integralClosure S (FractionRing S)) ∧
        ∃ _ : IsLocalRing (integralClosure S (FractionRing S)),
          IsNoetherianRing (integralClosure S (FractionRing S)) ∧
          IsAdicComplete (maximalIdeal (integralClosure S (FractionRing S)))
            (integralClosure S (FractionRing S)) := by
  intro S _ _ _ _ p hp hpm hS hSc
  obtain ⟨A, _, _, _, i, hi, hfin, hAn, hAic, hAc⟩ :=
    _root_.GlobalTheory.CohenStructure.exists_finite_injective_of_isAdicComplete S p hp hpm hS hSc
  letI : Algebra A S := i.toAlgebra
  haveI : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).2 hi
  haveI : Module.Finite A S := hfin
  haveI := hAn
  haveI := hAic
  haveI := hS
  haveI := hSc
  haveI hC : Module.Finite S (integralClosure S (FractionRing S)) := _root_.GlobalTheory.finite_normalisation_of_finite_over_normal A S
  haveI : IsLocalRing (integralClosure S (FractionRing S)) := isLocalRing_of_finite_domain_over_complete S _
  haveI : IsNoetherianRing (integralClosure S (FractionRing S)) := isNoetherian_of_tower S inferInstance
  exact ⟨hC, inferInstance, inferInstance,
    _root_.GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite S _⟩
end _root_.GlobalTheory
end GlobalTheory
