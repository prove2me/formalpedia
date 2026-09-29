-- Prove2me | solution 1 for ModularCurve.CharPModel.isDiscreteValuationRing_localizationAtPrime_of_derivative_evalEval_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/03506e3b-c937-50e9-b7b6-bdf4a265118d

import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Polynomial.Bivariate
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_isDiscreteValuationRing_localizationAtPrime_of_derivative_evalEval_ne_zero

open Polynomial IsLocalRing

namespace CharpS10bB

section PrincipalRegular

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] {t : T}

theorem exists_isUnit_mul_pow_eq_of_maximalIdeal_eq_span
    (ht : maximalIdeal T = Ideal.span {t}) {a : T} (ha : a ≠ 0) :
    ∃ (n : ℕ) (u : T), IsUnit u ∧ a = u * t ^ n := by
  classical
  have hKrull : ⨅ i : ℕ, (maximalIdeal T) ^ i • (⊤ : Submodule T T) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal T).ne_top
  have hex : ∃ n : ℕ, a ∉ (maximalIdeal T) ^ n := by
    by_contra! h
    apply ha
    have hmem : a ∈ ⨅ i : ℕ, (maximalIdeal T) ^ i • (⊤ : Submodule T T) := by
      simp only [Submodule.mem_iInf, Ideal.smul_eq_mul, Ideal.mul_top]
      exact h
    rw [hKrull] at hmem
    simpa using hmem
  have hn : a ∉ maximalIdeal T ^ Nat.find hex := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    apply hn
    rw [h0, pow_zero, Ideal.one_eq_top]
    trivial
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := Nat.exists_eq_succ_of_ne_zero hn0
  have hmem : a ∈ maximalIdeal T ^ m := by
    have := Nat.find_min hex (m := m) (by omega)
    simpa using this
  rw [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨m, c, ?_, by rw [hc, mul_comm]⟩
  by_contra hcu
  have hcm : c ∈ maximalIdeal T := by
    simpa [mem_maximalIdeal, mem_nonunits_iff] using hcu
  apply hn
  rw [hm, ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hc]
  rw [ht, Ideal.mem_span_singleton] at hcm
  obtain ⟨d, rfl⟩ := hcm
  exact ⟨d, by ring⟩

theorem isDomain_of_maximalIdeal_eq_span_of_mem_nonZeroDivisors
    (ht : maximalIdeal T = Ideal.span {t}) (hreg : t ∈ nonZeroDivisors T) : IsDomain T := by
  have hpow : ∀ k : ℕ, t ^ k ≠ 0 := fun k ↦ nonZeroDivisors.ne_zero (pow_mem hreg k)
  haveI : NoZeroDivisors T := ⟨fun {a b} hab ↦ by
    by_contra! h
    obtain ⟨ha, hb⟩ := h
    obtain ⟨n, u, hu, rfl⟩ := exists_isUnit_mul_pow_eq_of_maximalIdeal_eq_span ht ha
    obtain ⟨m, w, hw, rfl⟩ := exists_isUnit_mul_pow_eq_of_maximalIdeal_eq_span ht hb
    have h1 : u * t ^ n * (w * t ^ m) = (u * w) * t ^ (n + m) := by ring
    rw [h1] at hab
    exact hpow _ ((hu.mul hw).mul_right_eq_zero.mp hab)⟩
  exact NoZeroDivisors.to_isDomain T

theorem exists_isDiscreteValuationRing_of_maximalIdeal_eq_span_of_mem_nonZeroDivisors
    (ht : maximalIdeal T = Ideal.span {t}) (hreg : t ∈ nonZeroDivisors T) :
    ∃ _ : IsDomain T, IsDiscreteValuationRing T := by
  haveI := isDomain_of_maximalIdeal_eq_span_of_mem_nonZeroDivisors ht hreg
  refine ⟨this, ?_⟩
  have hnf : ¬ IsField T := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, ht, Ideal.span_singleton_eq_bot]
    exact nonZeroDivisors.ne_zero hreg
  have hprinc : (maximalIdeal T).IsPrincipal := ⟨⟨t, ht⟩⟩
  exact ((IsDiscreteValuationRing.TFAE T hnf).out 4 0).mp hprinc

end PrincipalRegular

section StandardEtale

variable {R : Type*} [CommRing R] {P : R[X]}

theorem isUnramifiedAt_adjoinRoot_of_derivative_notMem (hP : P.Monic)
    (𝔮 : Ideal (AdjoinRoot P)) [𝔮.IsPrime] (hd : AdjoinRoot.mk P (derivative P) ∉ 𝔮) :
    Algebra.IsUnramifiedAt R 𝔮 := by
  let pair : StandardEtalePair R := ⟨P, hP, derivative P, 1, 0, 1, by simp⟩
  have hFU : Algebra.FormallyUnramified R (Localization.Away (AdjoinRoot.mk P (derivative P))) :=
    .of_equiv pair.equivAwayAdjoinRoot
  have hsub := (Algebra.basicOpen_subset_unramifiedLocus_iff (R := R) (A := AdjoinRoot P)
    (f := AdjoinRoot.mk P (derivative P))).mpr hFU
  exact hsub ((PrimeSpectrum.mem_basicOpen _ ⟨𝔮, inferInstance⟩).mpr hd)

variable [IsDomain R] [IsPrincipalIdealRing R]

theorem exists_isDiscreteValuationRing_localization_adjoinRoot (hP : P.Monic)
    (𝔪 : Ideal (AdjoinRoot P)) [𝔪.IsMaximal]
    (hd : AdjoinRoot.mk P (derivative P) ∉ 𝔪) (hbot : 𝔪.under R ≠ ⊥) :
    ∃ _ : IsDomain (Localization.AtPrime 𝔪),
      IsDiscreteValuationRing (Localization.AtPrime 𝔪) := by
  classical
  haveI : Module.Finite R (AdjoinRoot P) := hP.finite_adjoinRoot
  haveI : Module.Free R (AdjoinRoot P) := hP.free_adjoinRoot
  haveI : IsNoetherianRing (AdjoinRoot P) := Algebra.FiniteType.isNoetherianRing R (AdjoinRoot P)

  haveI : Algebra.IsUnramifiedAt R 𝔪 := isUnramifiedAt_adjoinRoot_of_derivative_notMem hP 𝔪 hd
  letI := Localization.AtPrime.algebraOfLiesOver (𝔪.under R) 𝔪
  have hmap : (𝔪.under R).map (algebraMap R (Localization.AtPrime 𝔪)) = maximalIdeal _ :=
    ((Algebra.isUnramifiedAt_iff_map_eq R (𝔪.under R) 𝔪).mp inferInstance).2

  haveI := IsPrincipalIdealRing.principal (𝔪.under R)
  obtain ⟨π, hπ⟩ := Submodule.IsPrincipal.principal (𝔪.under R)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    apply hbot
    simpa using hπ
  have hmax : maximalIdeal (Localization.AtPrime 𝔪) =
      Ideal.span {algebraMap R (Localization.AtPrime 𝔪) π} := by
    rw [← hmap, show 𝔪.under R = Ideal.span {π} from hπ, Ideal.map_span, Set.image_singleton]

  have hreg : algebraMap R (Localization.AtPrime 𝔪) π ∈ nonZeroDivisors _ := by
    have h1 : IsSMulRegular (Localization.AtPrime 𝔪) π :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hπ0)
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    apply h1
    change π • x = π • (0 : Localization.AtPrime 𝔪)
    rw [smul_zero, Algebra.smul_def, mul_comm, hx]
  exact exists_isDiscreteValuationRing_of_maximalIdeal_eq_span_of_mem_nonZeroDivisors hmax hreg

end StandardEtale

section Fibre

open scoped Polynomial.Bivariate

variable {k : Type*} [Field k] {P : k[X][Y]}

theorem fibre_exists_isDiscreteValuationRing (hP : P.Monic)
    (𝔪 : Ideal (AdjoinRoot P)) [𝔪.IsMaximal] (hd : AdjoinRoot.mk P (derivative P) ∉ 𝔪) :
    ∃ _ : IsDomain (Localization.AtPrime 𝔪),
      IsDiscreteValuationRing (Localization.AtPrime 𝔪) := by
  haveI : Module.Finite k[X] (AdjoinRoot P) := hP.finite_adjoinRoot
  refine exists_isDiscreteValuationRing_localization_adjoinRoot hP 𝔪 hd ?_
  exact Ring.ne_bot_of_isMaximal_of_not_isField inferInstance (Polynomial.not_isField k)

theorem fibre_isIntegrallyClosed (hP : P.Monic)
    (𝔪 : Ideal (AdjoinRoot P)) [𝔪.IsMaximal] (hd : AdjoinRoot.mk P (derivative P) ∉ 𝔪) :
    IsIntegrallyClosed (Localization.AtPrime 𝔪) := by
  obtain ⟨_, _⟩ := fibre_exists_isDiscreteValuationRing hP 𝔪 hd
  exact UniqueFactorizationMonoid.instIsIntegrallyClosed

theorem sub_CC_evalEval_mem_span (F : k[X][Y]) (a b : k) :
    F - CC (F.evalEval a b) ∈ Ideal.span {C (X - C a), Y - CC b} := by
  have h1 : Y - CC b ∣ F - C (F.eval (C b)) := X_sub_C_dvd_sub_C_eval
  have h2 : C (X - C a) ∣ C (F.eval (C b)) - CC (F.evalEval a b) := by
    have h := map_dvd (C : k[X] →+* k[X][Y]) (X_sub_C_dvd_sub_C_eval (p := F.eval (C b)) (a := a))
    simpa [CC, evalEval, map_sub] using h
  have hsplit : F - CC (F.evalEval a b) =
      (F - C (F.eval (C b))) + (C (F.eval (C b)) - CC (F.evalEval a b)) := by ring
  rw [hsplit]
  refine Ideal.add_mem _ ?_ ?_
  · obtain ⟨c, hc⟩ := h1
    rw [hc]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · obtain ⟨c, hc⟩ := h2
    rw [hc]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

set_option maxSynthPendingDepth 3 in

theorem isDiscreteValuationRing_localizationAtPrime_of_derivative_evalEval_ne_zero
    (P : k[X][Y]) (hP : P.Monic) (a b : k)
    (hder : (Polynomial.derivative P).evalEval a b ≠ 0)
    [hm : (Ideal.span {Ideal.Quotient.mk (Ideal.span {P}) (C (X - C a)),
        Ideal.Quotient.mk (Ideal.span {P}) (Y - CC b)}).IsMaximal] :
    ∃ _ : IsDomain (Localization.AtPrime (Ideal.span
      {Ideal.Quotient.mk (Ideal.span {P}) (C (X - C a)),
       Ideal.Quotient.mk (Ideal.span {P}) (Y - CC b)})),
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span
      {Ideal.Quotient.mk (Ideal.span {P}) (C (X - C a)),
       Ideal.Quotient.mk (Ideal.span {P}) (Y - CC b)})) := by

  let 𝔪 : Ideal (AdjoinRoot P) :=
    Ideal.span {AdjoinRoot.mk P (C (X - C a)), AdjoinRoot.mk P (Y - CC b)}
  haveI h𝔪 : 𝔪.IsMaximal := hm
  have hgen : ∀ F ∈ Ideal.span {C (X - C a), Y - CC b}, AdjoinRoot.mk P F ∈ 𝔪 := by
    intro F hF
    have hmapeq : Ideal.map (AdjoinRoot.mk P) (Ideal.span {C (X - C a), Y - CC b}) = 𝔪 := by
      rw [Ideal.map_span, Set.image_pair]
    rw [← hmapeq]
    exact Ideal.mem_map_of_mem _ hF

  have hroot : P.evalEval a b = 0 := by
    by_contra hne
    have hPm : AdjoinRoot.mk P (CC (P.evalEval a b)) ∈ 𝔪 := by
      have h := hgen _ (sub_CC_evalEval_mem_span P a b)
      rw [map_sub, AdjoinRoot.mk_self, zero_sub] at h
      exact (Ideal.neg_mem_iff _).mp h
    have hu : IsUnit (AdjoinRoot.mk P (CC (P.evalEval a b))) :=
      (((isUnit_iff_ne_zero.mpr hne).map C).map C).map (AdjoinRoot.mk P)
    exact hm.ne_top (Ideal.eq_top_of_isUnit_mem 𝔪 hPm hu)

  let ev : AdjoinRoot P →+* k :=
    AdjoinRoot.lift (evalRingHom a) b (by rw [eval₂_evalRingHom]; exact hroot)
  have hev : ∀ F : k[X][Y], ev (AdjoinRoot.mk P F) = F.evalEval a b := fun F ↦ by
    simp only [ev, AdjoinRoot.lift_mk, eval₂_evalRingHom]
  have hker : 𝔪 ≤ RingHom.ker ev := by
    rw [Ideal.span_le]
    rintro _ (rfl | rfl)
    · rw [SetLike.mem_coe, RingHom.mem_ker, hev]
      simp [evalEval]
    · rw [SetLike.mem_coe, RingHom.mem_ker, hev]
      simp [evalEval, CC]
  have hd : AdjoinRoot.mk P (derivative P) ∉ 𝔪 := fun h ↦ hder (by
    have h' := hker h
    rwa [RingHom.mem_ker, hev] at h')
  exact fibre_exists_isDiscreteValuationRing (k := k) hP 𝔪 hd

end Fibre

end CharpS10bB

set_option maxSynthPendingDepth 3 in
open scoped Polynomial.Bivariate in
theorem solution
    {k : Type*} [Field k] (P : k[X][Y]) (hP : P.Monic) (a b : k)
    (hder : (Polynomial.derivative P).evalEval a b ≠ 0)
    [hm : (Ideal.span {Ideal.Quotient.mk (Ideal.span {P}) (C (X - C a)),
        Ideal.Quotient.mk (Ideal.span {P}) (Y - CC b)}).IsMaximal] :
    ∃ _ : IsDomain (Localization.AtPrime (Ideal.span
      {Ideal.Quotient.mk (Ideal.span {P}) (C (X - C a)),
       Ideal.Quotient.mk (Ideal.span {P}) (Y - CC b)})),
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span
      {Ideal.Quotient.mk (Ideal.span {P}) (C (X - C a)),
       Ideal.Quotient.mk (Ideal.span {P}) (Y - CC b)})) :=
  CharpS10bB.isDiscreteValuationRing_localizationAtPrime_of_derivative_evalEval_ne_zero
    (P := P) (hP := hP) (a := a) (b := b) (hder := hder)

end S_ModularCurve_CharPModel_isDiscreteValuationRing_localizationAtPrime_of_derivative_evalEval_ne_zero
end P2MW
export P2MW.S_ModularCurve_CharPModel_isDiscreteValuationRing_localizationAtPrime_of_derivative_evalEval_ne_zero (solution)
