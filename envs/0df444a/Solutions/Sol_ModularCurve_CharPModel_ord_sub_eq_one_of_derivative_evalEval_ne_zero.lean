-- Prove2me | solution 1 for ModularCurve.CharPModel.ord_sub_eq_one_of_derivative_evalEval_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/8d279c68-8167-59ea-a7c1-5bf89e1db5cc

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Mathlib.Algebra.Polynomial.Bivariate
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

namespace P2MW.S_ModularCurve_CharPModel_ord_sub_eq_one_of_derivative_evalEval_ne_zero

set_option autoImplicit false

section FO

open Polynomial IsLocalRing

namespace OrdOneFO

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
      IsDiscreteValuationRing (Localization.AtPrime 𝔪) ∧
      (𝔪.under R).map (algebraMap R (Localization.AtPrime 𝔪)) = maximalIdeal _ := by
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
  obtain ⟨hdom', hdvr'⟩ :=
    exists_isDiscreteValuationRing_of_maximalIdeal_eq_span_of_mem_nonZeroDivisors hmax hreg
  exact ⟨hdom', hdvr', hmap⟩

end StandardEtale

section Fibre

open scoped Polynomial.Bivariate

variable {k : Type*} [Field k] {P : k[X][Y]}

theorem fibre_exists_isDiscreteValuationRing (hP : P.Monic)
    (𝔪 : Ideal (AdjoinRoot P)) [𝔪.IsMaximal] (hd : AdjoinRoot.mk P (derivative P) ∉ 𝔪) :
    ∃ _ : IsDomain (Localization.AtPrime 𝔪),
      IsDiscreteValuationRing (Localization.AtPrime 𝔪) ∧
      (𝔪.under k[X]).map (algebraMap k[X] (Localization.AtPrime 𝔪)) = maximalIdeal _ := by
  haveI : Module.Finite k[X] (AdjoinRoot P) := hP.finite_adjoinRoot
  refine exists_isDiscreteValuationRing_localization_adjoinRoot hP 𝔪 hd ?_
  exact Ring.ne_bot_of_isMaximal_of_not_isField inferInstance (Polynomial.not_isField k)

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

theorem isDVR_and_maximalIdeal_eq_span
    (P : k[X][Y]) (hP : P.Monic) (a b : k)
    (hder : (Polynomial.derivative P).evalEval a b ≠ 0)
    [hm : (Ideal.span {Ideal.Quotient.mk (Ideal.span {P}) (C (X - C a)),
        Ideal.Quotient.mk (Ideal.span {P}) (Y - CC b)}).IsMaximal] :
    ∃ _ : IsDomain (Localization.AtPrime (Ideal.span
      {Ideal.Quotient.mk (Ideal.span {P}) (C (X - C a)),
       Ideal.Quotient.mk (Ideal.span {P}) (Y - CC b)})),
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span
      {Ideal.Quotient.mk (Ideal.span {P}) (C (X - C a)),
       Ideal.Quotient.mk (Ideal.span {P}) (Y - CC b)})) ∧
    maximalIdeal (Localization.AtPrime (Ideal.span
      {Ideal.Quotient.mk (Ideal.span {P}) (C (X - C a)),
       Ideal.Quotient.mk (Ideal.span {P}) (Y - CC b)})) =
      Ideal.span {algebraMap (k[X][Y] ⧸ Ideal.span {P}) (Localization.AtPrime (Ideal.span
        {Ideal.Quotient.mk (Ideal.span {P}) (C (X - C a)),
         Ideal.Quotient.mk (Ideal.span {P}) (Y - CC b)}))
        (Ideal.Quotient.mk (Ideal.span {P}) (C (X - C a)))} := by

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
  obtain ⟨hdom, hdvr, hmap⟩ := fibre_exists_isDiscreteValuationRing (k := k) hP 𝔪 hd
  refine ⟨hdom, hdvr, ?_⟩

  have halg : ∀ p : k[X], algebraMap k[X] (AdjoinRoot P) p = AdjoinRoot.mk P (C p) := fun p ↦ by
    rw [AdjoinRoot.algebraMap_eq]; rfl
  have hXa : (X - C a : k[X]) ∈ 𝔪.under k[X] := by
    rw [Ideal.under_def, Ideal.mem_comap, halg]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have hunder : 𝔪.under k[X] = Ideal.span {X - C a} := by
    refine ((PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C a)).eq_of_le
      ?_ ?_).symm
    · rw [Ideal.under_def]; exact Ideal.comap_ne_top _ h𝔪.ne_top
    · rw [Ideal.span_le, Set.singleton_subset_iff]; exact hXa
  have key : maximalIdeal (Localization.AtPrime 𝔪) =
      Ideal.span {algebraMap (AdjoinRoot P) (Localization.AtPrime 𝔪)
        (AdjoinRoot.mk P (C (X - C a)))} := by
    rw [← hmap, hunder, Ideal.map_span, Set.image_singleton,
      IsScalarTower.algebraMap_apply k[X] (AdjoinRoot P) (Localization.AtPrime 𝔪), halg]
  exact key

end Fibre

end OrdOneFO

end FO

noncomputable section

open ModularCurve AlgebraicCurve Polynomial
open scoped Polynomial.Bivariate

namespace OrdOneHelper
namespace DE

private theorem exists_mul_eq_of_forall_mem_closure_range {L B : Type*} [Field L] [CommRing B]
    (π : B →+* L) (hgen : ∀ x : L, x ∈ Subfield.closure (π.range : Set L)) :
    ∀ x : L, ∃ b c : B, π c ≠ 0 ∧ x * π c = π b := by
  intro x
  obtain ⟨y, hy, z, hz, hyz⟩ := Subfield.mem_closure_iff.mp (hgen x)
  rw [Subring.closure_eq] at hy hz
  obtain ⟨b, rfl⟩ := RingHom.mem_range.mp hy
  obtain ⟨c, rfl⟩ := RingHom.mem_range.mp hz
  by_cases hc : π c = 0
  · refine ⟨0, 1, by simp, ?_⟩
    rw [← hyz, hc, div_zero, map_one, map_zero, zero_mul]
  · exact ⟨b, c, hc, ((div_eq_iff hc).mp hyz).symm⟩

private theorem forall_mem_closure_range_of_adjoin {F E : Type*} [Field F] [Field E] [Algebra F E]
    (S : Set E) {B : Type*} [CommRing B] (π : B →+* IntermediateField.adjoin F S)
    (hconst : ∀ c : F, algebraMap F (IntermediateField.adjoin F S) c ∈
      Subfield.closure (π.range : Set (IntermediateField.adjoin F S)))
    (hgen : ∀ (s : E) (hs : s ∈ S),
      (⟨s, IntermediateField.subset_adjoin F S hs⟩ : IntermediateField.adjoin F S) ∈
        Subfield.closure (π.range : Set (IntermediateField.adjoin F S))) :
    ∀ x : IntermediateField.adjoin F S,
      x ∈ Subfield.closure (π.range : Set (IntermediateField.adjoin F S)) := by
  intro x
  set T := Subfield.closure (π.range : Set (IntermediateField.adjoin F S)) with hT
  let T' : Subfield E := T.map (algebraMap (IntermediateField.adjoin F S) E)
  have hle : Subfield.closure (Set.range (algebraMap F E) ∪ S) ≤ T' := by
    rw [Subfield.closure_le]
    rintro e (⟨c, rfl⟩ | he)
    · exact ⟨_, hconst c, rfl⟩
    · exact ⟨_, hgen e he, rfl⟩
  have hxE : (x : E) ∈ Subfield.closure (Set.range (algebraMap F E) ∪ S) := x.2
  obtain ⟨t, ht, htx⟩ := Subfield.mem_map.mp (hle hxE)
  have htx' : t = x := Subtype.ext htx
  exact htx' ▸ ht

private theorem exists_mul_eq_of_adjoin {F E : Type*} [Field F] [Field E] [Algebra F E]
    (S : Set E) {B : Type*} [CommRing B] (π : B →+* IntermediateField.adjoin F S)
    (hconst : ∀ c : F, algebraMap F (IntermediateField.adjoin F S) c ∈
      Subfield.closure (π.range : Set (IntermediateField.adjoin F S)))
    (hgen : ∀ (s : E) (hs : s ∈ S),
      (⟨s, IntermediateField.subset_adjoin F S hs⟩ : IntermediateField.adjoin F S) ∈
        Subfield.closure (π.range : Set (IntermediateField.adjoin F S))) :
    ∀ x : IntermediateField.adjoin F S, ∃ b c : B, π c ≠ 0 ∧ x * π c = π b :=
  exists_mul_eq_of_forall_mem_closure_range π (forall_mem_closure_range_of_adjoin S π hconst hgen)

private abbrev M (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    IntermediateField k (LaurentSeries k) := modularFunctionFieldC k N

private def Jel (k : Type*) [Field k] (N : ℕ) [NeZero N] : M k N :=
  ⟨jqModC k, jqModC_mem k N⟩

private def JNel (k : Type*) [Field k] (N : ℕ) [NeZero N] : M k N :=
  ⟨jqNModC k N, jqNModC_mem k N⟩

private def ψ (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    Polynomial (Polynomial k) →+* M k N :=
  eval₂RingHom (eval₂RingHom (algebraMap k (M k N)) (Jel k N)) (JNel k N)

variable {k : Type*} [Field k] (N : ℕ) [NeZero N]

@[scoped simp] private theorem ψ_CC (c : k) : ψ k N (CC c) = algebraMap k (M k N) c := by
  simp [ψ, CC]

@[scoped simp] private theorem ψ_C_X : ψ k N (C X) = Jel k N := by
  simp [ψ]

@[scoped simp] private theorem ψ_Y : ψ k N (Polynomial.X (R := Polynomial k)) = JNel k N := by
  simp [ψ]

private def lmap {K K' : Type*} [CommRing K] [CommRing K'] (f : K →+* K') :
    LaurentSeries K →+* LaurentSeries K' where
  toFun x := x.map f
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_mul' x y := HahnSeries.map_mul f.toNonUnitalRingHom
  map_zero' := by ext g; simp [HahnSeries.map_coeff]
  map_add' x y := by ext g; simp [HahnSeries.map_coeff]

private theorem lmap_apply {K K' : Type*} [CommRing K] [CommRing K'] (f : K →+* K')
    (x : LaurentSeries K) : lmap f x = x.map f := rfl

private theorem lmap_qExpand {K K' : Type*} [CommRing K] [CommRing K'] (f : K →+* K')
    (Nn : ℕ) [NeZero Nn] (x : LaurentSeries K) :
    lmap f (qExpand K Nn x) = qExpand K' Nn (lmap f x) := by
  ext g
  rw [lmap_apply, lmap_apply, HahnSeries.map_coeff]
  by_cases h : (Nn : ℤ) ∣ g
  · obtain ⟨m, rfl⟩ := h
    rw [qExpand_coeff_mul, qExpand_coeff_mul, HahnSeries.map_coeff]
  · rw [qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

private theorem lmap_jqNModC {K K' : Type*} [CommRing K] [CommRing K'] (f : K →+* K')
    (Nn : ℕ) [NeZero Nn] : lmap f (jqNModC K Nn) = jqNModC K' Nn := by
  rw [show jqNModC K Nn = qExpand K Nn (jqModC K) from rfl, lmap_qExpand,
    show lmap f (jqModC K) = jqModC K' from map_jqModC f]
  rfl

private theorem lmap_eval₂ {K K' : Type*} [CommRing K] [CommRing K'] (f : K →+* K')
    (Φ : Polynomial (Polynomial ℤ)) (u w : LaurentSeries K) :
    lmap f (Φ.eval₂ (Polynomial.aeval (R := ℤ) u).toRingHom w)
      = Φ.eval₂ (Polynomial.aeval (R := ℤ) (lmap f u)).toRingHom (lmap f w) := by
  rw [Polynomial.hom_eval₂]
  congr 1
  apply Polynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_intCast,
      eq_intCast]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.aeval_X]

private theorem eval₂_int_eq_zero (data : ModularPolynomialData N) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqModC ℤ)).toRingHom (jqNModC ℤ N) = 0 := by
  have hinj : Function.Injective (lmap (Int.castRingHom ℚ)) := by
    intro x y hxy
    ext g
    have h := congrArg (fun z : LaurentSeries ℚ => z.coeff g) hxy
    simp only [lmap_apply, HahnSeries.map_coeff] at h
    rw [eq_intCast, eq_intCast] at h
    exact_mod_cast h
  apply hinj
  rw [map_zero, lmap_eval₂,
    show lmap (Int.castRingHom ℚ) (jqModC ℤ) = jqModC ℚ from map_jqModC _,
    lmap_jqNModC,
    show (Polynomial.aeval (R := ℤ) (jqModC ℚ)).toRingHom = evalAtJ from by
      rw [jqModC_rat]; rfl,
    show jqNModC ℚ N = jqN N from rfl]
  exact data.eval_eq_zero

private theorem ψ_map_Φ (data : ModularPolynomialData N) :
    ψ k N (data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))) = 0 := by
  refine Subtype.ext ?_
  have hcoe : (((ψ k N (data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k)))) : M k N)
        : LaurentSeries k)
      = (data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).eval₂
          (eval₂RingHom (algebraMap k (LaurentSeries k)) (jqModC k)) (jqNModC k N) := by
    have key : (algebraMap (M k N) (LaurentSeries k)).comp (ψ k N)
        = eval₂RingHom (eval₂RingHom (algebraMap k (LaurentSeries k)) (jqModC k))
            (jqNModC k N) := by
      apply Polynomial.ringHom_ext
      · intro p
        have hin : ((algebraMap (M k N) (LaurentSeries k)).comp (ψ k N)).comp Polynomial.C
            = eval₂RingHom (algebraMap k (LaurentSeries k)) (jqModC k) := by
          apply Polynomial.ringHom_ext
          · intro c
            show algebraMap (M k N) (LaurentSeries k) (ψ k N (CC c)) = _
            rw [ψ_CC]
            simp only [coe_eval₂RingHom, Polynomial.eval₂_C]
            exact (IsScalarTower.algebraMap_apply k (M k N) (LaurentSeries k) c).symm
          · show algebraMap (M k N) (LaurentSeries k) (ψ k N (C X)) = _
            rw [ψ_C_X]
            simp only [coe_eval₂RingHom, Polynomial.eval₂_X]
            rfl
        show algebraMap (M k N) (LaurentSeries k) (ψ k N (C p)) = _
        have h2 : (eval₂RingHom (eval₂RingHom (algebraMap k (LaurentSeries k)) (jqModC k))
              (jqNModC k N)) (C p)
            = (eval₂RingHom (algebraMap k (LaurentSeries k)) (jqModC k)) p := by
          simp only [coe_eval₂RingHom, Polynomial.eval₂_C]
        rw [h2]
        exact DFunLike.congr_fun hin p
      · show algebraMap (M k N) (LaurentSeries k) (ψ k N (Polynomial.X (R := Polynomial k)))
            = _
        rw [ψ_Y]
        simp only [coe_eval₂RingHom, Polynomial.eval₂_X]
        rfl
    exact DFunLike.congr_fun key _
  rw [show ((0 : M k N) : LaurentSeries k) = 0 from rfl, hcoe, Polynomial.eval₂_map]
  have hcomp : (eval₂RingHom (algebraMap k (LaurentSeries k)) (jqModC k)).comp
      (Polynomial.mapRingHom (Int.castRingHom k))
      = (Polynomial.aeval (R := ℤ) (jqModC k)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
        coe_eval₂RingHom, Polynomial.eval₂_C, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        map_intCast, eq_intCast]
    · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
        coe_eval₂RingHom, Polynomial.eval₂_X, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Polynomial.aeval_X]
  rw [hcomp,
    show jqModC k = lmap (Int.castRingHom k) (jqModC ℤ) from (map_jqModC _).symm,
    show jqNModC k N = lmap (Int.castRingHom k) (jqNModC ℤ N) from (lmap_jqNModC _ N).symm,
    ← lmap_eval₂, eval₂_int_eq_zero, map_zero]

variable (v : Place k (M k N))

private theorem Jel_sub_mem (s : k)
    (hvj : 0 < v.ord (Jel k N - algebraMap k (M k N) s)) :
    Jel k N - algebraMap k (M k N) s ∈ v.toValuationSubring := by
  by_cases h : Jel k N - algebraMap k (M k N) s = 0
  · rw [h]; exact zero_mem _
  · exact v.mem_of_ord_nonneg h hvj.le

private theorem JNel_sub_mem (t : k)
    (hvjN : 0 < v.ord (JNel k N - algebraMap k (M k N) t)) :
    JNel k N - algebraMap k (M k N) t ∈ v.toValuationSubring := by
  by_cases h : JNel k N - algebraMap k (M k N) t = 0
  · rw [h]; exact zero_mem _
  · exact v.mem_of_ord_nonneg h hvjN.le

private theorem Jel_mem (s : k)
    (hvj : 0 < v.ord (Jel k N - algebraMap k (M k N) s)) :
    Jel k N ∈ v.toValuationSubring := by
  have h1 := Jel_sub_mem N v s hvj
  have h2 : algebraMap k (M k N) s ∈ v.toValuationSubring := v.algebraMap_mem' s
  simpa using add_mem h1 h2

private theorem JNel_mem (t : k)
    (hvjN : 0 < v.ord (JNel k N - algebraMap k (M k N) t)) :
    JNel k N ∈ v.toValuationSubring := by
  have h1 := JNel_sub_mem N v t hvjN
  have h2 : algebraMap k (M k N) t ∈ v.toValuationSubring := v.algebraMap_mem' t
  simpa using add_mem h1 h2

private def ψv (s t : k)
    (hvj : 0 < v.ord (Jel k N - algebraMap k (M k N) s))
    (hvjN : 0 < v.ord (JNel k N - algebraMap k (M k N) t)) :
    Polynomial (Polynomial k) →+* v.toValuationSubring :=
  eval₂RingHom (eval₂RingHom ((algebraMap k (M k N)).codRestrict _
      fun c => v.algebraMap_mem' c)
    ⟨Jel k N, Jel_mem N v s hvj⟩) ⟨JNel k N, JNel_mem N v t hvjN⟩

private theorem coe_ψv (s t : k)
    (hvj : 0 < v.ord (Jel k N - algebraMap k (M k N) s))
    (hvjN : 0 < v.ord (JNel k N - algebraMap k (M k N) t))
    (f : Polynomial (Polynomial k)) :
    (ψv N v s t hvj hvjN f : M k N) = ψ k N f := by
  suffices h : (v.toValuationSubring.subtype).comp (ψv N v s t hvj hvjN) = ψ k N from
    DFunLike.congr_fun h f
  have hinner : (v.toValuationSubring.subtype).comp
      (eval₂RingHom ((algebraMap k (M k N)).codRestrict _ fun c => v.algebraMap_mem' c)
        (⟨Jel k N, Jel_mem N v s hvj⟩ : v.toValuationSubring))
      = eval₂RingHom (algebraMap k (M k N)) (Jel k N) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C]
      rfl
    · simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X]
      rfl
  apply Polynomial.ringHom_ext
  · intro a
    simp only [ψv, ψ, RingHom.comp_apply, coe_eval₂RingHom, eval₂_C]
    exact DFunLike.congr_fun hinner a
  · simp only [ψv, ψ, RingHom.comp_apply, coe_eval₂RingHom, eval₂_X]
    rfl

@[scoped simp] private theorem ψv_CC (s t : k)
    (hvj : 0 < v.ord (Jel k N - algebraMap k (M k N) s))
    (hvjN : 0 < v.ord (JNel k N - algebraMap k (M k N) t)) (c : k) :
    ψv N v s t hvj hvjN (CC c)
      = (algebraMap k (M k N)).codRestrict _ (fun a => v.algebraMap_mem' a) c := by
  simp [ψv, CC]

set_option maxHeartbeats 4000000 in
@[scoped simp] private theorem ψv_C_X (s t : k)
    (hvj : 0 < v.ord (Jel k N - algebraMap k (M k N) s))
    (hvjN : 0 < v.ord (JNel k N - algebraMap k (M k N) t)) :
    ψv N v s t hvj hvjN (C X) = ⟨Jel k N, Jel_mem N v s hvj⟩ := by
  simp [ψv]

set_option maxHeartbeats 4000000 in
@[scoped simp] private theorem ψv_Y (s t : k)
    (hvj : 0 < v.ord (Jel k N - algebraMap k (M k N) s))
    (hvjN : 0 < v.ord (JNel k N - algebraMap k (M k N) t)) :
    ψv N v s t hvj hvjN (Polynomial.X (R := Polynomial k)) = ⟨JNel k N, JNel_mem N v t hvjN⟩ := by
  simp [ψv]

@[scoped simp] private theorem evalEval_CC' (s t c : k) : (CC c).evalEval s t = c := by
  simp [CC, Polynomial.evalEval]

@[scoped simp] private theorem evalEval_C_X' (s t : k) : (C X : Polynomial (Polynomial k)).evalEval s t = s := by
  simp [Polynomial.evalEval]

@[scoped simp] private theorem evalEval_Y' (s t : k) :
    (Polynomial.X (R := Polynomial k)).evalEval s t = t := by
  simp [Polynomial.evalEval]

private def ctr (s t : k)
    (hvj : 0 < v.ord (Jel k N - algebraMap k (M k N) s))
    (hvjN : 0 < v.ord (JNel k N - algebraMap k (M k N) t)) :
    Ideal v.toValuationSubring :=
  Ideal.span {⟨Jel k N - algebraMap k (M k N) s, Jel_sub_mem N v s hvj⟩,
    ⟨JNel k N - algebraMap k (M k N) t, JNel_sub_mem N v t hvjN⟩}

set_option maxHeartbeats 4000000 in

private theorem ψv_sub_const_mem (s t : k)
    (hvj : 0 < v.ord (Jel k N - algebraMap k (M k N) s))
    (hvjN : 0 < v.ord (JNel k N - algebraMap k (M k N) t))
    (f : Polynomial (Polynomial k)) :
    ψv N v s t hvj hvjN f
      - (algebraMap k (M k N)).codRestrict _ (fun c => v.algebraMap_mem' c) (f.evalEval s t)
      ∈ ctr N v s t hvj hvjN := by
  rw [← Ideal.Quotient.eq]
  have hgen1 : (Ideal.Quotient.mk (ctr N v s t hvj hvjN))
      ((⟨Jel k N, Jel_mem N v s hvj⟩ : v.toValuationSubring)
        - ⟨algebraMap k (M k N) s, v.algebraMap_mem' s⟩) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have hgen2 : (Ideal.Quotient.mk (ctr N v s t hvj hvjN))
      ((⟨JNel k N, JNel_mem N v t hvjN⟩ : v.toValuationSubring)
        - ⟨algebraMap k (M k N) t, v.algebraMap_mem' t⟩) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have key : (Ideal.Quotient.mk (ctr N v s t hvj hvjN)).comp (ψv N v s t hvj hvjN)
      = (Ideal.Quotient.mk (ctr N v s t hvj hvjN)).comp
        (((algebraMap k (M k N)).codRestrict _ (fun c => v.algebraMap_mem' c)).comp
          (evalEvalRingHom s t)) := by
    apply Polynomial.ringHom_ext
    · intro p
      have hin : ((Ideal.Quotient.mk (ctr N v s t hvj hvjN)).comp
            (ψv N v s t hvj hvjN)).comp Polynomial.C
          = ((Ideal.Quotient.mk (ctr N v s t hvj hvjN)).comp
              (((algebraMap k (M k N)).codRestrict _ (fun c => v.algebraMap_mem' c)).comp
                (evalEvalRingHom s t))).comp Polynomial.C := by
        apply Polynomial.ringHom_ext
        · intro c
          show (Ideal.Quotient.mk (ctr N v s t hvj hvjN)) (ψv N v s t hvj hvjN (CC c))
              = (Ideal.Quotient.mk (ctr N v s t hvj hvjN))
                ((algebraMap k (M k N)).codRestrict _ (fun a => v.algebraMap_mem' a)
                  ((CC c).evalEval s t))
          rw [ψv_CC, evalEval_CC']
        · show (Ideal.Quotient.mk (ctr N v s t hvj hvjN)) (ψv N v s t hvj hvjN (C X))
              = (Ideal.Quotient.mk (ctr N v s t hvj hvjN))
                ((algebraMap k (M k N)).codRestrict _ (fun a => v.algebraMap_mem' a)
                  ((C X : Polynomial (Polynomial k)).evalEval s t))
          rw [ψv_C_X, evalEval_C_X']
          rw [show (algebraMap k (M k N)).codRestrict v.toValuationSubring
                (fun a => v.algebraMap_mem' a) s
              = ⟨algebraMap k (M k N) s, v.algebraMap_mem' s⟩ from rfl]
          rw [← sub_eq_zero, ← RingHom.map_sub]
          exact hgen1
      exact DFunLike.congr_fun hin p
    · show (Ideal.Quotient.mk (ctr N v s t hvj hvjN))
            (ψv N v s t hvj hvjN (Polynomial.X (R := Polynomial k)))
          = (Ideal.Quotient.mk (ctr N v s t hvj hvjN))
            ((algebraMap k (M k N)).codRestrict _ (fun a => v.algebraMap_mem' a)
              ((Polynomial.X (R := Polynomial k)).evalEval s t))
      rw [ψv_Y, evalEval_Y']
      rw [show (algebraMap k (M k N)).codRestrict v.toValuationSubring
            (fun a => v.algebraMap_mem' a) t
          = ⟨algebraMap k (M k N) t, v.algebraMap_mem' t⟩ from rfl]
      rw [← sub_eq_zero, ← RingHom.map_sub]
      exact hgen2
  exact DFunLike.congr_fun key f

private theorem ctr_le_maximalIdeal (s t : k)
    (hvj : 0 < v.ord (Jel k N - algebraMap k (M k N) s))
    (hvjN : 0 < v.ord (JNel k N - algebraMap k (M k N) t)) :
    ctr N v s t hvj hvjN ≤ IsLocalRing.maximalIdeal v.toValuationSubring := by
  rw [ctr, Ideal.span_le]
  rintro x (rfl | rfl)
  · rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have h0 := v.ord_coe_unit u
    rw [hu] at h0
    exact hvj.ne' h0
  · rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have h0 := v.ord_coe_unit u
    rw [hu] at h0
    exact hvjN.ne' h0

private theorem isUnit_ψv_of_evalEval_ne_zero (s t : k)
    (hvj : 0 < v.ord (Jel k N - algebraMap k (M k N) s))
    (hvjN : 0 < v.ord (JNel k N - algebraMap k (M k N) t))
    {f : Polynomial (Polynomial k)} (hf : f.evalEval s t ≠ 0) :
    IsUnit (ψv N v s t hvj hvjN f) := by
  set c := f.evalEval s t with hc
  have hu : IsUnit ((algebraMap k (M k N)).codRestrict _
      (fun a => v.algebraMap_mem' a) c) := by
    refine isUnit_iff_exists_inv.mpr ⟨(algebraMap k (M k N)).codRestrict _
      (fun a => v.algebraMap_mem' a) c⁻¹, ?_⟩
    rw [← map_mul, mul_inv_cancel₀ hf, map_one]
  by_contra hnu
  have h1 : ψv N v s t hvj hvjN f ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
    (IsLocalRing.mem_maximalIdeal _).mpr hnu
  have h2 : ψv N v s t hvj hvjN f - (algebraMap k (M k N)).codRestrict _
      (fun a => v.algebraMap_mem' a) c ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
    ctr_le_maximalIdeal N v s t hvj hvjN (ψv_sub_const_mem N v s t hvj hvjN f)
  have h3 : (algebraMap k (M k N)).codRestrict _
      (fun a => v.algebraMap_mem' a) c ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    have := Ideal.sub_mem _ h1 h2
    simpa using this
  exact (IsLocalRing.mem_maximalIdeal _).mp h3 hu

private theorem ord_pos_of_mem_ctr (s t : k)
    (hvj : 0 < v.ord (Jel k N - algebraMap k (M k N) s))
    (hvjN : 0 < v.ord (JNel k N - algebraMap k (M k N) t))
    {x : v.toValuationSubring} (hx : x ∈ ctr N v s t hvj hvjN) (hx0 : (x : M k N) ≠ 0) :
    0 < v.ord (x : M k N) := by
  have hmax := ctr_le_maximalIdeal N v s t hvj hvjN hx
  have hnn := v.ord_nonneg_of_mem x.2
  rcases hnn.lt_or_eq with h | h
  · exact h
  · exfalso
    have hinv : (x : M k N)⁻¹ ∈ v.toValuationSubring :=
      v.mem_of_ord_nonneg (inv_ne_zero hx0) (by rw [v.ord_inv]; omega)
    have hux : IsUnit x := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨(x : M k N)⁻¹, hinv⟩, ?_⟩
      exact Subtype.ext (by simpa using mul_inv_cancel₀ hx0)
    exact (IsLocalRing.mem_maximalIdeal _).mp hmax hux

private theorem ord_algebraMap_eq_zero (c : k) :
    v.ord (algebraMap k (M k N) c) = 0 := by
  have h1 := v.ord_nonneg_of_mem (v.algebraMap_mem' c)
  have h2 := v.ord_nonneg_of_mem (v.algebraMap_mem' c⁻¹)
  rw [map_inv₀, v.ord_inv] at h2
  omega

private theorem ord_ψ_eq_zero_of_evalEval_ne_zero (s t : k)
    (hvj : 0 < v.ord (Jel k N - algebraMap k (M k N) s))
    (hvjN : 0 < v.ord (JNel k N - algebraMap k (M k N) t))
    {f : Polynomial (Polynomial k)} (hf : f.evalEval s t ≠ 0) :
    v.ord (ψ k N f) = 0 := by
  obtain ⟨u, hu⟩ := isUnit_ψv_of_evalEval_ne_zero N v s t hvj hvjN hf
  have h0 := v.ord_coe_unit u
  rw [← coe_ψv N v s t hvj hvjN f, ← hu]
  exact h0

private theorem evalEval_eq_zero_of_ψ_eq_zero (s t : k)
    (hvj : 0 < v.ord (Jel k N - algebraMap k (M k N) s))
    (hvjN : 0 < v.ord (JNel k N - algebraMap k (M k N) t))
    {f : Polynomial (Polynomial k)} (hf : ψ k N f = 0) :
    f.evalEval s t = 0 := by
  by_contra hne
  have hu := isUnit_ψv_of_evalEval_ne_zero N v s t hvj hvjN hne
  refine hu.ne_zero (Subtype.ext ?_)
  rw [coe_ψv N v s t hvj hvjN f, hf]
  rfl

private theorem ord_ψ_nonneg (s t : k)
    (hvj : 0 < v.ord (Jel k N - algebraMap k (M k N) s))
    (hvjN : 0 < v.ord (JNel k N - algebraMap k (M k N) t))
    (f : Polynomial (Polynomial k)) :
    0 ≤ v.ord (ψ k N f) := by
  rw [← coe_ψv N v s t hvj hvjN f]
  exact v.ord_nonneg_of_mem (ψv N v s t hvj hvjN f).2

private abbrev Phib (k : Type*) [Field k] {N : ℕ} [NeZero N]
    (data : ModularPolynomialData N) : Polynomial (Polynomial k) :=
  data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))

private lemma ker_evalEvalRingHom {k : Type*} [Field k] (a b : k) :
    RingHom.ker (evalEvalRingHom a b) =
      Ideal.span {(C (X - C a) : k[X][Y]), Y - CC b} := by
  refine le_antisymm (fun f hf => ?_) (Ideal.span_le.mpr ?_)
  · rw [RingHom.mem_ker] at hf
    have hmod : f %ₘ (Y - CC b) = C (f.eval (C b)) := modByMonic_X_sub_C_eq_C_eval f (C b)
    have hr : (f.eval (C b)).eval a = 0 := hf
    obtain ⟨s, hs⟩ : (X - C a) ∣ f.eval (C b) := dvd_iff_isRoot.mpr hr
    have hsplit : f = C (X - C a) * C s + (Y - CC b) * (f /ₘ (Y - CC b)) := by
      conv_lhs => rw [← modByMonic_add_div f (Y - CC b)]
      rw [hmod, hs, map_mul]
    rw [hsplit]
    exact Ideal.add_mem _
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _)))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
  · rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · simp [RingHom.mem_ker]
    · simp [RingHom.mem_ker]

private theorem isMaximal_span_residue {k : Type*} [Field k] (P : k[X][Y]) (a b : k)
    (hroot : P.evalEval a b = 0) :
    (Ideal.span {Ideal.Quotient.mk (Ideal.span {P}) (C (X - C a)),
        Ideal.Quotient.mk (Ideal.span {P}) (Y - CC b)}).IsMaximal := by
  set J : Ideal k[X][Y] := Ideal.span {C (X - C a), Y - CC b} with hJdef
  have hker : RingHom.ker (evalEvalRingHom a b) = J := ker_evalEvalRingHom a b
  have hJmax : J.IsMaximal := by
    rw [← hker]
    exact RingHom.ker_isMaximal_of_surjective (evalEvalRingHom a b)
      (fun c => ⟨CC c, by simp⟩)
  have hPJ : Ideal.span {P} ≤ J := by
    rw [Ideal.span_le, Set.singleton_subset_iff, ← hker]
    exact hroot
  have hmap : Ideal.span {Ideal.Quotient.mk (Ideal.span {P}) (C (X - C a)),
      Ideal.Quotient.mk (Ideal.span {P}) (Y - CC b)} =
      J.map (Ideal.Quotient.mk (Ideal.span {P})) := by
    rw [hJdef, Ideal.map_span, Set.image_pair]
  rw [hmap]
  have hkle : RingHom.ker (Ideal.Quotient.mk (Ideal.span {P})) ≤ J := by
    rw [Ideal.mk_ker]; exact hPJ
  exact Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hkle

private theorem mk_mem_pt_iff {k : Type*} [Field k] (P : k[X][Y]) (s t : k)
    (hroot : P.evalEval s t = 0) (y : k[X][Y]) :
    Ideal.Quotient.mk (Ideal.span {P}) y ∈
        Ideal.span {Ideal.Quotient.mk (Ideal.span {P}) (C (X - C s)),
          Ideal.Quotient.mk (Ideal.span {P}) (Y - CC t)}
      ↔ y.evalEval s t = 0 := by
  set J : Ideal k[X][Y] := Ideal.span {C (X - C s), Y - CC t} with hJdef
  have hker : RingHom.ker (evalEvalRingHom s t) = J := ker_evalEvalRingHom s t
  have hPJ : Ideal.span {P} ≤ J := by
    rw [Ideal.span_le, Set.singleton_subset_iff, ← hker]
    exact hroot
  have hmap : Ideal.span {Ideal.Quotient.mk (Ideal.span {P}) (C (X - C s)),
      Ideal.Quotient.mk (Ideal.span {P}) (Y - CC t)} =
      J.map (Ideal.Quotient.mk (Ideal.span {P})) := by
    rw [hJdef, Ideal.map_span, Set.image_pair]
  rw [hmap]
  constructor
  · intro hy
    obtain ⟨z, hzJ, hzy⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hy
    have hsub : z - y ∈ Ideal.span {P} := Ideal.Quotient.eq.mp hzy
    have hyJ : y ∈ J := by
      have : y = z - (z - y) := by ring
      rw [this]
      exact J.sub_mem hzJ (hPJ hsub)
    rw [← hker] at hyJ
    exact hyJ
  · intro hy
    refine Ideal.mem_map_of_mem _ ?_
    rw [← hker]
    exact hy

private def psibar (k : Type*) [Field k] (N : ℕ) [NeZero N] (data : ModularPolynomialData N) :
    (k[X][Y] ⧸ Ideal.span {Phib k data}) →+* M k N :=
  Ideal.Quotient.lift (Ideal.span {Phib k data}) (ψ k N) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [map_mul, show ψ k N (Phib k data) = 0 from ψ_map_Φ N data, zero_mul])

@[scoped simp] private theorem psibar_mk {k : Type*} [Field k] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) (f : k[X][Y]) :
    psibar k N data (Ideal.Quotient.mk (Ideal.span {Phib k data}) f) = ψ k N f := rfl

set_option maxSynthPendingDepth 3 in

private noncomputable def rho {k : Type*} [Field k] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) (s t : k)
    [hm : (Ideal.span {Ideal.Quotient.mk (Ideal.span {Phib k data}) (C (X - C s)),
        Ideal.Quotient.mk (Ideal.span {Phib k data}) (Y - CC t)}).IsMaximal]
    (hroot : (Phib k data).evalEval s t = 0)
    (hker : ∀ f : k[X][Y], ψ k N f = 0 → f.evalEval s t = 0) :
    Localization.AtPrime (Ideal.span
      {Ideal.Quotient.mk (Ideal.span {Phib k data}) (C (X - C s)),
       Ideal.Quotient.mk (Ideal.span {Phib k data}) (Y - CC t)}) →+* M k N :=
  IsLocalization.lift
    (M := (Ideal.span {Ideal.Quotient.mk (Ideal.span {Phib k data}) (C (X - C s)),
        Ideal.Quotient.mk (Ideal.span {Phib k data}) (Y - CC t)}).primeCompl)
    (g := psibar k N data) (fun u => by
    obtain ⟨u, hu⟩ := u
    obtain ⟨u', rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {Phib k data}) u
    show IsUnit (psibar k N data (Ideal.Quotient.mk (Ideal.span {Phib k data}) u'))
    rw [psibar_mk, isUnit_iff_ne_zero]
    intro h0
    have hmem : Ideal.Quotient.mk (Ideal.span {Phib k data}) u' ∈ Ideal.span
        {Ideal.Quotient.mk (Ideal.span {Phib k data}) (C (X - C s)),
         Ideal.Quotient.mk (Ideal.span {Phib k data}) (Y - CC t)} :=
      (mk_mem_pt_iff (Phib k data) s t hroot u').mpr (hker u' h0)
    exact hu hmem)

set_option maxSynthPendingDepth 3 in
private theorem rho_algebraMap {k : Type*} [Field k] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) (s t : k)
    [hm : (Ideal.span {Ideal.Quotient.mk (Ideal.span {Phib k data}) (C (X - C s)),
        Ideal.Quotient.mk (Ideal.span {Phib k data}) (Y - CC t)}).IsMaximal]
    (hroot : (Phib k data).evalEval s t = 0)
    (hker : ∀ f : k[X][Y], ψ k N f = 0 → f.evalEval s t = 0) (f : k[X][Y]) :
    rho N data s t hroot hker ((algebraMap (k[X][Y] ⧸ Ideal.span {Phib k data})
        (Localization.AtPrime (Ideal.span
          {Ideal.Quotient.mk (Ideal.span {Phib k data}) (C (X - C s)),
           Ideal.Quotient.mk (Ideal.span {Phib k data}) (Y - CC t)})))
      (Ideal.Quotient.mk (Ideal.span {Phib k data}) f))
      = ψ k N f := by
  unfold rho
  rw [IsLocalization.lift_eq]
  exact psibar_mk N data f

set_option maxHeartbeats 16000000 in
set_option maxSynthPendingDepth 3 in

theorem ord_eq_one {k : Type*} [Field k] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) (s t : k)
    (hder : (Polynomial.derivative (Phib k data)).evalEval s t ≠ 0)
    (P : Place k (M k N))
    (hPj : 0 < P.ord (Jel k N - algebraMap k (M k N) s))
    (hPjN : 0 < P.ord (JNel k N - algebraMap k (M k N) t)) :
    P.ord (Jel k N - algebraMap k (M k N) s) = 1 := by
  classical
  have hroot : (Phib k data).evalEval s t = 0 :=
    evalEval_eq_zero_of_ψ_eq_zero N P s t hPj hPjN (ψ_map_Φ N data)
  have hker : ∀ f : k[X][Y], ψ k N f = 0 → f.evalEval s t = 0 :=
    fun f hf => evalEval_eq_zero_of_ψ_eq_zero N P s t hPj hPjN hf
  haveI hmax : (Ideal.span {Ideal.Quotient.mk (Ideal.span {Phib k data}) (C (X - C s)),
      Ideal.Quotient.mk (Ideal.span {Phib k data}) (Y - CC t)}).IsMaximal :=
    isMaximal_span_residue (Phib k data) s t hroot
  obtain ⟨hdom, hdvr, hgen⟩ :=
    OrdOneFO.isDVR_and_maximalIdeal_eq_span (Phib k data) (data.monic.map _) s t hder
  haveI := hdom
  haveI := hdvr
  haveI : IsBezout (Localization.AtPrime (Ideal.span
      {Ideal.Quotient.mk (Ideal.span {Phib k data}) (C (X - C s)),
       Ideal.Quotient.mk (Ideal.span {Phib k data}) (Y - CC t)})) :=
    (IsBezout.iff_span_pair_isPrincipal (R := Localization.AtPrime (Ideal.span
      {Ideal.Quotient.mk (Ideal.span {Phib k data}) (C (X - C s)),
       Ideal.Quotient.mk (Ideal.span {Phib k data}) (Y - CC t)}))).mpr
      fun _ _ => IsPrincipalIdealRing.principal _

  have hrange : ∀ (W : Place k (M k N)),
      0 < W.ord (Jel k N - algebraMap k (M k N) s) →
      0 < W.ord (JNel k N - algebraMap k (M k N) t) →
      ∀ x : M k N, x ∈ W.toValuationSubring ↔ x ∈ (rho N data s t hroot hker).range := by
    intro W hWj hWjN x

    have havatar : ∀ (y : M k N) (z' u' : k[X][Y]), u'.evalEval s t ≠ 0 →
        y * ψ k N u' = ψ k N z' →
        y ∈ W.toValuationSubring ∧ (z'.evalEval s t = 0 → y ≠ 0 → 0 < W.ord y) := by
      intro y z' u' hut hyspec
      have hψu0 : ψ k N u' ≠ 0 :=
        fun h => hut (evalEval_eq_zero_of_ψ_eq_zero N W s t hWj hWjN h)
      have hu0 : W.ord (ψ k N u') = 0 :=
        ord_ψ_eq_zero_of_evalEval_ne_zero N W s t hWj hWjN hut
      rcases eq_or_ne y 0 with rfl | hy0
      · exact ⟨zero_mem _, fun _ h => absurd rfl h⟩
      · have hz0 : ψ k N z' ≠ 0 := hyspec ▸ mul_ne_zero hy0 hψu0
        have hordy : W.ord y = W.ord (ψ k N z') := by
          have h := W.ord_mul hy0 hψu0
          rw [hyspec, hu0, add_zero] at h
          exact h.symm
        have hzmem : ψ k N z' ∈ W.toValuationSubring := by
          rw [← coe_ψv N W s t hWj hWjN z']
          exact (ψv N W s t hWj hWjN z').2
        refine ⟨W.mem_of_ord_nonneg hy0 ?_, fun hzt hy0' => ?_⟩
        · rw [hordy]
          exact W.ord_nonneg_of_mem hzmem
        · have hctrz : ψv N W s t hWj hWjN z' ∈ ctr N W s t hWj hWjN := by
            have h := ψv_sub_const_mem N W s t hWj hWjN z'
            rw [hzt, map_zero, sub_zero] at h
            exact h
          have hcz : ((ψv N W s t hWj hWjN z' : W.toValuationSubring) : M k N) ≠ 0 := by
            rw [coe_ψv]; exact hz0
          have hpos := ord_pos_of_mem_ctr N W s t hWj hWjN hctrz hcz
          rw [coe_ψv N W s t hWj hWjN z'] at hpos
          rw [hordy]
          exact hpos

    have hspec : ∀ r : Localization.AtPrime (Ideal.span
        {Ideal.Quotient.mk (Ideal.span {Phib k data}) (C (X - C s)),
         Ideal.Quotient.mk (Ideal.span {Phib k data}) (Y - CC t)}),
        ∃ z' u' : k[X][Y], u'.evalEval s t ≠ 0 ∧
          rho N data s t hroot hker r * ψ k N u' = ψ k N z' ∧
          (¬IsUnit r → z'.evalEval s t = 0) := by
      intro r
      obtain ⟨⟨z, u⟩, rfl⟩ := IsLocalization.mk'_surjective (Ideal.span
        {Ideal.Quotient.mk (Ideal.span {Phib k data}) (C (X - C s)),
         Ideal.Quotient.mk (Ideal.span {Phib k data}) (Y - CC t)}).primeCompl r
      obtain ⟨z', rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {Phib k data}) z
      obtain ⟨u', hu'⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {Phib k data}) (u : _)
      have hut : u'.evalEval s t ≠ 0 := by
        intro h0
        exact u.2 (hu' ▸ (mk_mem_pt_iff (Phib k data) s t hroot u').mpr h0)
      refine ⟨z', u', hut, ?_, ?_⟩
      · have h0 := congrArg (rho N data s t hroot hker)
          (IsLocalization.mk'_spec (Localization.AtPrime (Ideal.span
            {Ideal.Quotient.mk (Ideal.span {Phib k data}) (C (X - C s)),
             Ideal.Quotient.mk (Ideal.span {Phib k data}) (Y - CC t)}))
            (Ideal.Quotient.mk (Ideal.span {Phib k data}) z') u)
        rw [map_mul] at h0
        rw [show ((algebraMap (k[X][Y] ⧸ Ideal.span {Phib k data})
              (Localization.AtPrime (Ideal.span
            {Ideal.Quotient.mk (Ideal.span {Phib k data}) (C (X - C s)),
             Ideal.Quotient.mk (Ideal.span {Phib k data}) (Y - CC t)})))
              ((u : k[X][Y] ⧸ Ideal.span {Phib k data}))) =
            (algebraMap (k[X][Y] ⧸ Ideal.span {Phib k data})
              (Localization.AtPrime (Ideal.span
            {Ideal.Quotient.mk (Ideal.span {Phib k data}) (C (X - C s)),
             Ideal.Quotient.mk (Ideal.span {Phib k data}) (Y - CC t)})))
              (Ideal.Quotient.mk (Ideal.span {Phib k data}) u') from by rw [hu'],
          rho_algebraMap, rho_algebraMap] at h0
        exact h0
      · intro hnu
        have hz : Ideal.Quotient.mk (Ideal.span {Phib k data}) z' ∈ Ideal.span
            {Ideal.Quotient.mk (Ideal.span {Phib k data}) (C (X - C s)),
             Ideal.Quotient.mk (Ideal.span {Phib k data}) (Y - CC t)} := by
          by_contra hzc
          exact hnu ((IsLocalization.AtPrime.isUnit_mk'_iff _ _ _ u).mpr hzc)
        exact (mk_mem_pt_iff (Phib k data) s t hroot z').mp hz
    constructor
    · intro hx

      obtain ⟨b, c, hc0, hbc⟩ := exists_mul_eq_of_adjoin (F := k) (E := LaurentSeries k)
        ({jqModC k, jqNModC k N} : Set (LaurentSeries k)) (ψ k N)
        (fun c => Subfield.subset_closure ⟨CC c, ψ_CC N c⟩)
        (by
          rintro s' (rfl | rfl)
          · exact Subfield.subset_closure ⟨C X, ψ_C_X N⟩
          · exact Subfield.subset_closure ⟨Polynomial.X (R := Polynomial k), ψ_Y N⟩)
        x

      have hbc' : x * ψ k N c = ψ k N b := hbc
      have hc0' : ψ k N c ≠ 0 := hc0

      obtain ⟨r, hr | hr⟩ := ValuationRing.cond
        (algebraMap _ (Localization.AtPrime (Ideal.span
          {Ideal.Quotient.mk (Ideal.span {Phib k data}) (C (X - C s)),
           Ideal.Quotient.mk (Ideal.span {Phib k data}) (Y - CC t)}))
          (Ideal.Quotient.mk (Ideal.span {Phib k data}) b))
        (algebraMap _ (Localization.AtPrime (Ideal.span
          {Ideal.Quotient.mk (Ideal.span {Phib k data}) (C (X - C s)),
           Ideal.Quotient.mk (Ideal.span {Phib k data}) (Y - CC t)}))
          (Ideal.Quotient.mk (Ideal.span {Phib k data}) c))
      ·
        have hρr : ψ k N b * rho N data s t hroot hker r = ψ k N c := by
          have h0 := congrArg (rho N data s t hroot hker) hr
          rwa [map_mul, rho_algebraMap, rho_algebraMap] at h0
        by_cases hψb : ψ k N b = 0
        · have hx0 : x = 0 := by
            have h0 : x * ψ k N c = 0 := by rw [hbc', hψb]
            exact (mul_eq_zero.mp h0).resolve_right hc0'
          exact hx0 ▸ ⟨0, map_zero _⟩
        · have hxρ : x * rho N data s t hroot hker r = 1 := by
            have h1 : x * (ψ k N b * rho N data s t hroot hker r) = ψ k N b := by
              rw [hρr]; exact hbc'
            have h2 : ψ k N b * (x * rho N data s t hroot hker r) = ψ k N b * 1 := by
              rw [mul_one, show ψ k N b * (x * rho N data s t hroot hker r)
                = x * (ψ k N b * rho N data s t hroot hker r) from by ring]
              exact h1
            exact mul_left_cancel₀ hψb h2
          by_cases hur : IsUnit r
          · obtain ⟨ru, hru⟩ := hur
            refine ⟨↑ru⁻¹, ?_⟩
            have hρr0 : rho N data s t hroot hker r ≠ 0 := by
              intro h
              rw [h, mul_zero] at hxρ
              exact one_ne_zero hxρ.symm
            have hy : rho N data s t hroot hker ↑ru⁻¹
                * rho N data s t hroot hker r = 1 := by
              rw [← map_mul, ← hru, Units.inv_mul, map_one]
            exact mul_right_cancel₀ hρr0 (hy.trans hxρ.symm)
          ·
            exfalso
            obtain ⟨z', u', hut, hsp, hcond⟩ := hspec r
            obtain ⟨hymem, hypos⟩ := havatar _ _ _ hut hsp
            have hy0 : rho N data s t hroot hker r ≠ 0 := by
              intro h
              rw [h, mul_zero] at hxρ
              exact one_ne_zero hxρ.symm
            have hpos := hypos (hcond hur) hy0
            have hunit : IsUnit (⟨rho N data s t hroot hker r, hymem⟩ : W.toValuationSubring) := by
              refine IsUnit.of_mul_eq_one ⟨x, hx⟩ (Subtype.ext ?_)
              rw [MulMemClass.coe_mul]
              show rho N data s t hroot hker r * x = 1
              rw [mul_comm]
              exact hxρ
            obtain ⟨yu, hyu⟩ := hunit
            have h0 := W.ord_coe_unit yu
            rw [hyu] at h0
            have h0' : W.ord (rho N data s t hroot hker r) = 0 := h0
            omega
      ·
        have hρr : ψ k N c * rho N data s t hroot hker r = ψ k N b := by
          have h0 := congrArg (rho N data s t hroot hker) hr
          rwa [map_mul, rho_algebraMap, rho_algebraMap] at h0
        refine ⟨r, ?_⟩
        have h1 : ψ k N c * rho N data s t hroot hker r = ψ k N c * x := by
          rw [hρr, ← hbc']; ring
        exact mul_left_cancel₀ hc0' h1
    · rintro ⟨r, rfl⟩
      obtain ⟨z', u', hut, hsp, -⟩ := hspec r
      exact (havatar _ _ _ hut hsp).1

  have hj0 : Jel k N - algebraMap k (M k N) s ≠ 0 := by
    intro h
    rw [h, P.ord_zero] at hPj
    exact lt_irrefl _ hPj
  have hρg : rho N data s t hroot hker (algebraMap (k[X][Y] ⧸ Ideal.span {Phib k data}) (Localization.AtPrime (Ideal.span
      {Ideal.Quotient.mk (Ideal.span {Phib k data}) (C (X - C s)),
       Ideal.Quotient.mk (Ideal.span {Phib k data}) (Y - CC t)}))
      (Ideal.Quotient.mk (Ideal.span {Phib k data}) (C (X - C s))))
      = Jel k N - algebraMap k (M k N) s := by
    rw [rho_algebraMap]
    show ψ k N (C (X - C s)) = _
    rw [map_sub, map_sub, ψ_C_X]
    congr 1
    exact ψ_CC N s
  have hle : ∀ x : M k N, x ∈ P.toValuationSubring → x ≠ 0 → 0 < P.ord x →
      P.ord (Jel k N - algebraMap k (M k N) s) ≤ P.ord x := by
    intro x hx hx0 hxpos
    obtain ⟨r, hr⟩ := (hrange P hPj hPjN x).mp hx

    have hru : ¬ IsUnit r := by
      rintro ⟨u, rfl⟩
      have hinv : rho N data s t hroot hker ↑u⁻¹ ∈ P.toValuationSubring :=
        (hrange P hPj hPjN _).mpr ⟨_, rfl⟩
      have h1 : x * rho N data s t hroot hker ↑u⁻¹ = 1 := by
        rw [← hr, ← map_mul, Units.mul_inv, map_one]
      have hne : rho N data s t hroot hker ↑u⁻¹ ≠ 0 := by
        intro h
        rw [h, mul_zero] at h1
        exact zero_ne_one h1
      have hsum := P.ord_mul hx0 hne
      rw [h1, P.ord_one] at hsum
      have hnn := P.ord_nonneg_of_mem hinv
      omega
    have hrm : r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span
      {Ideal.Quotient.mk (Ideal.span {Phib k data}) (C (X - C s)),
       Ideal.Quotient.mk (Ideal.span {Phib k data}) (Y - CC t)})) :=
      (IsLocalRing.mem_maximalIdeal r).mpr (mem_nonunits_iff.mpr hru)
    rw [hgen, Ideal.mem_span_singleton'] at hrm
    obtain ⟨r', rfl⟩ := hrm
    rw [map_mul, hρg] at hr

    have hr'mem : rho N data s t hroot hker r' ∈ P.toValuationSubring := (hrange P hPj hPjN _).mpr ⟨_, rfl⟩
    have hr'0 : rho N data s t hroot hker r' ≠ 0 := by
      intro h
      apply hx0
      rw [← hr, h, zero_mul]
    rw [← hr, P.ord_mul hr'0 hj0]
    have hnn := P.ord_nonneg_of_mem hr'mem
    omega

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible P.toValuationSubring
  have hπ1 : P.ord (π : M k N) = 1 := P.ord_coe_irreducible hπ
  have hπ0 : (π : M k N) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hle1 := hle (π : M k N) π.2 hπ0 (by rw [hπ1]; exact one_pos)
  omega

end DE
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_ord_sub_eq_one_of_derivative_evalEval_ne_zero.OrdOneHelper.DE"
end OrdOneHelper
p2m_reactivate "P2MW.S_ModularCurve_CharPModel_ord_sub_eq_one_of_derivative_evalEval_ne_zero.OrdOneHelper.DE P2MW.S_ModularCurve_CharPModel_ord_sub_eq_one_of_derivative_evalEval_ne_zero.OrdOneHelper"

set_option maxSynthPendingDepth 3 in
theorem solution
    {k : Type*} [Field k] (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
    (s t : k)
    (hder : (Polynomial.derivative
        (data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k)))).evalEval s t ≠ 0)
    (P : Place k (modularFunctionFieldC k N))
    (hPj : 0 < P.ord (⟨jqModC k, jqModC_mem k N⟩
      - algebraMap k (modularFunctionFieldC k N) s))
    (hPjN : 0 < P.ord (⟨jqNModC k N, jqNModC_mem k N⟩
      - algebraMap k (modularFunctionFieldC k N) t)) :
    P.ord (⟨jqModC k, jqModC_mem k N⟩ - algebraMap k (modularFunctionFieldC k N) s) = 1 :=
  OrdOneHelper.DE.ord_eq_one N data s t hder P hPj hPjN

end
end S_ModularCurve_CharPModel_ord_sub_eq_one_of_derivative_evalEval_ne_zero
end P2MW
export P2MW.S_ModularCurve_CharPModel_ord_sub_eq_one_of_derivative_evalEval_ne_zero (solution)
