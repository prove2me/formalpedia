-- Prove2me | solution 1 for OAI.Erdos970.WeightedTorusJets.Geometry.DegreeBezout.linear_normalization_weighted_local_length_le_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:49:02.91508+00:00
-- url     : https://prove2.me/submissions/e4ad6d7b-acee-4035-82cd-64ee8ee17f8e

import Mathlib
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.Basic
import Definitions.Def_OAIQ247J007

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_MonicSMulRegularQuotientMapC
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.finite_rectangularQuotient _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section

open _root_.Polynomial

namespace WeightedTorusJets

theorem monic_isSMulRegular_quotient_map_C {A : Type*} [CommRing A]
    (I : Ideal A) {y : A[X]} (hy : y.Monic) :
    IsSMulRegular (A[X] ⧸ I.map (Polynomial.C : A →+* A[X])) y := by
  let e := I.polynomialQuotientEquivQuotientPolynomial.symm
  apply (e.toEquiv.isSMulRegular_congr (r := y)
    (s := y.map (Ideal.Quotient.mk I)) ?_).mpr
  · exact (hy.map (Ideal.Quotient.mk I)).isRegular.left
  · intro z
    change e (Ideal.Quotient.mk _ y * z) = y.map (Ideal.Quotient.mk I) * e z
    rw [map_mul]
    congr 1



open Ideal IsLocalRing _root_.Polynomial RingTheory.Sequence

theorem exists_regular_generators_polynomial_localization
    {A : Type*} [CommRing A] [IsLocalRing A]
    (rs : List A) (hreg : IsRegular A rs) (hgen : Ideal.ofList rs = maximalIdeal A)
    (p : Ideal A[X]) [p.IsPrime] (hclosed : p.comap Polynomial.C = maximalIdeal A) :
    ∃ ss : List (Localization.AtPrime p),
      IsRegular (Localization.AtPrime p) ss ∧
        Ideal.ofList ss = maximalIdeal (Localization.AtPrime p) := by
  let S := Localization.AtPrime p
  let rsC := rs.map (Polynomial.C : A →+* A[X])
  let q := (maximalIdeal A).map (Polynomial.C : A →+* A[X])
  have hweak : IsWeaklyRegular A[X] rsC := by
    simpa only [Polynomial.algebraMap_eq] using
      hreg.toIsWeaklyRegular.of_flat (S := A[X])
  have hgenC : Ideal.ofList rsC = q := by
    rw [show rsC = rs.map (Polynomial.C : A →+* A[X]) from rfl,
      ← Ideal.map_ofList, hgen]
  have hqle : q ≤ p := by
    simpa only [q, ← hclosed] using (Ideal.map_comap_le : (p.comap C).map C ≤ p)
  by_cases hpq : p = q
  · refine ⟨rsC.map (algebraMap A[X] S),
      hweak.isRegular_of_isLocalization_of_mem S p (fun r hr => ?_), ?_⟩
    · apply hqle
      rw [← hgenC]
      exact Ideal.subset_span hr
    · rw [← Ideal.map_ofList, hgenC, ← hpq, Localization.AtPrime.map_eq_maximalIdeal]
  · have hm : (p.comap C).IsMaximal := by
      rw [hclosed]
      infer_instance
    obtain ⟨y, hy, hpy⟩ := Polynomial.exists_monic_span_sup_map_eq A p hm
      (by simpa only [hclosed] using hpq)
    have hgens : Ideal.ofList (rsC ++ [y]) = p := by
      rw [Ideal.ofList_append, Ideal.ofList_singleton, hgenC]
      simpa only [q, hclosed] using hpy.symm
    have hweak' : IsWeaklyRegular A[X] (rsC ++ [y]) := by
      rw [isWeaklyRegular_append_iff, isWeaklyRegular_singleton_iff]
      refine ⟨hweak, ?_⟩
      rw [Ideal.smul_eq_mul, Ideal.mul_top, hgenC]
      exact monic_isSMulRegular_quotient_map_C (maximalIdeal A) hy
    refine ⟨(rsC ++ [y]).map (algebraMap A[X] S),
      hweak'.isRegular_of_isLocalization_of_mem S p (fun r hr => ?_), ?_⟩
    · rw [← hgens]
      exact Ideal.subset_span hr
    · rw [← Ideal.map_ofList, hgens, Localization.AtPrime.map_eq_maximalIdeal]

end WeightedTorusJets

open Ideal RingTheory.Sequence IsLocalRing

namespace WeightedTorusJets

theorem regular_maximal_generators_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) {rs : List R}
    (hreg : IsRegular R rs) (hgen : Ideal.ofList rs = maximalIdeal R) :
    IsRegular S (rs.map e) ∧ Ideal.ofList (rs.map e) = maximalIdeal S := by
  constructor
  · apply (e.toAddEquiv.isRegular_congr ?_).mp hreg
    exact List.forall₂_map_right_iff.mpr <|
      List.forall₂_same.mpr fun r _ z ↦ e.map_mul r z
  · change Ideal.ofList (rs.map e.toRingHom) = maximalIdeal S
    rw [← Ideal.map_ofList, hgen]
    exact map_ringEquiv_maximalIdeal e

theorem exists_regular_maximal_generators_field_localization (K : Type*) [Field K]
    (p : Ideal K) [p.IsPrime] :
    ∃ rs : List (Localization.AtPrime p), IsRegular (Localization.AtPrime p) rs ∧
      Ideal.ofList rs = maximalIdeal (Localization.AtPrime p) := by
  refine ⟨[], IsRegular.nil _ _, ?_⟩
  have hmap : p.map (algebraMap K (Localization.AtPrime p)) = ⊥ := by
    exact (congrArg (Ideal.map (algebraMap K (Localization.AtPrime p)))
      (Ideal.eq_bot_of_prime p)).trans Ideal.map_bot
  rw [← Localization.AtPrime.map_eq_maximalIdeal, hmap]
  simp

theorem exists_regular_maximal_generators_localizations_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      ∃ rs : List (Localization.AtPrime p), IsRegular (Localization.AtPrime p) rs ∧
        Ideal.ofList rs = maximalIdeal (Localization.AtPrime p))
    (p : Ideal S) [p.IsPrime] :
    ∃ rs : List (Localization.AtPrime p), IsRegular (Localization.AtPrime p) rs ∧
      Ideal.ofList rs = maximalIdeal (Localization.AtPrime p) := by
  obtain ⟨rs, hreg, hgen⟩ := hR (p.comap e)
  let E := IsLocalization.ringEquivOfRingEquiv
    (Localization.AtPrime (p.comap e)) (Localization.AtPrime p)
    e (e.map_primeCompl_comap_eq p)
  exact ⟨rs.map E, regular_maximal_generators_of_ringEquiv E hreg hgen⟩



open Ideal RingTheory.Sequence IsLocalRing _root_.Polynomial

theorem exists_regular_maximal_generators_polynomial_localizations
    {R : Type*} [CommRing R]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      ∃ rs : List (Localization.AtPrime p), IsRegular (Localization.AtPrime p) rs ∧
        Ideal.ofList rs = maximalIdeal (Localization.AtPrime p))
    (p : Ideal R[X]) [p.IsPrime] :
    ∃ rs : List (Localization.AtPrime p), IsRegular (Localization.AtPrime p) rs ∧
      Ideal.ofList rs = maximalIdeal (Localization.AtPrime p) := by
  let q := p.comap C
  let S := (Localization.AtPrime q)[X]
  let pc := Submonoid.map Polynomial.C.toMonoidHom q.primeCompl
  let : Algebra R[X] S := Polynomial.algebra R (Localization.AtPrime q)
  have : IsLocalization pc S := Polynomial.isLocalization _ _
  let pS := p.map (algebraMap R[X] S)
  have disj : Disjoint (pc : Set R[X]) (p : Set R[X]) := by
    simpa [pc, q] using! Set.disjoint_image_left.mpr
      (Set.disjoint_compl_left_iff_subset.mpr (fun _ a ↦ a))
  have : pS.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint pc _ _ ‹_› disj
  have : IsLocalization.AtPrime (Localization.AtPrime pS) p := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization pc
      (Localization.AtPrime pS) pS
    exact (IsLocalization.under_map_of_isPrime_disjoint pc _ ‹_› disj).symm
  have hclosed : comap C pS = maximalIdeal (Localization.AtPrime q) := by
    rw [← IsLocalization.map_under q.primeCompl _ (comap C pS),
      ← IsLocalization.map_under q.primeCompl _ (maximalIdeal (Localization.AtPrime q))]
    simp only [comap_comap, S, pS]
    rw [← Polynomial.algebraMap_eq (R := Localization.AtPrime q),
      ← IsScalarTower.algebraMap_eq R (Localization.AtPrime q) (Localization.AtPrime q)[X],
      IsScalarTower.algebraMap_eq R R[X] (Localization.AtPrime q)[X], ← comap_comap,
      ← Ideal.under_def R[X], IsLocalization.under_map_of_isPrime_disjoint pc _ ‹_› disj]
    simp [q, IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime q) q]
  obtain ⟨rs, hreg, hgen⟩ := hR q
  obtain ⟨ss, hsreg, hsgen⟩ :=
    exists_regular_generators_polynomial_localization rs hreg hgen pS hclosed
  let e := (IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime pS) (Localization.AtPrime p)).toRingEquiv
  exact ⟨ss.map e, regular_maximal_generators_of_ringEquiv e hsreg hsgen⟩

theorem exists_regular_maximal_generators_mvPolynomial_localization
    (K : Type*) [Field K] (σ : Type*) [Finite σ]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    ∃ rs : List (Localization.AtPrime p), IsRegular (Localization.AtPrime p) rs ∧
      Ideal.ofList rs = maximalIdeal (Localization.AtPrime p) := by
  revert p
  induction σ using Finite.induction_empty_option with
  | of_equiv e IH =>
    exact exists_regular_maximal_generators_localizations_of_ringEquiv
      (MvPolynomial.renameEquiv K e).toRingEquiv IH
  | h_empty =>
    exact exists_regular_maximal_generators_localizations_of_ringEquiv
      (MvPolynomial.isEmptyRingEquiv K PEmpty).symm
      (exists_regular_maximal_generators_field_localization K)
  | h_option IH =>
    exact exists_regular_maximal_generators_localizations_of_ringEquiv
      (MvPolynomial.optionEquivLeft K _).toRingEquiv.symm
      (exists_regular_maximal_generators_polynomial_localizations IH)

end WeightedTorusJets

open Ideal RingTheory.Sequence
open scoped Pointwise

namespace WeightedTorusJets

theorem span_singleton_sup_eq_of_sub_mem {R : Type*} [CommRing R]
    (J : Ideal R) {a b : R} (hdiff : a - b ∈ J) :
    Ideal.span {a} ⊔ J = Ideal.span {b} ⊔ J := by
  apply le_antisymm
  · refine sup_le ((Ideal.span_singleton_le_iff_mem _).mpr ?_) le_sup_right
    exact (Submodule.sub_mem_iff_left _ (Submodule.mem_sup_left (Ideal.mem_span_singleton_self b))).mp
      (Submodule.mem_sup_right hdiff)
  · refine sup_le ((Ideal.span_singleton_le_iff_mem _).mpr ?_) le_sup_right
    exact (Submodule.sub_mem_iff_right _ (Submodule.mem_sup_left (Ideal.mem_span_singleton_self a))).mp
      (Submodule.mem_sup_right hdiff)

theorem isRegular_append_singleton_iff_sub_mem {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (rs : List R) {a b : R}
    (hdiff : a - b ∈ Ideal.ofList rs) :
    IsRegular M (rs ++ [a]) ↔ IsRegular M (rs ++ [b]) := by
  have heq : Ideal.ofList (rs ++ [a]) = Ideal.ofList (rs ++ [b]) := by
    simpa only [Ideal.ofList_append, Ideal.ofList_singleton, sup_comm] using
      span_singleton_sup_eq_of_sub_mem (Ideal.ofList rs) hdiff
  have hab : Ideal.Quotient.mk (Ideal.ofList rs) a =
      Ideal.Quotient.mk (Ideal.ofList rs) b :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hdiff
  simp only [RingTheory.Sequence.isRegular_iff, isWeaklyRegular_append_iff' M, List.map_singleton, hab, heq]

theorem isRegular_cons_iff_sub_mem {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [IsNoetherian R M] (rs : List R) {a b : R}
    (hdiff : a - b ∈ Ideal.ofList rs) :
    IsRegular M (a :: rs) ↔ IsRegular M (b :: rs) := by
  have hp (x : R) : IsRegular M (x :: rs) ↔ IsRegular M (rs ++ [x]) :=
    ⟨fun h => IsLocalRing.isRegular_of_perm h (List.perm_append_singleton x rs).symm,
      fun h => IsLocalRing.isRegular_of_perm h (List.perm_append_singleton x rs)⟩
  exact (hp a).trans ((isRegular_append_singleton_iff_sub_mem rs hdiff).trans (hp b).symm)

theorem exists_regular_sequence_of_mem_sup_annihilator {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (J : Ideal R) (rs : List R)
    (hmem : ∀ r ∈ rs, r ∈ J ⊔ Module.annihilator R M) (hreg : IsRegular M rs) :
    ∃ ss : List R, ss.length = rs.length ∧ (∀ s ∈ ss, s ∈ J) ∧ IsRegular M ss := by
  have hrepresent : ∃ ss : List R,
      List.Forall₂ (fun r s : R => ∀ m : M, r • m = s • m) rs ss ∧
        (∀ s ∈ ss, s ∈ J) := by
    clear hreg
    induction rs with
    | nil => exact ⟨[], .nil, by simp⟩
    | cons r rs ih =>
      obtain ⟨s, hs, a, ha, hr⟩ := Submodule.mem_sup.mp (hmem r (by simp))
      obtain ⟨ss, hss, hssmem⟩ := ih (fun z hz => hmem z (by simp [hz]))
      refine ⟨s :: ss, .cons ?_ hss, ?_⟩
      · intro m
        rw [← hr, add_smul, Module.mem_annihilator.mp ha m, add_zero]
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hs
        · exact hssmem z hz
  obtain ⟨ss, hss, hssmem⟩ := hrepresent
  exact ⟨ss, hss.length_eq.symm, hssmem,
    ((AddEquiv.refl M).isRegular_congr hss).mp hreg⟩

theorem exists_regular_sequence_quotSMulTop_of_mem_sup {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (x : R) (J : Ideal R) (rs : List R)
    (hmem : ∀ r ∈ rs, r ∈ Ideal.span {x} ⊔ J)
    (hreg : IsRegular (QuotSMulTop x M) rs) :
    ∃ ss : List R, ss.length = rs.length ∧ (∀ s ∈ ss, s ∈ J) ∧
      IsRegular (QuotSMulTop x M) ss := by
  apply exists_regular_sequence_of_mem_sup_annihilator J rs _ hreg
  intro r hr
  exact (show Ideal.span {x} ⊔ J ≤ J ⊔ Module.annihilator R (QuotSMulTop x M) from
    sup_le (le_sup_of_le_right ((Ideal.span_singleton_le_iff_mem _).mpr
      (QuotSMulTop.mem_annihilator M x))) le_sup_left) (hmem r hr)

end WeightedTorusJets

open Ideal RingTheory.Sequence
open CategoryTheory Abelian

universe u

namespace WeightedTorusJets

theorem exists_regular_sequence_quotient_of_regular_element {R : Type u} [CommRing R]
    [IsNoetherianRing R] (M : ModuleCat.{u} R) [Module.Finite R M] {I : Ideal R}
    (hI : I • (⊤ : Submodule R M) < ⊤) {x : R} (hxmem : x ∈ I)
    (hx : IsSMulRegular M x) (n : ℕ) (rs : List R) (hlen : rs.length = n + 1)
    (hmem : ∀ r ∈ rs, r ∈ I) (hreg : IsRegular M rs) :
    ∃ ss : List R, ss.length = n ∧ (∀ r ∈ ss, r ∈ I) ∧
      IsRegular (QuotSMulTop x M) ss := by
  let Q := ModuleCat.of R (R ⧸ I)
  have hsupp : Module.support R Q = PrimeSpectrum.zeroLocus I := by
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  have hext : ∀ i < n + 1, Subsingleton (Ext Q M i) := by
    intro i hi
    exact ModuleCat.subsingleton_ext_of_exists_isRegular I Q hsupp.subset M hI rs
      hmem hreg i (hi.trans_eq hlen.symm)
  have hext' : ∀ i < n, Subsingleton (Ext Q (ModuleCat.of R (QuotSMulTop x M)) i) := by
    intro i hi
    have hzero₁ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hext i (by omega))
    have hzero₂ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hext (i + 1) (by omega))
    exact AddCommGrpCat.subsingleton_of_isZero <|
      ShortComplex.Exact.isZero_of_both_zeros
        ((Ext.covariant_sequence_exact₃' Q hx.smulShortComplex_shortExact) i (i + 1) rfl)
        (hzero₁.eq_zero_of_src _) (hzero₂.eq_zero_of_tgt _)
  have hquot : I • (⊤ : Submodule R (QuotSMulTop x M)) ≠ ⊤ := by
    intro htop
    absurd congrArg (Submodule.comap (Submodule.mkQ _)) htop
    simpa [Submodule.comap_smul_top_of_surjective I _ (Submodule.mkQ_surjective _),
      Submodule.smul_mono_left ((span_singleton_le_iff_mem I).mpr hxmem),
      ← Submodule.ideal_span_singleton_smul] using hI.ne
  exact ModuleCat.exists_isRegular_of_exists_subsingleton_ext I n
    (ModuleCat.of R (QuotSMulTop x M)) hquot.lt_top Q hsupp hext'

end WeightedTorusJets

open scoped BigOperators

namespace WeightedTorusJets

theorem exists_add_not_mem_of_prime_antichain {R : Type*} [CommRing R]
    (s : Finset (Ideal R)) (hp : ∀ P ∈ s, P.IsPrime)
    (hanti : ∀ P ∈ s, ∀ Q ∈ s, P ≠ Q → ¬ P ≤ Q)
    (a : R) (J : Ideal R)
    (havoid : ∀ P ∈ s, ¬ (Ideal.span {a} ⊔ J ≤ P)) :
    ∃ b ∈ J, ∀ P ∈ s, a + b ∉ P := by
  classical
  have hex (P : Ideal R) (hP : P ∈ s) :
      ∃ b : R, b ∈ J ∧ (∀ Q ∈ s, Q ≠ P → b ∈ Q) ∧
        (a ∈ P → b ∉ P) ∧ (a ∉ P → b = 0) := by
    by_cases ha : a ∈ P
    · have hJ : ¬ J ≤ P := by
        intro h
        exact havoid P hP (sup_le (P.span_singleton_le_iff_mem.mpr ha) h)
      have hi : ¬ (s.erase P).inf id ≤ P := by
        rw [(hp P hP).inf_le']
        rintro ⟨Q, hQ, hQP⟩
        have hm := Finset.mem_erase.mp hQ
        exact hanti Q hm.2 P hP hm.1 hQP
      have hn : ¬ J ⊓ (s.erase P).inf id ≤ P := by
        rw [(hp P hP).inf_le]
        exact not_or.mpr ⟨hJ, hi⟩
      obtain ⟨b, hb, hbp⟩ := SetLike.not_le_iff_exists.mp hn
      refine ⟨b, hb.1, ?_, (fun _ => hbp), (fun h => (h ha).elim)⟩
      intro Q hQ hQP
      exact (Finset.inf_le (f := id) (Finset.mem_erase.mpr ⟨hQP, hQ⟩)) hb.2
    · exact ⟨0, J.zero_mem, fun Q _ _ => Q.zero_mem, (fun h => (ha h).elim), (fun _ => rfl)⟩
  choose b hbJ hbQ hbP hbzero using hex
  let v : s → R := fun P => b P P.property
  refine ⟨∑ P : s, v P, J.sum_mem (fun P _ => hbJ P P.property), ?_⟩
  intro P hP ha
  let p : s := ⟨P, hP⟩
  have hrest : (∑ Q ∈ (Finset.univ : Finset s).erase p, v Q) ∈ P := by
    apply P.sum_mem
    intro Q hQ
    have hQp : (Q : Ideal R) ≠ P := by
      intro heq
      exact (Finset.mem_erase.mp hQ).1 (Subtype.ext heq)
    exact hbQ Q Q.property P hP hQp.symm
  have hsum : (∑ Q : s, v Q) = v p + ∑ Q ∈ (Finset.univ : Finset s).erase p, v Q := by
    symm
    exact Finset.add_sum_erase _ _ (Finset.mem_univ p)
  rw [hsum] at ha
  by_cases haP : a ∈ P
  · have hv : v p ∈ P := by
      have h := P.sub_mem ha (P.add_mem haP hrest)
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
    exact hbP P hP haP hv
  · have hv : v p = 0 := hbzero P hP haP
    exact haP (by simpa [hv] using P.sub_mem ha hrest)

end WeightedTorusJets

namespace WeightedTorusJets.Geometry

theorem exists_add_not_mem_of_finite_prime {R : Type*} [CommRing R]
    (s : Finset (Ideal R)) (hp : ∀ P ∈ s, P.IsPrime) (a : R) (J : Ideal R)
    (havoid : ∀ P ∈ s, ¬ (Ideal.span {a} ⊔ J ≤ P)) :
    ∃ b ∈ J, ∀ P ∈ s, a + b ∉ P := by
  classical
  let t := s.filter (Maximal (· ∈ s))
  have htanti : ∀ P ∈ t, ∀ Q ∈ t, P ≠ Q → ¬ P ≤ Q := by
    intro P hP Q hQ hne hle
    exact hne (le_antisymm hle
      ((Finset.mem_filter.mp hP).2.2 (Finset.mem_filter.mp hQ).1 hle))
  obtain ⟨b, hb, hbavoid⟩ := exists_add_not_mem_of_prime_antichain t
    (fun P hP ↦ hp P (Finset.mem_filter.mp hP).1) htanti a J
    (fun P hP ↦ havoid P (Finset.mem_filter.mp hP).1)
  refine ⟨b, hb, fun P hP hab ↦ ?_⟩
  obtain ⟨Q, hPQ, hQ⟩ := s.exists_le_maximal hP
  exact hbavoid Q (Finset.mem_filter.mpr ⟨hQ.1, hQ⟩) (hPQ hab)

theorem exists_add_isSMulRegular {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [IsNoetherian R M] (a : R) (J : Ideal R)
    (havoid : ∀ P ∈ associatedPrimes R M, ¬ (Ideal.span {a} ⊔ J ≤ P)) :
    ∃ b ∈ J, IsSMulRegular M (a + b) := by
  classical
  have hfinite := associatedPrimes.finite R M
  obtain ⟨b, hb, hbavoid⟩ := exists_add_not_mem_of_finite_prime hfinite.toFinset
    (fun P hP ↦ (hfinite.mem_toFinset.mp hP).isPrime) a J
    (fun P hP ↦ havoid P (hfinite.mem_toFinset.mp hP))
  refine ⟨b, hb, ?_⟩
  have hnot : a + b ∉ ⋃ P ∈ associatedPrimes R M, (P : Set R) := by
    intro h
    obtain ⟨P, hP⟩ := Set.mem_iUnion.mp h
    obtain ⟨hPass, hmem⟩ := Set.mem_iUnion.mp hP
    exact hbavoid P (hfinite.mem_toFinset.mpr hPass) hmem
  simpa only [biUnion_associatedPrimes_eq_compl_regular R M, Set.mem_compl_iff,
    Set.mem_ofPred_eq, not_not] using hnot

theorem exists_add_isSMulRegular_of_exists {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [IsNoetherian R M] (a : R) (J : Ideal R)
    (h : ∃ x ∈ Ideal.span {a} ⊔ J, IsSMulRegular M x) :
    ∃ b ∈ J, IsSMulRegular M (a + b) := by
  obtain ⟨x, hx, hxreg⟩ := h
  apply exists_add_isSMulRegular a J
  intro P hP hle
  have hxnot : x ∉ ⋃ Q ∈ associatedPrimes R M, (Q : Set R) := by
    simpa only [biUnion_associatedPrimes_eq_compl_regular R M, Set.mem_compl_iff,
      Set.mem_ofPred_eq, not_not] using hxreg
  exact hxnot (Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨hP, hle hx⟩⟩)

end WeightedTorusJets.Geometry

namespace WeightedTorusJets

universe uReg

theorem isRegular_of_exists_regular_sequence_in_ofList {R : Type uReg} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (gs : List R) (M : Type uReg)
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hproper : Ideal.ofList gs • (⊤ : Submodule R M) < ⊤)
    (rs : List R) (hlen : rs.length = gs.length)
    (hmem : ∀ r ∈ rs, r ∈ Ideal.ofList gs) (hreg : IsRegular M rs) :
    IsRegular M gs := by
  induction gs generalizing M rs with
  | nil =>
    have hrs : rs = [] := List.length_eq_zero_iff.mp hlen
    subst rs
    exact hreg
  | cons a gs ih =>
    cases rs with
    | nil => simp at hlen
    | cons z zs =>
      obtain ⟨b, hb, hxreg⟩ := Geometry.exists_add_isSMulRegular_of_exists a
        (Ideal.ofList gs) ⟨z, by simpa only [Ideal.ofList_cons] using hmem z (by simp),
          ((isRegular_cons_iff M z zs).mp hreg).1⟩
      let x := a + b
      have hdiff : x - a ∈ Ideal.ofList gs := by
        simpa only [x, add_sub_cancel_left] using hb
      have heq : Ideal.ofList (x :: gs) = Ideal.ofList (a :: gs) := by
        simpa only [Ideal.ofList_cons] using
          span_singleton_sup_eq_of_sub_mem (Ideal.ofList gs) hdiff
      have hxmem : x ∈ Ideal.ofList (a :: gs) :=
        heq ▸ Ideal.subset_span (by simp)
      obtain ⟨ss, hsslen, hssmem, hssreg⟩ :=
        exists_regular_sequence_quotient_of_regular_element (ModuleCat.of R M) hproper
          hxmem hxreg gs.length (z :: zs) hlen hmem hreg
      obtain ⟨ts, htslen, htsmem, htsreg⟩ :=
        exists_regular_sequence_quotSMulTop_of_mem_sup x (Ideal.ofList gs) ss
          (fun r hr => by simpa only [← heq, Ideal.ofList_cons] using hssmem r hr) hssreg
      have hquot : Ideal.ofList gs • (⊤ : Submodule R (QuotSMulTop x M)) < ⊤ := by
        apply lt_top_iff_ne_top.mpr
        intro htop
        have htop' := (Submodule.top_eq_ofList_cons_smul_iff (M := M)
          (r := x) (rs := gs)).mpr htop.symm
        rw [heq] at htop'
        exact hproper.ne htop'.symm
      have htail := ih (QuotSMulTop x M) hquot ts (htslen.trans hsslen) htsmem htsreg
      exact (isRegular_cons_iff_sub_mem gs hdiff).mp
        ((isRegular_cons_iff M x gs).mpr ⟨hxreg, htail⟩)

end WeightedTorusJets

namespace WeightedTorusJets
open IsLocalRing
theorem exists_regular_sequence_of_le_radical {R : Type u} [CommRing R]
    [IsNoetherianRing R] (M : ModuleCat.{u} R) [Module.Finite R M] {I J : Ideal R}
    (hI : I • (⊤ : Submodule R M) < ⊤) (hJ : J • (⊤ : Submodule R M) < ⊤)
    (hIJ : I ≤ J.radical) (rs : List R) (hmem : ∀ r ∈ rs, r ∈ I)
    (hreg : IsRegular M rs) :
    ∃ ss : List R, ss.length = rs.length ∧ (∀ r ∈ ss, r ∈ J) ∧ IsRegular M ss := by
  let Q := ModuleCat.of R (R ⧸ J)
  have hsupp : Module.support R Q = PrimeSpectrum.zeroLocus J := by
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  have hsub : Module.support R Q ⊆ PrimeSpectrum.zeroLocus I := by
    rw [hsupp, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff]
    exact hIJ
  have hext := ModuleCat.subsingleton_ext_of_exists_isRegular I Q hsub M hI rs hmem hreg
  exact ModuleCat.exists_isRegular_of_exists_subsingleton_ext J rs.length M hJ Q hsupp hext

theorem regular_maximal_generators_length {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] {rs : List R}
    (hreg : IsRegular R rs) (hgen : Ideal.ofList rs = maximalIdeal R) :
    (rs.length : ℕ∞) = (maximalIdeal R).height := by
  let := Ideal.Quotient.field (maximalIdeal R)
  have h := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular rs hreg
  rw [hgen, ringKrullDim_eq_zero_of_field, zero_add,
    ← maximalIdeal_height_eq_ringKrullDim] at h
  exact_mod_cast h

end WeightedTorusJets
namespace WeightedTorusJets

universe uReg

theorem isRegular_parameters_of_exists_regular_maximal_generators
    {R : Type uReg} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hex : ∃ rs : List R, IsRegular R rs ∧
      Ideal.ofList rs = IsLocalRing.maximalIdeal R)
    (fs : List R) (hrad : (Ideal.ofList fs).radical = IsLocalRing.maximalIdeal R)
    (hlen : (fs.length : ℕ∞) = (IsLocalRing.maximalIdeal R).height) :
    IsRegular R fs := by
  obtain ⟨rs, hrsreg, hrsgen⟩ := hex
  have hproper : Ideal.ofList fs ≠ ⊤ := by
    intro htop
    rw [htop, Ideal.radical_top] at hrad
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hrad.symm
  have hM : IsLocalRing.maximalIdeal R • (⊤ : Submodule R R) < ⊤ := by
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top.lt_top
  obtain ⟨ss, hsslen, hssmem, hssreg⟩ := exists_regular_sequence_of_le_radical
    (ModuleCat.of R R) hM
    (by simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hproper.lt_top)
    (le_of_eq hrad.symm) rs
    (fun r hr => hrsgen ▸ Ideal.subset_span hr) hrsreg
  have hrslen : rs.length = fs.length := by
    exact_mod_cast (regular_maximal_generators_length hrsreg hrsgen).trans hlen.symm
  exact isRegular_of_exists_regular_sequence_in_ofList fs R
    (by simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hproper.lt_top)
    ss (hsslen.trans hrslen) hssmem hssreg

end WeightedTorusJets

end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_LocalQuotientEquiv
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
open _root_.Polynomial
open Ideal RingTheory.Sequence IsLocalRing
open Ideal RingTheory.Sequence
open scoped Pointwise
open Ideal RingTheory.Sequence
open CategoryTheory Abelian
universe u
open scoped BigOperators
namespace WeightedTorusJets

theorem isRegular_parameters_mvPolynomial_localization
    (K : Type*) [Field K] (σ : Type*) [Finite σ]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (fs : List (Localization.AtPrime p))
    (hrad : (Ideal.ofList fs).radical = IsLocalRing.maximalIdeal (Localization.AtPrime p))
    (hlen : (fs.length : ℕ∞) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)).height) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime p) fs := by
  exact isRegular_parameters_of_exists_regular_maximal_generators
    (exists_regular_maximal_generators_mvPolynomial_localization K σ p) fs hrad hlen

end WeightedTorusJets

namespace WeightedTorusJets.Deformation

theorem isRegular_quotient_iff
    {K S R : Type*} [CommRing K] [CommRing S] [CommRing R]
    [Algebra K S] [Algebra K R]
    (J : Ideal S) (e : (S ⧸ J) ≃ₐ[K] R) (fs : List S) :
    RingTheory.Sequence.IsRegular (S ⧸ J) fs ↔
      RingTheory.Sequence.IsRegular R (fs.map (fun x => e (Ideal.Quotient.mk J x))) := by
  apply e.toAddEquiv.isRegular_congr
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro r _ x
  change e ((Ideal.Quotient.mk J r) * x) = e (Ideal.Quotient.mk J r) * e x
  exact e.map_mul _ _

theorem isRegular_quotSMulTop_iff
    {K S R : Type*} [CommRing K] [CommRing S] [CommRing R]
    [Algebra K S] [Algebra K R]
    (t : S) (e : (S ⧸ Ideal.span {t}) ≃ₐ[K] R) (fs : List S) :
    RingTheory.Sequence.IsRegular (QuotSMulTop t S) fs ↔
      RingTheory.Sequence.IsRegular R
        (fs.map (fun x => e (Ideal.Quotient.mk (Ideal.span {t}) x))) :=
  ((QuotSMulTop.equivQuotTensor t S ≪≫ₗ TensorProduct.rid S (S ⧸ Ideal.span {t})).isRegular_congr fs).trans
    (isRegular_quotient_iff (Ideal.span {t}) e fs)



open _root_.Polynomial

theorem isRegular_mvPolynomial_localized_special_fiber
    {K σ : Type*} [Field K] [Finite σ]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime] (a : K)
    (Fs : List (MvPolynomial σ K[X]))
    (hrad : (Ideal.ofList (Fs.map (fun f =>
      algebraMap (MvPolynomial σ K) (Localization.AtPrime p)
        (MvPolynomial.map (evalRingHom a) f)))).radical =
          IsLocalRing.maximalIdeal (Localization.AtPrime p))
    (hlen : (Fs.length : ℕ∞) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)).height) :
    let S := Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a)))
    let t : S := algebraMap (MvPolynomial σ K[X]) S
      (MvPolynomial.C (σ := σ) (X - C a))
    RingTheory.Sequence.IsRegular (QuotSMulTop t S)
      (Fs.map (algebraMap (MvPolynomial σ K[X]) S)) := by
  let S := Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a)))
  let : CommRing S := inferInstance
  let t : S := algebraMap (MvPolynomial σ K[X]) S
    (MvPolynomial.C (σ := σ) (X - C a))
  change RingTheory.Sequence.IsRegular (QuotSMulTop t S)
    (Fs.map (algebraMap (MvPolynomial σ K[X]) S))
  let e : (S ⧸ Ideal.span {t}) ≃ₐ[K] Localization.AtPrime p :=
    mvPolynomialLocalQuotientAlgEquiv p a
  apply (isRegular_quotSMulTop_iff (K := K) (S := S) (R := Localization.AtPrime p)
    t e (Fs.map (algebraMap (MvPolynomial σ K[X]) S))).mpr
  have hreg := WeightedTorusJets.isRegular_parameters_mvPolynomial_localization K σ p
    (Fs.map (fun f => algebraMap (MvPolynomial σ K) (Localization.AtPrime p)
      (MvPolynomial.map (evalRingHom a) f))) hrad (by simpa only [List.length_map] using hlen)
  simpa only [List.map_map, Function.comp_def, e, t, S,
    mvPolynomialLocalQuotientAlgEquiv_apply_mk_algebraMap] using hreg

end WeightedTorusJets.Deformation

namespace WeightedTorusJets.Deformation

theorem isRegular_source_polynomialDeformation_special_fiber
    {K σ : Type*} [Field K] [Finite σ]
    (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (f : σ → MvPolynomial σ K) (d : ℕ) (is : List σ)
    (hrad : (Ideal.ofList (is.map (fun i =>
      algebraMap (MvPolynomial σ K) (Localization.AtPrime p) (f i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime p))
    (hlen : (is.length : ℕ∞) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)).height) :
    let S := Localization.AtPrime
      (p.comap (MvPolynomial.map (σ := σ) (Polynomial.evalRingHom (0 : K))))
    let t : S := algebraMap (MvPolynomial σ (Polynomial K)) S
      (MvPolynomial.C (σ := σ) (Polynomial.X - Polynomial.C (0 : K)))
    RingTheory.Sequence.IsRegular (QuotSMulTop t S)
      ((is.map (WeightedTorusJets.polynomialDeformation f d)).map
        (algebraMap (MvPolynomial σ (Polynomial K)) S)) := by
  exact isRegular_mvPolynomial_localized_special_fiber p 0
    (is.map (WeightedTorusJets.polynomialDeformation f d))
    (by simpa only [List.map_map, Function.comp_def,
      WeightedTorusJets.polynomialDeformation_at_zero] using hrad)
    (by simpa only [List.length_map] using hlen)



open RingTheory.Sequence
open scoped Pointwise

theorem parameter_regular_after_quotient
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [IsNoetherian R M]
    (t : R) (fs : List R) (ht : IsSMulRegular M t)
    (hfs : RingTheory.Sequence.IsRegular (QuotSMulTop t M) fs) :
    IsSMulRegular (M ⧸ (Ideal.ofList fs • ⊤ : Submodule R M)) t := by
  have h : RingTheory.Sequence.IsRegular M (t :: fs) := IsRegular.cons ht hfs
  have hp : List.Perm (t :: fs) (fs ++ [t]) := by
    exact List.perm_append_comm (l₁ := [t]) (l₂ := fs)
  have h' := IsLocalRing.isRegular_of_perm h hp
  exact (isWeaklyRegular_singleton_iff _ _).mp
    ((isWeaklyRegular_append_iff M fs [t]).mp h'.toIsWeaklyRegular).2

theorem flat_of_regular_uniformizer
    {R M : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M]
    (t : R) (ht : Irreducible t) (hreg : IsSMulRegular M t) : Module.Flat R M := by
  have : Module.IsTorsionFree R M := ⟨fun r hr => by
    obtain ⟨n, h⟩ := IsDiscreteValuationRing.associated_pow_irreducible hr.ne_zero ht
    obtain ⟨u, hu⟩ := h.symm
    rw [← hu]
    exact (hreg.pow n).mul (u.isSMulRegular M)⟩
  infer_instance

theorem flat_quotient_of_regular_special_fiber
    {A S M : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing S] [IsLocalRing S] [Algebra A S]
    [AddCommGroup M] [Module S M] [Module A M] [IsScalarTower A S M]
    [IsNoetherian S M] (t : A) (ht : Irreducible t) (fs : List S)
    (hreg : IsSMulRegular M (algebraMap A S t))
    (hfs : RingTheory.Sequence.IsRegular (QuotSMulTop (algebraMap A S t) M) fs) :
    Module.Flat A (M ⧸ (Ideal.ofList fs • ⊤ : Submodule S M)) := by
  apply flat_of_regular_uniformizer t ht
  exact (isSMulRegular_map (algebraMap A S) fun m => algebraMap_smul S t m).mp
    (parameter_regular_after_quotient (algebraMap A S t) fs hreg hfs)

end WeightedTorusJets.Deformation

namespace WeightedTorusJets.Deformation

open _root_.Polynomial

theorem dvr_polynomial_at_linear
    {K : Type*} [Field K] (I : Ideal K[X]) [I.IsPrime]
    (a : K) (hI : I = Ideal.span {X - C a}) :
    IsDiscreteValuationRing (Localization.AtPrime I) := by
  apply IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain K[X] (P := I)
  rw [hI, ne_eq, Ideal.span_singleton_eq_bot]
  exact (irreducible_X_sub_C a).ne_zero

theorem irreducible_parameter_at_linear
    {K : Type*} [Field K] (I : Ideal K[X]) [I.IsPrime]
    (a : K) (hI : I = Ideal.span {X - C a}) :
    Irreducible (algebraMap K[X] (Localization.AtPrime I) (X - C a)) := by
  have : IsDiscreteValuationRing (Localization.AtPrime I) := dvr_polynomial_at_linear I a hI
  apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  calc
    Ideal.map (algebraMap K[X] (Localization.AtPrime I)) I =
        Ideal.map (algebraMap K[X] (Localization.AtPrime I)) (Ideal.span {X - C a}) :=
      congrArg (Ideal.map (algebraMap K[X] (Localization.AtPrime I))) hI
    _ = _ := by rw [Ideal.map_span]; simp

end WeightedTorusJets.Deformation

namespace WeightedTorusJets.Deformation

open _root_.Polynomial

theorem parameterLocalAlgebra_isScalarTower
    {K σ : Type*} [Field K] (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (I : Ideal K[X]) [I.IsPrime] (a : K) (hI : I = Ideal.span {X - C a}) :
    let := parameterLocalAlgebra p I a hI
    IsScalarTower K[X] (Localization.AtPrime I)
      (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a)))) := by
  let := parameterLocalAlgebra p I a hI
  apply IsScalarTower.of_algebraMap_eq
  intro f
  change algebraMap K[X] _ f =
    Localization.localRingHom I _ MvPolynomial.C _ (algebraMap K[X] _ f)
  rw [Localization.localRingHom_to_map]
  rfl

theorem parameterLocalAlgebra_parameter
    {K σ : Type*} [Field K] (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (I : Ideal K[X]) [I.IsPrime] (a : K) (hI : I = Ideal.span {X - C a}) :
    let := parameterLocalAlgebra p I a hI
    algebraMap (Localization.AtPrime I)
      (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a))))
        (algebraMap K[X] (Localization.AtPrime I) (X - C a)) =
      algebraMap (MvPolynomial σ K[X]) _ (MvPolynomial.C (X - C a)) := by
  let := parameterLocalAlgebra p I a hI
  exact Localization.localRingHom_to_map I _ MvPolynomial.C _ (X - C a)

theorem parameterLocalAlgebra_groundFieldTower
    {K σ : Type*} [Field K] (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (I : Ideal K[X]) [I.IsPrime] (a : K) (hI : I = Ideal.span {X - C a}) :
    letI := parameterLocalAlgebra p I a hI
    IsScalarTower K (Localization.AtPrime I)
      (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a)))) := by
  let := parameterLocalAlgebra p I a hI
  have := parameterLocalAlgebra_isScalarTower p I a hI
  exact IsScalarTower.to₁₃₄ K K[X] (Localization.AtPrime I) _

theorem localized_polynomial_parameter_ne_zero
    {K σ : Type*} [Field K] (p : Ideal (MvPolynomial σ K)) [p.IsPrime] (a : K) :
    algebraMap (MvPolynomial σ K[X])
      (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a))))
        (MvPolynomial.C (X - C a)) ≠ 0 := by
  intro h
  have hC : MvPolynomial.C (σ := σ) (X - C a) = 0 :=
    (FaithfulSMul.algebraMap_injective (MvPolynomial σ K[X]) _)
      (h.trans (map_zero _).symm)
  exact X_sub_C_ne_zero a ((MvPolynomial.C_injective σ K[X])
    (hC.trans (map_zero _).symm))

theorem parameterLocalAlgebra_parameter_regular
    {K σ : Type*} [Field K] (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (I : Ideal K[X]) [I.IsPrime] (a : K) (hI : I = Ideal.span {X - C a}) :
    letI := parameterLocalAlgebra p I a hI
    IsSMulRegular
      (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a))))
      (algebraMap (Localization.AtPrime I)
        (Localization.AtPrime (p.comap (MvPolynomial.map (σ := σ) (evalRingHom a))))
          (algebraMap K[X] (Localization.AtPrime I) (X - C a))) := by
  let := parameterLocalAlgebra p I a hI
  rw [parameterLocalAlgebra_parameter]
  exact IsSMulRegular.of_ne_zero (localized_polynomial_parameter_ne_zero p a)

end WeightedTorusJets.Deformation

namespace WeightedTorusJets.Deformation

theorem flat_ideal_quotient_of_flat_smul_top
    {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    (I : Ideal S)
    (hflat : Module.Flat A (S ⧸ (I • ⊤ : Submodule S S))) :
    Module.Flat A (S ⧸ I) := by
  let := hflat
  have hI : (I • ⊤ : Submodule S S) = I := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  exact Module.Flat.of_linearEquiv
    (((Submodule.quotEquivOfEq _ _ hI).restrictScalars A).symm)

theorem ideal_ofList_ofFn_eq_span_range
    {S : Type*} [CommRing S] {n : ℕ} (f : Fin n → S) :
    Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f) := by
  unfold Ideal.ofList
  congr 1
  ext x
  exact List.mem_ofFn' f x

theorem ideal_ofList_map_finRange_eq_span_range
    {S : Type*} [CommRing S] {n : ℕ} (f : Fin n → S) :
    Ideal.ofList ((List.finRange n).map f) = Ideal.span (Set.range f) := by
  rw [← List.ofFn_eq_map]
  exact ideal_ofList_ofFn_eq_span_range f

theorem flat_span_range_quotient_of_flat_ofFn_smul_top
    {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    {n : ℕ} (f : Fin n → S)
    (hflat : Module.Flat A (S ⧸ (Ideal.ofList (List.ofFn f) • ⊤ : Submodule S S))) :
    Module.Flat A (S ⧸ Ideal.span (Set.range f)) := by
  let := flat_ideal_quotient_of_flat_smul_top (Ideal.ofList (List.ofFn f)) hflat
  exact Module.Flat.of_linearEquiv
    ((Ideal.quotientEquivAlgOfEq A (ideal_ofList_ofFn_eq_span_range f)).toLinearEquiv.symm)



open _root_.Polynomial
open scoped Pointwise

theorem flat_polynomialDeformation_localized
    {K : Type*} [Field K] {h : ℕ}
    (p : Ideal (MvPolynomial (Fin h) K)) [p.IsPrime]
    (I : Ideal K[X]) [I.IsPrime] (hI : I = Ideal.span {X - C (0 : K)})
    (f : Fin h → MvPolynomial (Fin h) K) (d : ℕ)
    (hrad : (Ideal.span (Set.range (fun i =>
      algebraMap (MvPolynomial (Fin h) K) (Localization.AtPrime p) (f i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime p))
    (hlen : (h : ℕ∞) = (IsLocalRing.maximalIdeal (Localization.AtPrime p)).height) :
    letI := parameterLocalAlgebra p I 0 hI
    let S := Localization.AtPrime
      (p.comap (MvPolynomial.map (σ := Fin h) (evalRingHom (0 : K))))
    letI : CommRing S := inferInstance
    Module.Flat (Localization.AtPrime I)
      (S ⧸ Ideal.span (Set.range (fun i =>
        algebraMap (MvPolynomial (Fin h) K[X]) S (polynomialDeformation f d i)))) := by
  let := parameterLocalAlgebra p I 0 hI
  have := dvr_polynomial_at_linear I 0 hI
  let S := Localization.AtPrime
    (p.comap (MvPolynomial.map (σ := Fin h) (evalRingHom (0 : K))))
  let : CommRing S := inferInstance
  let fs : Fin h → S := fun i =>
    algebraMap (MvPolynomial (Fin h) K[X]) S (polynomialDeformation f d i)
  apply flat_span_range_quotient_of_flat_ofFn_smul_top fs
  apply flat_quotient_of_regular_special_fiber
    (algebraMap K[X] (Localization.AtPrime I) (X - C (0 : K)))
    (irreducible_parameter_at_linear I 0 hI) (List.ofFn fs)
    (parameterLocalAlgebra_parameter_regular p I 0 hI)
  rw [show algebraMap (Localization.AtPrime I) S
      (algebraMap K[X] (Localization.AtPrime I) (X - C (0 : K))) =
      algebraMap (MvPolynomial (Fin h) K[X]) S (MvPolynomial.C (X - C (0 : K))) from
        parameterLocalAlgebra_parameter p I 0 hI]
  have hs := isRegular_source_polynomialDeformation_special_fiber p f d (List.finRange h)
    (by simpa only [ideal_ofList_map_finRange_eq_span_range] using hrad)
    (by simpa only [List.length_finRange] using hlen)
  simpa only [← List.ofFn_eq_map, List.map_ofFn, Function.comp_def] using hs

end WeightedTorusJets.Deformation

end

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_HomogeneousDeformation
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.GradedQuotient.degreePiece_finite _root_.OAI.Erdos970.WeightedTorusJets.Geometry.finite_rectangularQuotient _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.OAI.Erdos970.WeightedTorusJets.Geometry.rectangularCoefficientDerivation_mk _root_.OAI.Erdos970.WeightedTorusJets.Geometry.rectangularCoefficientDerivation_zero _root_.OAI.Erdos970.WeightedTorusJets.Geometry.rectangularMap_mk _root_.OAI.Erdos970.WeightedTorusJets.Geometry.rectangularTaylorAlong_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section

open scoped BigOperators

namespace WeightedTorusJets

open MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S]

theorem map_homogeneousComponent (φ : R →+* S) (n : ℕ) (f : MvPolynomial σ R) :
    map φ (homogeneousComponent n f) = homogeneousComponent n (map φ f) := by
  ext a
  simp only [coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

theorem polynomialDeformation_at_one (f : σ → MvPolynomial σ R) (d : ℕ) (i : σ) :
    map (Polynomial.evalRingHom 1) (polynomialDeformation f d i) = X i ^ d := by
  simp [polynomialDeformation]

theorem homogeneousDeformation_at_one (f : σ → MvPolynomial σ R) (d : ℕ) (i : σ) :
    map (Polynomial.evalRingHom 1) (homogeneousDeformation f d i) = X i ^ d := by
  rw [homogeneousDeformation, map_homogeneousComponent, polynomialDeformation_at_one]
  simp [homogeneousComponent_of_mem (isHomogeneous_X_pow i d)]

theorem macaulayMatrix_map (φ : R →+* S) (d n : ℕ) (G : σ → MvPolynomial σ R) :
    (macaulayMatrix d n G).map φ = macaulayMatrix d n (fun i => map φ (G i)) := by
  ext a b
  change φ ((monomial b.2.1 1 * G b.1).coeff a.1) =
    (monomial b.2.1 1 * map φ (G b.1)).coeff a.1
  rw [← coeff_map]
  simp

theorem deformed_macaulay_at_one (f : σ → MvPolynomial σ R) (d n : ℕ) :
    (macaulayMatrix d n (homogeneousDeformation f d)).map (Polynomial.evalRingHom 1) =
      macaulayMatrix d n (fun i => (X i : MvPolynomial σ R) ^ d) := by
  rw [macaulayMatrix_map]
  simp only [homogeneousDeformation_at_one]

end WeightedTorusJets

open Module

open MvPolynomial

noncomputable section

namespace WeightedTorusJets.Geometry.GradedQuotient

variable {K σ : Type*} [Field K]

theorem degreePresentation_surjective (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    Function.Surjective (degreePresentation I n) :=
  (Ideal.Quotient.mkₐ K I).toLinearMap.submoduleMap_surjective _

theorem ker_degreePresentation (I : Ideal (MvPolynomial σ K)) (n : ℕ) :
    LinearMap.ker (degreePresentation I n) =
      (I.restrictScalars K).comap (homogeneousSubmodule σ K n).subtype := by
  change LinearMap.ker (((I.restrictScalars K).mkQ).submoduleMap
    (homogeneousSubmodule σ K n)) = _
  rw [LinearMap.ker_submoduleMap, Submodule.ker_mkQ]

theorem finrank_degreePiece_eq_sub_finrank_range [Finite σ]
    {V : Type*} [AddCommGroup V] [Module K V]
    (I : Ideal (MvPolynomial σ K)) (n : ℕ) (m : V →ₗ[K] homogeneousSubmodule σ K n)
    (hrange : LinearMap.range m =
      (I.restrictScalars K).comap (homogeneousSubmodule σ K n).subtype) :
    Module.finrank K (degreePiece I n) =
      Module.finrank K (homogeneousSubmodule σ K n) - Module.finrank K (LinearMap.range m) := by
  let : Module.Finite K (homogeneousSubmodule σ K n) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg σ K n)
  have h := (degreePresentation I n).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (degreePresentation_surjective I n), finrank_top,
    ker_degreePresentation, ← hrange] at h
  omega

end WeightedTorusJets.Geometry.GradedQuotient

namespace WeightedTorusJets

open MvPolynomial

theorem macaulayMap_range_eq_ideal_slice {σ K : Type*} [Fintype σ] [Field K]
    (d n : ℕ) (G : σ → MvPolynomial σ K) (hG : ∀ i, (G i).IsHomogeneous d) :
    LinearMap.range (macaulayMap d n G hG) =
      ((Ideal.span (Set.range G)).restrictScalars K).comap
        (homogeneousSubmodule σ K n).subtype := by
  classical
  let T := LinearMap.range (macaulayMap d n G hG)
  let J := T.map (homogeneousSubmodule σ K n).subtype
  have hJ (b : σ × {b : σ →₀ ℕ // b.degree + d = n}) :
      monomial b.2.1 1 * G b.1 ∈ J := by
    refine ⟨macaulayColumn d n G hG b, ?_, rfl⟩
    exact ⟨Finsupp.single b 1, by simp [macaulayMap]⟩
  apply le_antisymm
  · rw [macaulayMap, Finsupp.range_linearCombination]
    apply Submodule.span_le.mpr
    rintro p ⟨b, rfl⟩
    change monomial b.2.1 1 * G b.1 ∈ Ideal.span (Set.range G)
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨b.1, rfl⟩)
  · intro p hp
    change (p : MvPolynomial σ K) ∈ Ideal.span (Set.range G) at hp
    obtain ⟨g, hg⟩ := Ideal.mem_span_range_iff_exists_fun.mp hp
    have hmul (i : σ) : homogeneousComponent n (g i * G i) ∈ J := by
      by_cases hdn : d ≤ n
      · rw [mul_comm (g i) (G i),
          Geometry.GradedQuotient.homogeneousComponent_mul_of_le (hG i) hdn,
          mul_comm (G i)]
        let a := homogeneousComponent (n - d) (g i)
        change a * G i ∈ J
        rw [a.as_sum, Finset.sum_mul]
        apply J.sum_mem
        intro b hb
        have hbdeg : b.degree = n - d :=
          (Finsupp.degree_apply b).trans
            ((homogeneousComponent_isHomogeneous (n - d) (g i)).degree_eq_sum_deg_support hb).symm
        have hbnd : b.degree + d = n := by omega
        simpa only [← smul_mul_assoc, smul_monomial, smul_eq_mul, mul_one] using
          J.smul_mem (a.coeff b) (hJ (i, ⟨b, hbnd⟩))
      · rw [mul_comm (g i) (G i),
          Geometry.GradedQuotient.homogeneousComponent_mul_of_lt (hG i)
            (Nat.lt_of_not_ge hdn)]
        exact J.zero_mem
    have hpJ : (p : MvPolynomial σ K) ∈ J := by
      rw [← homogeneousComponent_eq_self p.property, ← hg, map_sum]
      exact J.sum_mem fun i _ => hmul i
    obtain ⟨p', hp', hpp⟩ := hpJ
    have hpp' : p' = p := Subtype.ext hpp
    rwa [hpp'] at hp'

end WeightedTorusJets

namespace WeightedTorusJets

open MvPolynomial Geometry.GradedQuotient

theorem toMatrix_macaulayMap {σ K : Type*} [Fintype σ] [Field K]
    (d n : ℕ) (G : σ → MvPolynomial σ K) (hG : ∀ i, (G i).IsHomogeneous d)
    [Fintype {a : σ →₀ ℕ // a.degree = n}]
    [Fintype {b : σ →₀ ℕ // b.degree + d = n}]
    [DecidableEq (σ × {b : σ →₀ ℕ // b.degree + d = n})] :
    LinearMap.toMatrix Finsupp.basisSingleOne (homogeneousMonomialBasis σ K n)
      (macaulayMap d n G hG) = macaulayMatrix d n G := by
  ext a b
  simp only [macaulayMap, LinearMap.toMatrix_apply, Finsupp.coe_basisSingleOne,
    Finsupp.linearCombination_single, one_smul]
  rfl

theorem macaulayMatrix_rank_eq_finrank_range {σ K : Type*} [Fintype σ] [Field K]
    (d n : ℕ) (G : σ → MvPolynomial σ K) (hG : ∀ i, (G i).IsHomogeneous d)
    [Fintype {a : σ →₀ ℕ // a.degree = n}]
    [Fintype {b : σ →₀ ℕ // b.degree + d = n}] :
    (macaulayMatrix d n G).rank = Module.finrank K (LinearMap.range (macaulayMap d n G hG)) := by
  classical
  rw [← toMatrix_macaulayMap d n G hG]
  rw [Matrix.rank_eq_finrank_range_toLin _ (homogeneousMonomialBasis σ K n)
    Finsupp.basisSingleOne, Matrix.toLin_toMatrix]

theorem finrank_degreePiece_span_eq_sub_macaulayMatrix_rank
    {σ K : Type*} [Fintype σ] [Field K]
    (d n : ℕ) (G : σ → MvPolynomial σ K) (hG : ∀ i, (G i).IsHomogeneous d)
    [Fintype {a : σ →₀ ℕ // a.degree = n}]
    [Fintype {b : σ →₀ ℕ // b.degree + d = n}] :
    Module.finrank K (degreePiece (Ideal.span (Set.range G)) n) =
      Module.finrank K (homogeneousSubmodule σ K n) - (macaulayMatrix d n G).rank := by
  rw [finrank_degreePiece_eq_sub_finrank_range _ _ _
    (macaulayMap_range_eq_ideal_slice d n G hG),
    macaulayMatrix_rank_eq_finrank_range d n G hG]

end WeightedTorusJets

namespace WeightedTorusJets.Geometry

theorem exists_row_minor_det_ne_zero {K ι n : Type*} [Field K]
    [Fintype n] [DecidableEq n] (v : ι → n → K)
    (hv : Submodule.span K (Set.range v) = ⊤) :
    ∃ e : n → ι, Function.Injective e ∧ Matrix.det (fun i j => v (e i) j) ≠ 0 := by
  classical
  obtain ⟨b, hbmem, _, hbli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range v)
  choose f hf using hbmem
  have hk : Module.finrank K (Submodule.span K (Set.range v)) = Fintype.card n := by
    rw [hv, finrank_top, Module.finrank_pi]
  let e₀ : n ≃ Fin (Module.finrank K (Submodule.span K (Set.range v))) :=
    Fintype.equivFinOfCardEq hk.symm
  let e : n → ι := f ∘ e₀
  have he : (fun i => v (e i)) = b ∘ e₀ := by
    funext i
    exact hf (e₀ i)
  have hrow : LinearIndependent K (fun i => v (e i)) := by
    rw [he]
    exact hbli.comp e₀ e₀.injective
  refine ⟨e, ?_, ?_⟩
  · intro i j hij
    exact hrow.injective (congrArg v hij)
  · exact isUnit_iff_ne_zero.mp
      ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hrow))

theorem exists_rank_minor {K m n : Type*} [Field K] [Fintype m] [Fintype n]
    (A : Matrix m n K) :
    ∃ (r : Fin A.rank → m) (c : Fin A.rank → n), (A.submatrix r c).det ≠ 0 := by
  classical
  rw [A.rank_eq_finrank_span_row]
  obtain ⟨b, hbmem, _, hbli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range A.row)
  choose r hr using hbmem
  let B := A.submatrix r id
  have hrow : LinearIndependent K B.row := by
    have he : B.row = b := by
      funext i
      exact hr i
    rw [he]
    exact hbli
  have hspan : Submodule.span K (Set.range B.transpose.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row, Matrix.rank_transpose, hrow.rank_matrix,
      Module.finrank_pi]
  obtain ⟨c, _, hc⟩ := exists_row_minor_det_ne_zero B.transpose.row hspan
  refine ⟨r, c, ?_⟩
  have he : (fun i j => B.transpose.row (c i) j) = (A.submatrix r c).transpose := rfl
  rwa [he, Matrix.det_transpose] at hc

theorem rank_specialization_le {R K L m n : Type*}
    [CommRing R] [Field K] [Field L] [Fintype m] [Fintype n]
    (φ : R →+* K) (ψ : R →+* L) (hψ : Function.Injective ψ) (A : Matrix m n R) :
    (A.map φ).rank ≤ (A.map ψ).rank := by
  classical
  obtain ⟨r, c, hc⟩ := exists_rank_minor (A.map φ)
  have hφ : φ ((A.submatrix r c).det) ≠ 0 := by
    rw [φ.map_det]
    exact hc
  have hdet : (A.submatrix r c).det ≠ 0 := by
    intro h
    exact hφ (by rw [h, map_zero])
  have hψdet : ψ ((A.submatrix r c).det) ≠ 0 := by
    exact fun h => hdet (hψ (h.trans (map_zero ψ).symm))
  have hminor : ((A.map ψ).submatrix r c).det ≠ 0 := by
    change (ψ.mapMatrix (A.submatrix r c)).det ≠ 0
    rw [← ψ.map_det]
    exact hψdet
  have heq := Matrix.rank_of_det_ne_zero hminor
  simpa only [Fintype.card_fin] using
    heq.symm.le.trans (Matrix.rank_submatrix_le (A.map ψ) r c)

theorem rank_polynomial_eval_le {K m n : Type*} [Field K]
    [Fintype m] [Fintype n] (A : Matrix m n (Polynomial K)) (a : K) :
    (A.map (Polynomial.evalRingHom a)).rank ≤
      (A.map (algebraMap (Polynomial K) (RatFunc K))).rank :=
  rank_specialization_le _ _ (RatFunc.algebraMap_injective K) A



theorem finrank_homogeneousSubmodule {σ K : Type*} [Fintype σ] [Field K] (n : ℕ) :
    Module.finrank K (MvPolynomial.homogeneousSubmodule σ K n) =
      (Fintype.card σ + n - 1).choose n := by
  classical
  let e : Sym σ n ≃ {d : σ →₀ ℕ // d.degree = n} := Sym.equivNatSum σ n
  let : Fintype {d : σ →₀ ℕ // d.degree = n} := Fintype.ofEquiv (Sym σ n) e
  rw [Module.finrank_eq_card_basis (WeightedTorusJets.homogeneousMonomialBasis σ K n)]
  exact (Fintype.card_congr e).symm.trans (Sym.card_sym_eq_choose n)

end WeightedTorusJets.Geometry

namespace WeightedTorusJets

open MvPolynomial

theorem deformed_macaulay_generic_rank_ge
    {σ K : Type*} [Field K] [Fintype σ]
    (f : σ → MvPolynomial σ K) (d n : ℕ)
    [Fintype {a : σ →₀ ℕ // a.degree = n}]
    [Fintype {b : σ →₀ ℕ // b.degree + d = n}] :
    (macaulayMatrix d n (fun i => (X i : MvPolynomial σ K) ^ d)).rank ≤
      (macaulayMatrix d n (fun i =>
        map (algebraMap (Polynomial K) (RatFunc K))
          (homogeneousDeformation f d i))).rank := by
  have h := Geometry.rank_polynomial_eval_le
    (macaulayMatrix d n (homogeneousDeformation f d)) (1 : K)
  rwa [deformed_macaulay_at_one, macaulayMatrix_map] at h

end WeightedTorusJets
namespace WeightedTorusJets

open MvPolynomial Geometry.GradedQuotient

theorem finrank_degreePiece_deformed_le_pure_powers
    {σ K : Type*} [Fintype σ] [Field K]
    (f : σ → MvPolynomial σ K) (d n : ℕ) :
    Module.finrank (RatFunc K)
        (degreePiece (Ideal.span (Set.range (fun i =>
          map (algebraMap (Polynomial K) (RatFunc K))
            (homogeneousDeformation f d i)))) n) ≤
      Module.finrank K
        (degreePiece (Ideal.span (Set.range (fun i => (X i : MvPolynomial σ K) ^ d))) n) := by
  let := monomialDegreeFintype σ n
  let := monomialSourceFintype σ n d
  have hG (i : σ) :
      (map (algebraMap (Polynomial K) (RatFunc K))
        (homogeneousDeformation f d i)).IsHomogeneous d :=
    (homogeneousComponent_isHomogeneous d (polynomialDeformation f d i)).map _
  rw [finrank_degreePiece_span_eq_sub_macaulayMatrix_rank d n _ hG,
    finrank_degreePiece_span_eq_sub_macaulayMatrix_rank d n _ (fun i => isHomogeneous_X_pow i d),
    Geometry.finrank_homogeneousSubmodule, Geometry.finrank_homogeneousSubmodule]
  exact Nat.sub_le_sub_left (deformed_macaulay_generic_rank_ge f d n) _

end WeightedTorusJets

noncomputable section

open scoped BigOperators DirectSum
open MvPolynomial

namespace WeightedTorusJets.Geometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem homogeneous_quotient_coeLinearMap_injective
    {K σ : Type*} [Field K] (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K)) (N : ℕ) :
    Function.Injective (DirectSum.coeLinearMap
      (fun i : Fin N => (homogeneousSubmodule σ K (i : ℕ)).map
        (Ideal.Quotient.mkₐ K I).toLinearMap)) := by
  classical
  let A (i : Fin N) := (homogeneousSubmodule σ K (i : ℕ)).map
    (Ideal.Quotient.mkₐ K I).toLinearMap
  let q := Ideal.Quotient.mkₐ K I
  change Function.Injective (DirectSum.coeLinearMap A)
  suffices hk : ∀ x : ⨁ i, A i, DirectSum.coeLinearMap A x = 0 → x = 0 by
    intro x y hxy
    exact sub_eq_zero.mp (hk (x - y) (by simp only [map_sub, hxy, sub_self]))
  intro x hx
  have hxsum : (∑ i : Fin N, (x i : MvPolynomial σ K ⧸ I)) = 0 := by
    rw [_root_.DirectSum.coeLinearMap_eq_dfinsuppSum,
      DFinsupp.sum_of_support_subset (Finset.subset_univ _) (fun _ _ => rfl)] at hx
    exact hx
  have hlift (i : Fin N) : ∃ p : MvPolynomial σ K,
      p ∈ homogeneousSubmodule σ K (i : ℕ) ∧ q p = (x i : MvPolynomial σ K ⧸ I) :=
    (x i).property
  choose p hp hpx using hlift
  have hsum : (∑ i, p i) ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (∑ i, p i) = 0
    rw [map_sum]
    simpa only [hpx] using hxsum
  apply DFinsupp.ext
  intro i
  apply Subtype.ext
  change (x i : MvPolynomial σ K ⧸ I) = 0
  rw [← hpx i]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hmem := homogeneousComponent_mem_of_mem hI hsum (i : ℕ)
  have heq : homogeneousComponent (i : ℕ) (∑ j : Fin N, p j) = p i := by
    rw [map_sum]
    simp_rw [homogeneousComponent_of_mem (hp _)]
    simp [Fin.val_inj]
  rwa [heq] at hmem

open MvPolynomial
open scoped DirectSum

variable {K σ : Type*} [Field K] [Finite σ]

theorem quotient_finrank_le_sum_homogeneous_images
    (I : Ideal (MvPolynomial σ K)) (N : ℕ)
    (hzero : ∀ n, N ≤ n →
      (homogeneousSubmodule σ K n).map (Ideal.Quotient.mkₐ K I).toLinearMap = ⊥) :
    Module.Finite K (MvPolynomial σ K ⧸ I) ∧
      Module.finrank K (MvPolynomial σ K ⧸ I) ≤
        ∑ i : Fin N, Module.finrank K
          ((homogeneousSubmodule σ K (i : ℕ)).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
  classical
  let q := Ideal.Quotient.mkₐ K I
  let A (i : Fin N) := (homogeneousSubmodule σ K (i : ℕ)).map q.toLinearMap
  have hfinite (i : Fin N) : Module.Finite K (A i) := by
    have : Module.Finite K (homogeneousSubmodule σ K (i : ℕ)) :=
      Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg σ K (i : ℕ))
    exact Module.Finite.map _ _
  have hspan : (⨆ i, A i) = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective K I x
    change q f ∈ ⨆ i, A i
    rw [← sum_homogeneousComponent f, map_sum]
    apply Submodule.sum_mem
    intro n _
    by_cases hn : n < N
    · apply (le_iSup A ⟨n, hn⟩)
      exact Submodule.mem_map_of_mem (homogeneousComponent_mem n f)
    · have hz : q (homogeneousComponent n f) = 0 := by
        have hm := Submodule.mem_map_of_mem (f := q.toLinearMap) (homogeneousComponent_mem n f)
        rw [hzero n (Nat.le_of_not_gt hn)] at hm
        exact hm
      simpa only [hz] using (⨆ i, A i).zero_mem
  have hsurj : Function.Surjective (DirectSum.coeLinearMap A) := by
    rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap, hspan]
  have hfiniteQ := Module.Finite.of_surjective (DirectSum.coeLinearMap A) hsurj
  refine ⟨hfiniteQ, ?_⟩
  have heq := Module.finrank_directSum (R := K) (fun i : Fin N => A i)
  exact (LinearMap.finrank_le_finrank_of_surjective hsurj).trans_eq heq

theorem quotient_finrank_le_of_homogeneous_image_finrank_le
    {L τ : Type*} [Field L] [Finite τ]
    (I : Ideal (MvPolynomial σ K)) (J : Ideal (MvPolynomial τ L))
    (hJ : J.IsHomogeneous (homogeneousSubmodule τ L)) (N : ℕ)
    (hcut : ∀ n, N ≤ n →
      (homogeneousSubmodule τ L n).map (Ideal.Quotient.mkₐ L J).toLinearMap = ⊥)
    (hle : ∀ n, Module.finrank K
      ((homogeneousSubmodule σ K n).map (Ideal.Quotient.mkₐ K I).toLinearMap) ≤
      Module.finrank L
        ((homogeneousSubmodule τ L n).map (Ideal.Quotient.mkₐ L J).toLinearMap)) :
    Module.Finite K (MvPolynomial σ K ⧸ I) ∧
      Module.finrank K (MvPolynomial σ K ⧸ I) ≤
        Module.finrank L (MvPolynomial τ L ⧸ J) := by
  classical
  have hfiniteI (n : ℕ) : Module.Finite K
      ((homogeneousSubmodule σ K n).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
    have : Module.Finite K (homogeneousSubmodule σ K n) :=
      Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg σ K n)
    exact Module.Finite.map _ _
  have hfiniteJ (n : ℕ) : Module.Finite L
      ((homogeneousSubmodule τ L n).map (Ideal.Quotient.mkₐ L J).toLinearMap) := by
    have : Module.Finite L (homogeneousSubmodule τ L n) :=
      Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg τ L n)
    exact Module.Finite.map _ _
  have hcutI (n : ℕ) (hn : N ≤ n) :
      (homogeneousSubmodule σ K n).map (Ideal.Quotient.mkₐ K I).toLinearMap = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    have hz := congrArg (fun V : Submodule L (MvPolynomial τ L ⧸ J) => Module.finrank L V)
      (hcut n hn)
    rw [finrank_bot] at hz
    exact Nat.eq_zero_of_le_zero ((hle n).trans_eq hz)
  obtain ⟨hIfin, hIbound⟩ := quotient_finrank_le_sum_homogeneous_images I N hcutI
  have : Module.Finite L (MvPolynomial τ L ⧸ J) :=
    (quotient_finrank_le_sum_homogeneous_images J N hcut).1
  have hsumJ : (∑ i : Fin N, Module.finrank L
      ((homogeneousSubmodule τ L (i : ℕ)).map (Ideal.Quotient.mkₐ L J).toLinearMap)) ≤
        Module.finrank L (MvPolynomial τ L ⧸ J) := by
    have hinj := homogeneous_quotient_coeLinearMap_injective J hJ N
    have heq := Module.finrank_directSum (R := L) (fun i : Fin N =>
      (homogeneousSubmodule τ L (i : ℕ)).map (Ideal.Quotient.mkₐ L J).toLinearMap)
    rw [← heq]
    exact LinearMap.finrank_le_finrank_of_injective hinj
  refine ⟨hIfin, hIbound.trans ((Finset.sum_le_sum ?_).trans hsumJ)⟩
  intro i _
  exact hle i

open MvPolynomial

theorem finrank_rectangularQuotient {σ K : Type*} [Fintype σ] [Field K] (k : σ → ℕ) :
    Module.finrank K (MvPolynomial σ K ⧸ rectangularIdeal k) = ∏ i, k i := by
  classical
  rw [Module.finrank_eq_card_basis (rectangularQuotientBasis k)]
  simp

open MvPolynomial

theorem homogeneous_mem_rectangularIdeal {σ K : Type*} [Fintype σ] [CommRing K]
    (k : σ → ℕ) {p : MvPolynomial σ K} {n : ℕ}
    (hp : p.IsHomogeneous n) (hn : (∑ i, (k i - 1)) < n) :
    p ∈ rectangularIdeal k := by
  classical
  apply (mem_rectangularIdeal k p).mpr
  intro d hd
  by_contra h
  push Not at h
  have hsum : (∑ i, d i) ≤ ∑ i, (k i - 1) :=
    Finset.sum_le_sum fun i _ => Nat.le_pred_of_lt (h i)
  have hdegree : n = ∑ i, d i := by
    simpa only [← Finsupp.degree_apply, Finsupp.degree_eq_sum] using
      hp.degree_eq_sum_deg_support hd
  omega

theorem rectangular_homogeneous_image_eq_bot {σ K : Type*} [Fintype σ] [CommRing K]
    (k : σ → ℕ) (n : ℕ) (hn : (∑ i, (k i - 1)) < n) :
    (homogeneousSubmodule σ K n).map
      (Ideal.Quotient.mkₐ K (rectangularIdeal k)).toLinearMap = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
  change Ideal.Quotient.mk (rectangularIdeal k) p = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact homogeneous_mem_rectangularIdeal k
    ((mem_homogeneousSubmodule n p).mp hp) hn

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

theorem rectangularIdeal_isHomogeneous {σ K : Type*} [CommRing K] (k : σ → ℕ) :
    (rectangularIdeal k : Ideal (MvPolynomial σ K)).IsHomogeneous
      (homogeneousSubmodule σ K) := by
  apply Ideal.homogeneous_span (homogeneousSubmodule σ K)
  rintro _ ⟨i, rfl⟩
  exact ⟨k i, isHomogeneous_X_pow i (k i)⟩

theorem quotient_finrank_le_prod_of_homogeneous_image_le_rectangular
    {L τ : Type*} [Field L] [Fintype τ]
    (I : Ideal (MvPolynomial σ K)) (k : τ → ℕ)
    (hle : ∀ n, Module.finrank K
      ((homogeneousSubmodule σ K n).map (Ideal.Quotient.mkₐ K I).toLinearMap) ≤
      Module.finrank L ((homogeneousSubmodule τ L n).map
        (Ideal.Quotient.mkₐ L (rectangularIdeal k)).toLinearMap)) :
    Module.Finite K (MvPolynomial σ K ⧸ I) ∧
      Module.finrank K (MvPolynomial σ K ⧸ I) ≤ ∏ i, k i := by
  have h := quotient_finrank_le_of_homogeneous_image_finrank_le I
    (rectangularIdeal k : Ideal (MvPolynomial τ L)) (rectangularIdeal_isHomogeneous k)
    ((∑ i, (k i - 1)) + 1)
    (fun n hn => rectangular_homogeneous_image_eq_bot k n (Nat.lt_of_succ_le hn)) hle
  simpa only [finrank_rectangularQuotient] using h

end WeightedTorusJets.Geometry

end
end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_LocalFractionAlgebra
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
open scoped BigOperators
open Module
open MvPolynomial
noncomputable section
noncomputable section
open scoped BigOperators DirectSum
open MvPolynomial
namespace WeightedTorusJets

open MvPolynomial

theorem generic_homogeneous_deformation_quotient_bound
    {σ K : Type*} [Fintype σ] [Field K]
    (f : σ → MvPolynomial σ K) (d : ℕ) :
    Module.Finite (RatFunc K)
        (MvPolynomial σ (RatFunc K) ⧸ Ideal.span (Set.range (fun i =>
          map (algebraMap (Polynomial K) (RatFunc K)) (homogeneousDeformation f d i)))) ∧
      Module.finrank (RatFunc K)
        (MvPolynomial σ (RatFunc K) ⧸ Ideal.span (Set.range (fun i =>
          map (algebraMap (Polynomial K) (RatFunc K)) (homogeneousDeformation f d i)))) ≤
        d ^ Fintype.card σ := by
  classical
  have h := Geometry.quotient_finrank_le_prod_of_homogeneous_image_le_rectangular
    (L := K)
    (Ideal.span (Set.range (fun i =>
      map (algebraMap (Polynomial K) (RatFunc K)) (homogeneousDeformation f d i))))
    (fun _ : σ => d) (fun n => by
      exact finrank_degreePiece_deformed_le_pure_powers f d n)
  simpa only [Finset.prod_const, Finset.card_univ] using h

end WeightedTorusJets

namespace WeightedTorusJets.Geometry

open MvPolynomial

theorem exists_lift_of_mem_leadingFormIdeal {ι σ K : Type*} [Fintype ι] [CommRing K]
    (f : ι → MvPolynomial σ K) (D : ℕ) (hf : ∀ i, (f i).totalDegree ≤ D)
    (p : MvPolynomial σ K) (n : ℕ) (hp : p.IsHomogeneous n)
    (hmem : p ∈ Ideal.span (Set.range fun i => homogeneousComponent D (f i))) :
    ∃ q ∈ Ideal.span (Set.range f), q.totalDegree ≤ n ∧ homogeneousComponent n q = p := by
  classical
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (MvPolynomial σ K)).mp hmem
  have ha : ∑ i, a i * homogeneousComponent D (f i) = p := by
    simpa only [smul_eq_mul] using ha
  by_cases hDn : D ≤ n
  · have hright (i : ι) : homogeneousComponent n (a i * homogeneousComponent D (f i)) =
        homogeneousComponent (n - D) (a i) * homogeneousComponent D (f i) := by
      rw [mul_comm (a i), GradedQuotient.homogeneousComponent_mul_of_le
        (homogeneousComponent_isHomogeneous D (f i)) hDn, mul_comm]
    have hleft (i : ι) : homogeneousComponent n (homogeneousComponent (n - D) (a i) * f i) =
        homogeneousComponent (n - D) (a i) * homogeneousComponent D (f i) := by
      rw [GradedQuotient.homogeneousComponent_mul_of_le
        (homogeneousComponent_isHomogeneous (n - D) (a i)) (Nat.sub_le n D),
        Nat.sub_sub_self hDn]
    have he : ∑ i, homogeneousComponent (n - D) (a i) * homogeneousComponent D (f i) = p := by
      simpa only [map_sum, hright, homogeneousComponent_eq_self hp] using
        congrArg (homogeneousComponent n) ha
    refine ⟨∑ i, homogeneousComponent (n - D) (a i) * f i, ?_, ?_, ?_⟩
    · exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    · exact totalDegree_finsetSum_le fun i _ => (totalDegree_mul _ _).trans
        ((Nat.add_le_add (homogeneousComponent_isHomogeneous (n - D) (a i)).totalDegree_le
          (hf i)).trans_eq (Nat.sub_add_cancel hDn))
    · simpa only [map_sum, hleft] using he
  · have hz (i : ι) : homogeneousComponent n (a i * homogeneousComponent D (f i)) = 0 := by
      rw [mul_comm, GradedQuotient.homogeneousComponent_mul_of_lt
        (homogeneousComponent_isHomogeneous D (f i)) (Nat.lt_of_not_ge hDn)]
    have he : p = 0 := by
      have h := congrArg (homogeneousComponent n) ha
      simpa only [map_sum, hz, Finset.sum_const_zero, homogeneousComponent_eq_self hp] using h.symm
    exact ⟨0, Ideal.zero_mem _, by simp, by simp [he]⟩

theorem homogeneousComponent_mem_leadingFormIdeal {ι σ K : Type*} [CommRing K]
    (f : ι → MvPolynomial σ K) (D : ℕ) (p : MvPolynomial σ K)
    (hp : p ∈ Ideal.span (Set.range fun i => homogeneousComponent D (f i))) (n : ℕ) :
    homogeneousComponent n p ∈ Ideal.span (Set.range fun i => homogeneousComponent D (f i)) := by
  let : GradedAlgebra (homogeneousSubmodule σ K) := MvPolynomial.gradedAlgebra
  apply homogeneousComponent_mem_of_mem _ hp n
  apply Ideal.homogeneous_span
  rintro g ⟨i, rfl⟩
  exact ⟨D, homogeneousComponent_isHomogeneous D (f i)⟩

theorem eq_zero_or_totalDegree_lt_of_homogeneousComponent_eq_zero {σ K : Type*} [CommRing K]
    (p : MvPolynomial σ K) (n : ℕ) (hp : p.totalDegree ≤ n)
    (hn : homogeneousComponent n p = 0) : p = 0 ∨ p.totalDegree < n := by
  classical
  by_cases hn0 : n = 0
  · left
    subst n
    have hhom : p.IsHomogeneous 0 :=
      (totalDegree_zero_iff_isHomogeneous σ).mp (Nat.eq_zero_of_le_zero hp)
    simpa only [homogeneousComponent_eq_self hhom] using hn
  · right
    rw [totalDegree, Finset.sup_lt_iff (Nat.pos_of_ne_zero hn0)]
    intro d hd
    have hdle : d.degree ≤ n := (le_totalDegree hd).trans hp
    apply lt_of_le_of_ne hdle
    intro he
    have hz := congrArg (fun q : MvPolynomial σ K => q.coeff d) hn
    have hdne := mem_support_iff.mp hd
    exact hdne (by simpa [coeff_homogeneousComponent, he] using hz)

theorem representatives_of_homogeneous_lifts {σ K : Type*} [CommRing K]
    (I J : Ideal (MvPolynomial σ K)) (S : Submodule K (MvPolynomial σ K))
    (hS : ∀ p ∈ S, ∀ n, homogeneousComponent n p ∈ S)
    (hJ : ∀ p ∈ J, ∀ n, homogeneousComponent n p ∈ J)
    (hlift : ∀ (p : MvPolynomial σ K) (n : ℕ), p.IsHomogeneous n → p ∈ J →
      ∃ q ∈ I, q.totalDegree ≤ n ∧ homogeneousComponent n q = p)
    (hrep : ∀ p : MvPolynomial σ K, ∃ s ∈ S, p - s ∈ J) :
    ∀ p : MvPolynomial σ K, ∃ s ∈ S, p - s ∈ I := by
  have H : ∀ n : ℕ, ∀ p : MvPolynomial σ K, p.totalDegree ≤ n →
      ∃ s ∈ S, p - s ∈ I := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hp
      obtain ⟨s, hs, hps⟩ := hrep (homogeneousComponent n p)
      let t := homogeneousComponent n s
      have htS : t ∈ S := hS s hs n
      have htHom : t.IsHomogeneous n := homogeneousComponent_isHomogeneous n s
      have hptHom : (homogeneousComponent n p - t).IsHomogeneous n :=
        (homogeneousComponent_isHomogeneous n p).sub htHom
      have hptJ : homogeneousComponent n p - t ∈ J := by
        simpa only [map_sub,
          homogeneousComponent_eq_self (homogeneousComponent_isHomogeneous n p)] using hJ _ hps n
      obtain ⟨q, hqI, hqdeg, hqtop⟩ := hlift _ n hptHom hptJ
      let r := p - t - q
      have hrdeg : r.totalDegree ≤ n :=
        (totalDegree_sub _ _).trans (max_le
          ((totalDegree_sub _ _).trans (max_le hp htHom.totalDegree_le)) hqdeg)
      have hrtop : homogeneousComponent n r = 0 := by
        simp only [r, map_sub, homogeneousComponent_eq_self htHom, hqtop, sub_self]
      rcases eq_zero_or_totalDegree_lt_of_homogeneousComponent_eq_zero r n hrdeg hrtop with hr | hr
      · refine ⟨t, htS, ?_⟩
        have he : p - t = q := sub_eq_zero.mp hr
        rwa [he]
      · obtain ⟨u, huS, hruI⟩ := ih r.totalDegree hr r le_rfl
        refine ⟨t + u, S.add_mem htS huS, ?_⟩
        have he : p - (t + u) = (r - u) + q := by dsimp [r]; abel
        rw [he]
        exact I.add_mem hruI hqI
  intro p
  exact H p.totalDegree p le_rfl

end WeightedTorusJets.Geometry

open Module

namespace WeightedTorusJets

theorem exists_monomial_basis_quotient
    {K σ : Type*} [Field K] (J : Ideal (MvPolynomial σ K))
    [Module.Finite K (MvPolynomial σ K ⧸ J)] :
    ∃ m : Fin (finrank K (MvPolynomial σ K ⧸ J)) → (σ →₀ ℕ),
      LinearIndependent K (fun i => Ideal.Quotient.mk J (MvPolynomial.monomial (m i) 1)) ∧
      Submodule.span K (Set.range fun i =>
        Ideal.Quotient.mk J (MvPolynomial.monomial (m i) 1)) = ⊤ := by
  classical
  let v := fun m : σ →₀ ℕ => Ideal.Quotient.mk J (MvPolynomial.monomial m 1)
  let f := (Ideal.Quotient.mkₐ K J).toLinearMap
  have hspan : Submodule.span K (Set.range v) = ⊤ := by
    have h := congrArg (Submodule.map f) (MvPolynomial.basisMonomials σ K).span_eq
    rw [Submodule.map_span, Submodule.map_top,
      LinearMap.range_eq_top.mpr (Ideal.Quotient.mkₐ_surjective K J)] at h
    simpa [← Set.range_comp, MvPolynomial.coe_basisMonomials, Function.comp_def, f, v] using h
  obtain ⟨b, hb, hbspan, hblin⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range v)
  choose m hm using hb
  have hdim : finrank K (Submodule.span K (Set.range v)) =
      finrank K (MvPolynomial σ K ⧸ J) := by rw [hspan, finrank_top]
  let e := finCongr hdim.symm
  have hrows : (fun i => v (m (e i))) = b ∘ e := by
    funext i
    exact hm (e i)
  refine ⟨m ∘ e, ?_, ?_⟩
  · change LinearIndependent K (fun i => v (m (e i)))
    rw [hrows]
    exact hblin.comp e e.injective
  · change Submodule.span K (Set.range fun i => v (m (e i))) = ⊤
    rw [hrows, e.surjective.range_comp, hbspan, hspan]

end WeightedTorusJets

namespace WeightedTorusJets.Geometry

open MvPolynomial

theorem homogeneousComponent_mem_span_monomials {τ σ K : Type*} [CommRing K]
    (m : τ → (σ →₀ ℕ)) (p : MvPolynomial σ K)
    (hp : p ∈ Submodule.span K (Set.range fun i => monomial (m i) (1 : K))) (n : ℕ) :
    homogeneousComponent n p ∈ Submodule.span K (Set.range fun i => monomial (m i) (1 : K)) := by
  classical
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨i, rfl⟩ := hp
      rw [homogeneousComponent_of_mem (isHomogeneous_monomial (1 : K) rfl)]
      split_ifs
      · exact Submodule.subset_span ⟨i, rfl⟩
      · exact Submodule.zero_mem _
  | zero => simpa only [map_zero] using (Submodule.zero_mem _)
  | add p q hp hq hp' hq' => simpa only [map_add] using Submodule.add_mem _ hp' hq'
  | smul c p hp hp' => simpa only [map_smul] using Submodule.smul_mem _ c hp'

theorem quotient_span_eq_top_iff_representatives {τ σ K : Type*} [CommRing K]
    (J : Ideal (MvPolynomial σ K)) (v : τ → MvPolynomial σ K) :
    Submodule.span K (Set.range fun i => Ideal.Quotient.mk J (v i)) = ⊤ ↔
      ∀ p : MvPolynomial σ K,
        ∃ s ∈ Submodule.span K (Set.range v), p - s ∈ J := by
  let L := (Ideal.Quotient.mkₐ K J).toLinearMap
  have hmap : (Submodule.span K (Set.range v)).map L =
      Submodule.span K (Set.range fun i => Ideal.Quotient.mk J (v i)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [← hmap]
  constructor
  · intro h p
    have hp : L p ∈ (Submodule.span K (Set.range v)).map L := by rw [h]; exact Submodule.mem_top
    obtain ⟨s, hs, he⟩ := Submodule.mem_map.mp hp
    exact ⟨s, hs, Ideal.Quotient.eq.mp he.symm⟩
  · intro h
    apply top_unique
    intro x _
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨s, hs, he⟩ := h p
    exact Submodule.mem_map.mpr ⟨s, hs, (Ideal.Quotient.eq.mpr he).symm⟩

theorem finite_and_finrank_le_leadingFormQuotient {ι σ K : Type*} [Fintype ι] [Field K]
    (f : ι → MvPolynomial σ K) (D : ℕ) (hf : ∀ i, (f i).totalDegree ≤ D)
    [Module.Finite K (MvPolynomial σ K ⧸
      Ideal.span (Set.range fun i => homogeneousComponent D (f i)))] :
    Module.Finite K (MvPolynomial σ K ⧸ Ideal.span (Set.range f)) ∧
      Module.finrank K (MvPolynomial σ K ⧸ Ideal.span (Set.range f)) ≤
        Module.finrank K (MvPolynomial σ K ⧸
          Ideal.span (Set.range fun i => homogeneousComponent D (f i))) := by
  classical
  let J := Ideal.span (Set.range fun i => homogeneousComponent D (f i))
  obtain ⟨m, _, hmspan⟩ := WeightedTorusJets.exists_monomial_basis_quotient J
  have hrepJ := (quotient_span_eq_top_iff_representatives J
    (fun i => monomial (m i) (1 : K))).mp hmspan
  have hrepI := representatives_of_homogeneous_lifts (Ideal.span (Set.range f)) J
    (Submodule.span K (Set.range fun i => monomial (m i) (1 : K)))
    (homogeneousComponent_mem_span_monomials m)
    (homogeneousComponent_mem_leadingFormIdeal f D)
    (exists_lift_of_mem_leadingFormIdeal f D hf) hrepJ
  have hspanI := (quotient_span_eq_top_iff_representatives (Ideal.span (Set.range f))
    (fun i => monomial (m i) (1 : K))).mpr hrepI
  refine ⟨Module.Finite.of_fg_top ?_, ?_⟩
  · rw [← hspanI]
    exact Submodule.fg_span (Set.finite_range _)
  · simpa only [Fintype.card_fin] using finrank_le_of_span_eq_top hspanI

end WeightedTorusJets.Geometry

namespace WeightedTorusJets

open MvPolynomial

theorem polynomialDeformation_totalDegree_le {σ R : Type*} [CommRing R]
    (f : σ → MvPolynomial σ R) (d : ℕ) (hf : ∀ i, (f i).totalDegree ≤ d)
    (i : σ) : (polynomialDeformation f d i).totalDegree ≤ d := by
  have hmap : (map Polynomial.C (f i)).totalDegree ≤ (f i).totalDegree :=
    Finset.sup_mono (support_map_subset _ _)
  unfold polynomialDeformation
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_mul _ _).trans ?_
    simpa only [totalDegree_C, zero_add] using hmap.trans (hf i)
  · refine (totalDegree_mul _ _).trans ?_
    simpa only [totalDegree_C, zero_add] using
      (isHomogeneous_X_pow (R := Polynomial R) i d).totalDegree_le

theorem map_polynomialDeformation_totalDegree_le {σ R S : Type*}
    [CommRing R] [CommRing S] (φ : Polynomial R →+* S)
    (f : σ → MvPolynomial σ R) (d : ℕ) (hf : ∀ i, (f i).totalDegree ≤ d)
    (i : σ) : (map φ (polynomialDeformation f d i)).totalDegree ≤ d := by
  exact (Finset.sup_mono (support_map_subset _ _)).trans
    (polynomialDeformation_totalDegree_le f d hf i)

end WeightedTorusJets

namespace WeightedTorusJets

open MvPolynomial

theorem generic_affine_deformation_quotient_bound
    {σ K : Type*} [Fintype σ] [Field K]
    (f : σ → MvPolynomial σ K) (d : ℕ) (hf : ∀ i, (f i).totalDegree ≤ d) :
    Module.Finite (RatFunc K)
        (MvPolynomial σ (RatFunc K) ⧸ Ideal.span (Set.range (fun i =>
          map (algebraMap (Polynomial K) (RatFunc K)) (polynomialDeformation f d i)))) ∧
      Module.finrank (RatFunc K)
        (MvPolynomial σ (RatFunc K) ⧸ Ideal.span (Set.range (fun i =>
          map (algebraMap (Polynomial K) (RatFunc K)) (polynomialDeformation f d i)))) ≤
        d ^ Fintype.card σ := by
  have htop (i : σ) :
      homogeneousComponent d
          (map (algebraMap (Polynomial K) (RatFunc K)) (polynomialDeformation f d i)) =
        map (algebraMap (Polynomial K) (RatFunc K)) (homogeneousDeformation f d i) := by
    rw [homogeneousDeformation, map_homogeneousComponent]
  have hIdeals := congrArg
    (fun g : σ → MvPolynomial σ (RatFunc K) => Ideal.span (Set.range g)) (funext htop)
  let e := (Ideal.quotientEquivAlgOfEq (RatFunc K) hIdeals).toLinearEquiv
  obtain ⟨hfinite, hbound⟩ := generic_homogeneous_deformation_quotient_bound f d
  let : Module.Finite (RatFunc K)
      (MvPolynomial σ (RatFunc K) ⧸ Ideal.span (Set.range (fun i =>
        map (algebraMap (Polynomial K) (RatFunc K)) (homogeneousDeformation f d i)))) := hfinite
  let : Module.Finite (RatFunc K)
      (MvPolynomial σ (RatFunc K) ⧸ Ideal.span (Set.range (fun i =>
        homogeneousComponent d
          (map (algebraMap (Polynomial K) (RatFunc K)) (polynomialDeformation f d i))))) :=
    Module.Finite.equiv e.symm
  have h := Geometry.finite_and_finrank_le_leadingFormQuotient
    (fun i => map (algebraMap (Polynomial K) (RatFunc K)) (polynomialDeformation f d i)) d
    (map_polynomialDeformation_totalDegree_le _ f d hf)
  exact ⟨h.1, h.2.trans (e.finrank_eq.trans_le hbound)⟩

end WeightedTorusJets

end

section

namespace WeightedTorusJets.Geometry

variable {K : Type*} [Field K]

theorem maximal_polynomial_height (n : ℕ)
    (p : Ideal (MvPolynomial (Fin n) K)) [p.IsMaximal] : p.height = n := by
  induction n with
  | zero =>
    have h := p.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
    have h0 : p.height ≤ 0 := WithBot.coe_le_coe.mp (by simpa using h)
    exact le_antisymm h0 bot_le
  | succ n ih =>
    let e := (MvPolynomial.finSuccEquiv K n).toRingEquiv
    let P : Ideal (Polynomial (MvPolynomial (Fin n) K)) := p.map e
    have : P.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let q : Ideal (MvPolynomial (Fin n) K) := P.comap Polynomial.C
    have : q.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    have : P.LiesOver q := ⟨rfl⟩
    have hq : q.height = n := ih q
    calc
      p.height = P.height := (e.height_map p).symm
      _ = q.height + 1 := Polynomial.height_eq_height_add_one q P
      _ = (n + 1 : ℕ) := by rw [hq]; simp

end WeightedTorusJets.Geometry

end

section

namespace WeightedTorusJets.Deformation

theorem localFractionAlgebra_isScalarTower
    {R F : Type*} [CommRing R] [Field F]
    [Algebra R F] [IsFractionRing R F] (p : Ideal R) [p.IsPrime] :
    let := localFractionAlgebra (F := F) p
    IsScalarTower R (Localization.AtPrime p) F := by
  let := localFractionAlgebra (F := F) p
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change algebraMap R F r = IsLocalization.lift _ (algebraMap R (Localization.AtPrime p) r)
  rw [IsLocalization.lift_eq]

theorem localFractionAlgebra_isFractionRing
    {R F : Type*} [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (p : Ideal R) [p.IsPrime] :
    let := localFractionAlgebra (F := F) p
    IsFractionRing (Localization.AtPrime p) F := by
  let := localFractionAlgebra (F := F) p
  have := localFractionAlgebra_isScalarTower (F := F) p
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl
    (Localization.AtPrime p) F

end WeightedTorusJets.Deformation

end

section

open TensorProduct

namespace WeightedTorusJets.Deformation

theorem surjective_baseChange_localization
    {R F Q B : Type*} [CommRing R] [Field F] [Algebra R F]
    [CommRing Q] [Algebra R Q] [CommRing B] [Algebra R B]
    [Algebra Q B] [IsScalarTower R Q B]
    (M : Submonoid Q) [IsLocalization M B]
    [Module.Finite F (F ⊗[R] Q)] :
    Function.Surjective
      (Algebra.TensorProduct.map (AlgHom.id R F) (IsScalarTower.toAlgHom R Q B)) := by
  let G := F ⊗[R] Q
  let L := F ⊗[R] B
  let : Algebra G L :=
    (Algebra.TensorProduct.map (AlgHom.id R F) (IsScalarTower.toAlgHom R Q B)).toAlgebra
  have : IsScalarTower F G L :=
    .of_algebraMap_eq (by intro x; simp [G, L, RingHom.algebraMap_toAlgebra])
  have : IsLocalization
      (M.map (Algebra.TensorProduct.includeRight (R := R) (A := F))) L :=
    IsLocalization.tensorProduct_tensorProduct_right R F M B
      (by ext; simp [RingHom.algebraMap_toAlgebra])
  have : IsArtinianRing G := isArtinian_of_tower F (inferInstance : IsArtinian F G)
  exact IsArtinianRing.localization_surjective
    (M.map (Algebra.TensorProduct.includeRight (R := R) (A := F))) L

theorem surjective_baseChange_localized_quotient
    {R F P S : Type*} [CommRing R] [Field F] [Algebra R F]
    [CommRing P] [Algebra R P] [CommRing S] [Algebra R S]
    [Algebra P S] [IsScalarTower R P S]
    (M : Submonoid P) [IsLocalization M S] (I : Ideal P)
    [Module.Finite F (F ⊗[R] (P ⧸ I))] :
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id R F)
      (Ideal.quotientMapₐ (I.map (algebraMap P S))
        (IsScalarTower.toAlgHom R P S) Ideal.le_comap_map)) := by
  have : IsScalarTower R (P ⧸ I) (S ⧸ I.map (algebraMap P S)) :=
    .of_algebraMap_eq (by
      intro r
      change Ideal.Quotient.mk _ (algebraMap R S r) =
        Ideal.Quotient.mk _ (algebraMap P S (algebraMap R P r))
      rw [IsScalarTower.algebraMap_apply R P S])
  exact surjective_baseChange_localization (R := R) (F := F)
    (B := S ⧸ I.map (algebraMap P S)) (Algebra.algebraMapSubmonoid (P ⧸ I) M)

end WeightedTorusJets.Deformation

open TensorProduct

end
end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_CoordinateLocalizedPrime
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
section
open scoped BigOperators
open Module
open MvPolynomial
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MvPolynomial

namespace WeightedTorusJets.Geometry.DegreeBezout

theorem ring_length_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) : Module.length A A = Module.length B B := by
  let : Algebra A B := e.toRingHom.toAlgebra
  let f : A ≃ₗ[A] B :=
    { e.toAddEquiv with map_smul' := by intro a b; exact e.map_mul a b }
  rw [← Module.length_eq_of_surjective (M := B) e.surjective]
  exact f.length_eq

theorem quotient_length_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I : Ideal A) (J : Ideal B)
    (hJ : J = I.map e.toRingHom) :
    Module.length A (A ⧸ I) = Module.length B (B ⧸ J) := by
  rw [Module.length_eq_of_surjective (S := A) (R := A ⧸ I) (M := A ⧸ I)
      (Ideal.Quotient.mk_surjective (I := I)),
    Module.length_eq_of_surjective (S := B) (R := B ⧸ J) (M := B ⧸ J)
      (Ideal.Quotient.mk_surjective (I := J))]
  exact ring_length_eq_of_ringEquiv (Ideal.quotientEquiv I J e hJ)

end WeightedTorusJets.Geometry.DegreeBezout

namespace WeightedTorusJets.Geometry

theorem radical_map_ringEquiv_eq_maximalIdeal
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) (I : Ideal A)
    (hI : I.radical = IsLocalRing.maximalIdeal A) :
    (I.map e.toRingHom).radical = IsLocalRing.maximalIdeal B := by
  have hk : RingHom.ker e.toRingHom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot e.toRingHom).mp e.injective
  rw [← Ideal.map_radical_of_surjective e.surjective
    (hk ▸ bot_le), hI]
  exact IsLocalRing.map_ringEquiv_maximalIdeal e

theorem map_span_range_of_commuting_images
    {A B ι : Type*} [CommRing A] [CommRing B]
    (e : A →+* B) (f : ι → A) (g : ι → B) (h : ∀ i, e (f i) = g i) :
    (Ideal.span (Set.range f)).map e = Ideal.span (Set.range g) := by
  rw [Ideal.map_span, ← Set.range_comp]
  congr 1
  exact congrArg Set.range (funext h)

theorem quotient_length_eq_of_commuting_images
    {A B ι : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (f : ι → A) (g : ι → B) (h : ∀ i, e (f i) = g i) :
    Module.length A (A ⧸ Ideal.span (Set.range f)) =
      Module.length B (B ⧸ Ideal.span (Set.range g)) := by
  exact DegreeBezout.quotient_length_eq_of_ringEquiv e _ _
    (map_span_range_of_commuting_images e.toRingHom f g h).symm

theorem radical_span_eq_maximalIdeal_of_commuting_images
    {A B ι : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) (f : ι → A) (g : ι → B) (h : ∀ i, e (f i) = g i)
    (hf : (Ideal.span (Set.range f)).radical = IsLocalRing.maximalIdeal A) :
    (Ideal.span (Set.range g)).radical = IsLocalRing.maximalIdeal B := by
  rw [← map_span_range_of_commuting_images e.toRingHom f g h]
  exact radical_map_ringEquiv_eq_maximalIdeal e _ hf



universe u v w

end WeightedTorusJets.Geometry

noncomputable section

namespace WeightedTorusJets.Geometry.DegreeBezout

open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {K σ ι τ : Type*} [CommRing K]

theorem normalizationPresentation_coefficient_comap_eq_bot
    (e : MvPolynomial (ι ⊕ τ) K ≃ₐ[K] MvPolynomial σ K)
    (P : Ideal (MvPolynomial σ K))
    (g : MvPolynomial ι K →ₐ[K] (MvPolynomial σ K ⧸ P))
    (hginj : Function.Injective g)
    (hg : ∀ i, g (X i) = Ideal.Quotient.mk P (e (X (Sum.inl i)))) :
    (P.comap (normalizationPresentation e).symm.toRingHom).comap C = ⊥ := by
  apply bot_unique
  intro b hb
  apply hginj
  rw [map_zero, ← normalizationPresentation_coefficient_map e P g hg b]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hb

theorem finite_normalizationPresentation_quotient
    (e : MvPolynomial (ι ⊕ τ) K ≃ₐ[K] MvPolynomial σ K)
    (P : Ideal (MvPolynomial σ K))
    (g : MvPolynomial ι K →ₐ[K] (MvPolynomial σ K ⧸ P))
    (hg : ∀ i, g (X i) = Ideal.Quotient.mk P (e (X (Sum.inl i))))
    (hfinite : letI := g.toAlgebra
      letI : Module (MvPolynomial ι K) (MvPolynomial σ K ⧸ P) := Algebra.toModule
      Module.Finite (MvPolynomial ι K) (MvPolynomial σ K ⧸ P)) :
    Module.Finite (MvPolynomial ι K)
      (MvPolynomial τ (MvPolynomial ι K) ⧸
        P.comap (normalizationPresentation e).symm.toRingHom) := by
  let := g.toAlgebra
  let : Module (MvPolynomial ι K) (MvPolynomial σ K ⧸ P) := Algebra.toModule
  have : Module.Finite (MvPolynomial ι K) (MvPolynomial σ K ⧸ P) := hfinite
  exact Module.Finite.equiv (normalizationPresentationQuotientEquiv e P g hg).symm.toLinearEquiv

end WeightedTorusJets.Geometry.DegreeBezout

end
end
end
end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_ResidueTensorQuotientAlgEquiv
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
open scoped BigOperators
open Module
open MvPolynomial
noncomputable section
section
open TensorProduct
open TensorProduct
namespace WeightedTorusJets.Deformation

open TensorProduct

theorem exists_surjective_global_polynomial_quotient_to_local_generic_fiber
    {R A F S σ ι : Type*} [CommRing R] [CommRing A] [Field F] [CommRing S]
    [Algebra R A] [Algebra R F] [Algebra A F] [IsScalarTower R A F]
    [Algebra R S] [Algebra A S] [IsScalarTower R A S]
    [Algebra (MvPolynomial σ R) S] [IsScalarTower R (MvPolynomial σ R) S]
    (M : Submonoid R) [IsLocalization M A]
    (N : Submonoid (MvPolynomial σ R)) [IsLocalization N S]
    (f : ι → MvPolynomial σ R)
    [Module.Finite F (MvPolynomial σ F ⧸ Ideal.span
      (Set.range (fun i => MvPolynomial.map (algebraMap R F) (f i))))] :
    ∃ π : (MvPolynomial σ F ⧸ Ideal.span
        (Set.range (fun i => MvPolynomial.map (algebraMap R F) (f i)))) →ₗ[F]
        F ⊗[A] (S ⧸ Ideal.span
          (Set.range (fun i => algebraMap (MvPolynomial σ R) S (f i)))),
      Function.Surjective π ∧ ∀ p : MvPolynomial σ R,
        π (Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R F) p)) =
          1 ⊗ₜ[A] Ideal.Quotient.mk _ (algebraMap (MvPolynomial σ R) S p) := by
  let I := Ideal.span (Set.range f)
  let E := mvPolynomialSpanQuotientBaseChange (A := F) f
  have : Module.Finite F (F ⊗[R] (MvPolynomial σ R ⧸ I)) :=
    Module.Finite.equiv E.symm.toLinearEquiv
  let qmap := Ideal.quotientMapₐ (I.map (algebraMap (MvPolynomial σ R) S))
    (IsScalarTower.toAlgHom R (MvPolynomial σ R) S) Ideal.le_comap_map
  let Tmap := Algebra.TensorProduct.map (AlgHom.id F F) qmap
  have hT : Function.Surjective Tmap :=
    surjective_baseChange_localized_quotient (R := R) (F := F)
      (P := MvPolynomial σ R) (S := S) N I
  let EB := genericFiberLocalBaseEquiv (A := A) (F := F)
    (B := S ⧸ I.map (algebraMap (MvPolynomial σ R) S)) M
  let EJ := Ideal.quotientEquivAlgOfEq A
    (show I.map (algebraMap (MvPolynomial σ R) S) =
      Ideal.span (Set.range (fun i => algebraMap (MvPolynomial σ R) S (f i))) by
        dsimp only [I]
        rw [Ideal.map_span, ← Set.range_comp'])
  let ET := Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) EJ
  let π := ET.toLinearEquiv.toLinearMap.comp (EB.symm.toLinearEquiv.toLinearMap.comp
    (Tmap.toLinearMap.comp E.symm.toLinearEquiv.toLinearMap))
  refine ⟨π, ET.surjective.comp (EB.symm.surjective.comp (hT.comp E.symm.surjective)), ?_⟩
  intro p
  simp only [π, LinearMap.comp_apply, LinearEquiv.coe_coe,
    E, AlgEquiv.toLinearEquiv_apply,
    mvPolynomialSpanQuotientBaseChange_symm_mk_map]
  change ET (EB.symm (Tmap (1 ⊗ₜ[R] Ideal.Quotient.mk I p))) = _
  simp only [Tmap, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    qmap]
  change ET (1 ⊗ₜ[A] Ideal.Quotient.mk _ (algebraMap (MvPolynomial σ R) S p)) = _
  simp only [ET, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    AlgEquiv.coe_toAlgHom, EJ, Ideal.quotientEquivAlgOfEq_mk]
  rfl

end WeightedTorusJets.Deformation

end

section

namespace WeightedTorusJets.Deformation

theorem finiteLength_quotient_of_radical_eq_maximalIdeal
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hrad : I.radical = IsLocalRing.maximalIdeal R) :
    IsFiniteLength R (R ⧸ I) := by
  have hI : I ≠ ⊤ := by
    intro h
    have := congrArg (fun J : Ideal R => J.radical) h
    rw [hrad, Ideal.radical_top] at this
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top this
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmax : (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I) =
      IsLocalRing.maximalIdeal (R ⧸ I) := by
    apply IsLocalRing.eq_maximalIdeal
    exact Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by simpa only [Ideal.mk_ker] using IsLocalRing.le_maximalIdeal hI)
  have hart : IsArtinianRing (R ⧸ I) := by
    apply (isArtinianRing_iff_isNilpotent_maximalIdeal (R ⧸ I)).mpr
    obtain ⟨n, hn⟩ := I.exists_radical_pow_le_of_fg (Ideal.fg_of_isNoetherianRing _)
    refine ⟨n, ?_⟩
    rw [← hmax, ← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker,
      Ideal.mk_ker]
    rwa [hrad] at hn
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨isNoetherian_quotient I,
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))⟩

theorem finite_of_finiteLength_of_finite_residue
    {K R M : Type*} [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]
    [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
    [Module.Finite K (IsLocalRing.ResidueField R)] (hM : IsFiniteLength R M) :
    Module.Finite K M := by
  have hres : Module.length (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField R) ≠ ⊤ := by
    rw [← Module.length_eq_of_surjective (M := IsLocalRing.ResidueField R)
      (IsLocalRing.residue_surjective (R := K))]
    exact Module.length_ne_top
  have hlen : Module.length K M ≠ ⊤ := by
    rw [IsLocalRing.length_restrictScalars K R M]
    exact WithTop.mul_ne_top (Module.length_ne_top_iff.mpr hM) hres
  have : IsNoetherian K M :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hlen)).1
  infer_instance

theorem finite_quotient_of_radical_eq_maximalIdeal
    {K R : Type*} [Field K] [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [Algebra K R] [Module.Finite K (IsLocalRing.ResidueField R)]
    (I : Ideal R) (hrad : I.radical = IsLocalRing.maximalIdeal R) :
    Module.Finite K (R ⧸ I) :=
  finite_of_finiteLength_of_finite_residue
    (finiteLength_quotient_of_radical_eq_maximalIdeal I hrad)

end WeightedTorusJets.Deformation
end

section

open TensorProduct

namespace WeightedTorusJets.Deformation

theorem finite_residueTensor_of_finite_quotient
    {K A B : Type*} [Field K] [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra K A] [Algebra A B] [Algebra K B] [IsScalarTower K A B]
    (t : A) (ht : IsLocalRing.maximalIdeal A = Ideal.span {t})
    [Module.Finite K (B ⧸ Ideal.span {algebraMap A B t})] :
    Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] B) := by
  have : Module.Finite K (IsLocalRing.ResidueField A ⊗[A] B) :=
    Module.Finite.of_surjective (residueTensorQuotientAlgEquiv (K := K) t ht).symm.toLinearMap
      (residueTensorQuotientAlgEquiv (K := K) t ht).symm.surjective
  exact Module.Finite.of_restrictScalars_finite K (IsLocalRing.ResidueField A) _

theorem finrank_residueTensor_eq_quotient
    {K A B : Type*} [Field K] [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra K A] [Algebra A B] [Algebra K B] [IsScalarTower K A B]
    (t : A) (ht : IsLocalRing.maximalIdeal A = Ideal.span {t})
    (e : IsLocalRing.ResidueField A ≃ₐ[K] K) :
    Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] B) =
      Module.finrank K (B ⧸ Ideal.span {algebraMap A B t}) := by
  have hdegree : Module.finrank K (IsLocalRing.ResidueField A) = 1 := by
    simpa using e.toLinearEquiv.finrank_eq
  have hdim := Module.finrank_mul_finrank K (IsLocalRing.ResidueField A)
    (IsLocalRing.ResidueField A ⊗[A] B)
  rw [hdegree, one_mul] at hdim
  exact hdim.trans (residueTensorQuotientAlgEquiv (K := K) t ht).toLinearEquiv.finrank_eq

end WeightedTorusJets.Deformation

end

section

open Module TensorProduct

namespace WeightedTorusJets.Deformation

theorem finrank_special_fiber_le_generic
    (R F M : Type*) [CommRing R] [IsLocalRing R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    [Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M)]
    [Module.Finite F (F ⊗[R] M)] :
    Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M) ≤
      Module.finrank F (F ⊗[R] M) := by
  classical
  let k := IsLocalRing.ResidueField R
  let b := Module.finBasis k (k ⊗[R] M)
  choose v hv using fun i =>
    TensorProduct.mk_surjective R M k (IsLocalRing.residue_surjective (R := R)) (b i)
  have hspecial : LinearIndependent k (TensorProduct.mk R k M 1 ∘ v) := by
    simpa only [Function.comp_def, hv] using b.linearIndependent
  have hbase : LinearIndependent R v := IsLocalRing.linearIndependent_of_flat v hspecial
  have hgeneric : LinearIndependent F (TensorProduct.mk R F M 1 ∘ v) :=
    hbase.of_isLocalizedModule F (nonZeroDivisors R) (TensorProduct.mk R F M 1)
  simpa using hgeneric.fintype_card_le_finrank

theorem finrank_special_fiber_le_global_generic
    (R F M G : Type*) [CommRing R] [IsLocalRing R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    [Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M)]
    [AddCommGroup G] [Module F G] [Module.Finite F G]
    (π : G →ₗ[F] F ⊗[R] M) (hπ : Function.Surjective π) :
    Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M) ≤
      Module.finrank F G := by
  have : Module.Finite F (F ⊗[R] M) := Module.Finite.of_surjective π hπ
  exact (finrank_special_fiber_le_generic R F M).trans
    (LinearMap.finrank_le_finrank_of_surjective hπ)

end WeightedTorusJets.Deformation

end

section

namespace WeightedTorusJets.Deformation

theorem finite_residueField_mvPolynomial_maximal
    {K σ : Type*} [Field K] [Finite σ]
    (p : Ideal (MvPolynomial σ K)) [p.IsMaximal] : Module.Finite K p.ResidueField := by
  let := Ideal.Quotient.field p
  let : Module.Finite K (MvPolynomial σ K ⧸ p) :=
    finite_of_finite_type_of_isJacobsonRing K _
  exact Module.Finite.of_surjective
    (IsScalarTower.toAlgHom K (MvPolynomial σ K ⧸ p) p.ResidueField).toLinearMap
    p.bijective_algebraMap_quotient_residueField.surjective

end WeightedTorusJets.Deformation

end

section
namespace WeightedTorusJets.Deformation

open _root_.Polynomial TensorProduct

theorem finrank_local_quotient_le_pow_of_radical
    {K : Type*} [Field K] (h d : ℕ)
    (p : Ideal (MvPolynomial (Fin h) K)) [p.IsMaximal]
    (f : Fin h → MvPolynomial (Fin h) K)
    (hf : ∀ i, (f i).totalDegree ≤ d)
    (hrad : (Ideal.span (Set.range (fun i =>
      algebraMap (MvPolynomial (Fin h) K) (Localization.AtPrime p) (f i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime p)) :
    Module.finrank K ((Localization.AtPrime p) ⧸ Ideal.span (Set.range (fun i =>
      algebraMap (MvPolynomial (Fin h) K) (Localization.AtPrime p) (f i)))) ≤ d ^ h := by
  let I : Ideal K[X] := RingHom.ker (evalRingHom (0 : K))
  have hI : I = Ideal.span {Polynomial.X - Polynomial.C (0 : K)} := ker_evalRingHom _
  let : I.IsPrime := RingHom.ker_isPrime (evalRingHom (0 : K))
  let A := Localization.AtPrime I
  let q := p.comap (MvPolynomial.map (σ := Fin h) (evalRingHom (0 : K)))
  let S := Localization.AtPrime q
  let : CommRing S := inferInstance
  let : Algebra A S := parameterLocalAlgebra p I (0 : K) hI
  have : IsScalarTower K[X] A S := parameterLocalAlgebra_isScalarTower p I (0 : K) hI
  have : IsScalarTower K A S := parameterLocalAlgebra_groundFieldTower p I (0 : K) hI
  have hFracTower := localFractionAlgebra_isScalarTower (F := RatFunc K) I
  have hFracField := localFractionAlgebra_isFractionRing (F := RatFunc K) I
  let : Algebra A (RatFunc K) := localFractionAlgebra (F := RatFunc K) I
  let : SMul A (RatFunc K) := (localFractionAlgebra (F := RatFunc K) I).toSMul
  have : IsScalarTower K[X] A (RatFunc K) := hFracTower
  have : IsFractionRing A (RatFunc K) := hFracField
  let Fs := fun i => algebraMap (MvPolynomial (Fin h) K[X]) S (polynomialDeformation f d i)
  let J := Ideal.span (Set.range Fs)
  let B := S ⧸ J
  let t : A := algebraMap K[X] A (Polynomial.X - Polynomial.C (0 : K))
  let L := (Localization.AtPrime p) ⧸ Ideal.span (Set.range (fun i =>
    algebraMap (MvPolynomial (Fin h) K) (Localization.AtPrime p) (f i)))
  have ht : IsLocalRing.maximalIdeal A = Ideal.span {t} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    calc
      I.map (algebraMap K[X] A) =
          (Ideal.span {Polynomial.X - Polynomial.C (0 : K)}).map (algebraMap K[X] A) :=
        congrArg (Ideal.map (algebraMap K[X] A)) hI
      _ = _ := by
        rw [Ideal.map_span]
        simp only [Set.image_singleton]
        rfl
  let e : (B ⧸ Ideal.span {algebraMap A B t}) ≃ₐ[K] L := by
    have hJ : (Ideal.span {algebraMap A B t} : Ideal B) =
        (Ideal.span {algebraMap (MvPolynomial (Fin h) K[X]) S
          (MvPolynomial.C (σ := Fin h) (Polynomial.X - Polynomial.C (0 : K)))} : Ideal S).map
            (Ideal.Quotient.mk J) := by
      rw [Ideal.map_span, Set.image_singleton]
      congr 1
      congr 1
      rw [IsScalarTower.algebraMap_apply A S B, parameterLocalAlgebra_parameter]
      rfl
    exact (Ideal.quotientEquivAlgOfEq K hJ).trans
      (polynomialDeformationSpecialFiberAlgEquiv p f d)
  have : Module.Finite K p.ResidueField := finite_residueField_mvPolynomial_maximal p
  have : Module.Finite K L := finite_quotient_of_radical_eq_maximalIdeal _ hrad
  have : Module.Finite K (B ⧸ Ideal.span {algebraMap A B t}) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  have : Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] B) :=
    finite_residueTensor_of_finite_quotient (K := K) t ht
  have hlen : (h : ℕ∞) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)).height := by
    have hd := IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
      Geometry.maximal_polynomial_height h p] at hd
    exact_mod_cast hd.symm
  have : Module.Flat A B := flat_polynomialDeformation_localized p I hI f d hrad hlen
  let G := MvPolynomial (Fin h) (RatFunc K) ⧸ Ideal.span (Set.range (fun i =>
    MvPolynomial.map (algebraMap K[X] (RatFunc K)) (polynomialDeformation f d i)))
  obtain ⟨hfinite, hbound⟩ := generic_affine_deformation_quotient_bound f d hf
  let : Module.Finite (RatFunc K) G := hfinite
  obtain ⟨π, hπ, _⟩ := exists_surjective_global_polynomial_quotient_to_local_generic_fiber
    (A := A) (F := RatFunc K) (S := S) I.primeCompl q.primeCompl
      (polynomialDeformation f d)
  have hcomp := finrank_special_fiber_le_global_generic A (RatFunc K) B G π hπ
  rw [finrank_residueTensor_eq_quotient (K := K) t ht
    (residueFieldAtLinearAlgEquiv I (0 : K) hI), e.toLinearEquiv.finrank_eq] at hcomp
  exact hcomp.trans (by simpa only [Fintype.card_fin] using hbound)

end WeightedTorusJets.Deformation
end

end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_NormalizationPresentationLocalEquiv
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
section
open scoped BigOperators
open Module
open MvPolynomial
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section
namespace WeightedTorusJets.Geometry.DegreeBezout

open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {K σ ι τ : Type*} [CommRing K]

theorem normalizationPresentationLocalEquiv_algebraMap
    (e : MvPolynomial (ι ⊕ τ) K ≃ₐ[K] MvPolynomial σ K)
    (P : Ideal (MvPolynomial σ K)) [P.IsPrime] (f : MvPolynomial σ K) :
    normalizationPresentationLocalEquiv e P (algebraMap _ (Localization.AtPrime P) f) =
      algebraMap _ (Localization.AtPrime
        (P.comap (normalizationPresentation e).symm.toRingHom))
          (normalizationPresentation e f) := by
  apply (normalizationPresentationLocalEquiv e P).symm.injective
  rw [AlgEquiv.symm_apply_apply]
  change algebraMap _ (Localization.AtPrime P) f =
    Localization.localRingHom _ P (normalizationPresentation e).symm.toRingHom rfl
      (algebraMap _ _ (normalizationPresentation e f))
  rw [Localization.localRingHom_to_map]
  exact congrArg (algebraMap _ (Localization.AtPrime P))
    ((normalizationPresentation e).symm_apply_apply f).symm

end WeightedTorusJets.Geometry.DegreeBezout

namespace WeightedTorusJets.Geometry

theorem totalDegree_eval₂_le_of_linear_images
    {R S σ τ : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (x : σ → MvPolynomial τ S)
    (hx : ∀ i, (x i).totalDegree ≤ 1) (p : MvPolynomial σ R) :
    (p.eval₂ (MvPolynomial.C.comp f) x).totalDegree ≤ p.totalDegree := by
  classical
  let φ := MvPolynomial.eval₂Hom (MvPolynomial.C.comp f) x
  change (φ p).totalDegree ≤ p.totalDegree
  conv_lhs => rw [p.as_sum, map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  apply le_trans _ (MvPolynomial.le_totalDegree hd)
  rw [MvPolynomial.monomial_eq, map_mul, Finsupp.prod, map_prod]
  calc
    _ ≤ (φ (MvPolynomial.C (p.coeff d))).totalDegree +
        (∑ i ∈ d.support, (φ (MvPolynomial.X i ^ d i)).totalDegree) :=
      (MvPolynomial.totalDegree_mul _ _).trans
        (Nat.add_le_add_left (MvPolynomial.totalDegree_finsetProd _ _) _)
    _ = ∑ i ∈ d.support, ((x i) ^ d i).totalDegree := by simp [φ]
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i _
      exact (MvPolynomial.totalDegree_pow _ _).trans
        (by simpa using Nat.mul_le_mul_left (d i) (hx i))
    _ = d.sum (fun _ e => e) := rfl

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry.DegreeBezout

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem coefficient_localization_finrank_le_pow
    {B F : Type*} [CommRing B] [IsDomain B] [Field F]
    [Algebra B F] [IsFractionRing B F]
    (h D : ℕ) (p : Ideal (MvPolynomial (Fin h) B)) [p.IsPrime]
    [Module.Finite B (MvPolynomial (Fin h) B ⧸ p)]
    (hp : p.comap MvPolynomial.C = ⊥)
    (f : Fin h → MvPolynomial (Fin h) B)
    (hf : ∀ i, (MvPolynomial.map (algebraMap B F) (f i)).totalDegree ≤ D)
    (hrad : (Ideal.span (Set.range (fun i =>
      algebraMap _ (Localization.AtPrime p) (f i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime p)) :
    let := coefficient_localization_isMaximal_of_finite (F := F) p hp
    let q := p.map (algebraMap (MvPolynomial (Fin h) B) (MvPolynomial (Fin h) F))
    Module.finrank F (Localization.AtPrime q ⧸ Ideal.span (Set.range (fun i =>
      algebraMap _ (Localization.AtPrime q)
        (MvPolynomial.map (algebraMap B F) (f i))))) ≤ D ^ h := by
  let := coefficient_localization_isMaximal_of_finite (F := F) p hp
  let q := p.map (algebraMap (MvPolynomial (Fin h) B) (MvPolynomial (Fin h) F))
  let e := coefficientLocalizationLocalEquiv (F := F) p hp
  have hcomm (i : Fin h) : e (algebraMap _ (Localization.AtPrime p) (f i)) =
      algebraMap _ (Localization.AtPrime q)
        (MvPolynomial.map (algebraMap B F) (f i)) := by
    rw [AlgEquiv.commutes]
    rfl
  have hrad' := radical_span_eq_maximalIdeal_of_commuting_images
    e.toRingEquiv _ _ hcomm hrad
  exact WeightedTorusJets.Deformation.finrank_local_quotient_le_pow_of_radical h D q
    (fun i => MvPolynomial.map (algebraMap B F) (f i)) hf hrad'

end WeightedTorusJets.Geometry.DegreeBezout

namespace WeightedTorusJets.Geometry.DegreeBezout

open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem totalDegree_normalizationPresentation_le
    {K σ ι τ : Type*} [Field K]
    (e : MvPolynomial (ι ⊕ τ) K ≃ₐ[K] MvPolynomial σ K)
    (f : MvPolynomial σ K) :
    (normalizationPresentation e f).totalDegree ≤ (e.symm f).totalDegree := by
  let s := ((renameEquiv K (Equiv.sumComm ι τ)).trans (sumAlgEquiv K τ ι)).toRingHom
  have hs : s = eval₂Hom (C.comp (C : K →+* MvPolynomial ι K))
      (Sum.elim (fun i => C (X i)) X) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [s]
    · intro i
      cases i <;> simp [s]
  change (s (e.symm f)).totalDegree ≤ _
  rw [hs]
  apply totalDegree_eval₂_le_of_linear_images
  intro i
  cases i <;> simp

theorem totalDegree_localized_normalizationPresentation_le
    {K σ ι τ : Type*} [Field K]
    (e : MvPolynomial (ι ⊕ τ) K ≃ₐ[K] MvPolynomial σ K)
    (f : MvPolynomial σ K) :
    (MvPolynomial.map (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)))
      (normalizationPresentation e f)).totalDegree ≤ (e.symm f).totalDegree := by
  exact (Finset.sup_mono (support_map_subset _ _)).trans
    (totalDegree_normalizationPresentation_le e f)

theorem normalizationPresentation_radical_eq_maximal
    {K σ ι τ ν : Type*} [CommRing K]
    (e : MvPolynomial (ι ⊕ τ) K ≃ₐ[K] MvPolynomial σ K)
    (P : Ideal (MvPolynomial σ K)) [P.IsPrime] (f : ν → MvPolynomial σ K)
    (hrad : (Ideal.span (Set.range (fun i =>
      algebraMap _ (Localization.AtPrime P) (f i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    (Ideal.span (Set.range (fun i => algebraMap _
      (Localization.AtPrime (P.comap (normalizationPresentation e).symm.toRingHom))
      (normalizationPresentation e (f i))))).radical = IsLocalRing.maximalIdeal
        (Localization.AtPrime (P.comap (normalizationPresentation e).symm.toRingHom)) := by
  exact radical_span_eq_maximalIdeal_of_commuting_images
    (normalizationPresentationLocalEquiv e P).toRingEquiv
    (fun i => algebraMap _ (Localization.AtPrime P) (f i))
    (fun i => algebraMap _
      (Localization.AtPrime (P.comap (normalizationPresentation e).symm.toRingHom))
      (normalizationPresentation e (f i)))
    (fun i => normalizationPresentationLocalEquiv_algebraMap e P (f i)) hrad

end WeightedTorusJets.Geometry.DegreeBezout

open Module TensorProduct

namespace WeightedTorusJets.Deformation

theorem finrank_eq_length_mul_residue_degree
    (K R M : Type*) [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]
    [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
    [Module.Finite K M] [Module.Finite K (IsLocalRing.ResidueField R)] :
    (Module.finrank K M : ℕ∞) = Module.length R M *
      (Module.finrank K (IsLocalRing.ResidueField R) : ℕ∞) := by
  have h := IsLocalRing.length_restrictScalars K R M
  rw [← Module.length_eq_of_surjective (M := IsLocalRing.ResidueField R)
    (IsLocalRing.residue_surjective (R := K)),
    Module.length_eq_finrank K M,
    Module.length_eq_finrank K (IsLocalRing.ResidueField R)] at h
  exact h

end WeightedTorusJets.Deformation

namespace WeightedTorusJets.Geometry

variable {R : Type*} [CommRing R] (I p : Ideal R) [p.IsPrime]

theorem component_local_artinian [IsNoetherianRing R] (hp : p ∈ I.minimalPrimes) :
    IsArtinianRing
      (Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p))) := by
  apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing
  rwa [IsLocalization.minimalPrimes_map p.primeCompl (Localization.AtPrime p) I,
    Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]

theorem component_local_length_ne_top [IsNoetherianRing R] (hp : p ∈ I.minimalPrimes) :
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p))) ≠ ⊤ := by
  have := component_local_artinian I p hp
  have : IsArtinian (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p))) :=
    isArtinian_of_surjective_algebraMap
      (R := Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p)))
      Ideal.Quotient.mk_surjective
  exact Module.length_ne_top

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry.DegreeBezout

theorem map_extended_ideal_eq {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (I : Ideal R) :
    (I.map (algebraMap R A)).map e.toRingEquiv.toRingHom = I.map (algebraMap R B) := by
  rw [Ideal.map_map]
  congr 1
  exact RingHom.ext e.commutes

theorem extended_quotient_length_eq {R A B : Type*}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (I : Ideal R) :
    Module.length A (A ⧸ I.map (algebraMap R A)) =
      Module.length B (B ⧸ I.map (algebraMap R B)) :=
  quotient_length_eq_of_ringEquiv e.toRingEquiv _ _ (map_extended_ideal_eq e I).symm



open IsLocalRing Module

section Local

variable (K R M : Type*) [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]
  [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]

theorem field_length_eq_local_length_mul_residue_length :
    length K M = length R M * length K (ResidueField R) := by
  rw [IsLocalRing.length_restrictScalars K R M,
    ← Module.length_eq_of_surjective (M := ResidueField R)
      (IsLocalRing.residue_surjective (R := K))]

theorem finite_of_finite_length_of_finite_residue
    [Module.Finite K (ResidueField R)] (hM : IsFiniteLength R M) :
    Module.Finite K M := by
  have hlen : length K M ≠ ⊤ := by
    rw [field_length_eq_local_length_mul_residue_length K R M,
      Module.length_eq_finrank K (ResidueField R)]
    lift length R M to ℕ using Module.length_ne_top_iff.mpr hM with n hn
    rw [← Nat.cast_mul]
    exact ENat.natCast_ne_top _
  have hfinite := Module.length_ne_top_iff.mp hlen
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite).1
  infer_instance

end Local

end WeightedTorusJets.Geometry.DegreeBezout

namespace WeightedTorusJets.Geometry.DegreeBezout

open IsLocalRing Module

variable (K A : Type*) [Field K] [CommRing A] [Algebra K A]

theorem finite_residue_of_maximal [Algebra.FiniteType K A]
    (p : Ideal A) [p.IsMaximal] :
    Module.Finite K (ResidueField (Localization.AtPrime p)) := by
  let : Field (A ⧸ p) := Ideal.Quotient.field p
  let : Module.Finite K (A ⧸ p) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ p)
  let : Module.Finite (A ⧸ p) p.ResidueField := Module.Finite.of_surjective
    (Algebra.linearMap (A ⧸ p) p.ResidueField)
    p.bijective_algebraMap_quotient_residueField.surjective
  exact Module.Finite.trans (A ⧸ p) p.ResidueField

theorem isolated_quotient_finite [IsNoetherianRing A] [Algebra.FiniteType K A]
    (I p : Ideal A) [p.IsMaximal] (hp : p ∈ I.minimalPrimes) :
    Module.Finite K
      (Localization.AtPrime p ⧸ I.map (algebraMap A (Localization.AtPrime p))) := by
  let := finite_residue_of_maximal K A p
  exact finite_of_finite_length_of_finite_residue K (Localization.AtPrime p) _
    (Module.length_ne_top_iff.mp (component_local_length_ne_top I p hp))

theorem isolated_component_finrank [IsNoetherianRing A] [Algebra.FiniteType K A]
    (I p : Ideal A) [p.IsMaximal] (hp : p ∈ I.minimalPrimes) :
    (finrank K
      (Localization.AtPrime p ⧸ I.map (algebraMap A (Localization.AtPrime p))) : ℕ∞) =
      length (Localization.AtPrime p)
        (Localization.AtPrime p ⧸ I.map (algebraMap A (Localization.AtPrime p))) *
          (finrank K (ResidueField (Localization.AtPrime p)) : ℕ∞) := by
  let := finite_residue_of_maximal K A p
  let := isolated_quotient_finite K A I p hp
  exact WeightedTorusJets.Deformation.finrank_eq_length_mul_residue_degree K
    (Localization.AtPrime p) _

end WeightedTorusJets.Geometry.DegreeBezout

namespace WeightedTorusJets.Geometry.DegreeBezout

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem coefficient_localization_residue_degree_eq_rank
    {B F σ : Type*} [CommRing B] [IsDomain B] [Field F]
    [Algebra B F] [IsFractionRing B F]
    (p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    [(p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).IsPrime]
    [Algebra F p.ResidueField] [IsScalarTower B F p.ResidueField]
    (hp : p.comap MvPolynomial.C = ⊥) :
    Module.finrank F
      (p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).ResidueField =
      Module.finrank B (MvPolynomial σ B ⧸ p) := by
  rw [← (coefficientLocalizationResidueAlgEquiv p hp).toLinearEquiv.finrank_eq]
  exact IsFractionRing.finrank_eq B F (MvPolynomial σ B ⧸ p) p.ResidueField

theorem projected_residue_degree_eq_component_rank
    {B F σ : Type*} [CommRing B] [IsDomain B] [Field F]
    [Algebra B F] [IsFractionRing B F]
    (p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    [(p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).IsPrime]
    (hp : p.comap MvPolynomial.C = ⊥) :
    Module.finrank F
      (p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).ResidueField =
      Module.finrank B (MvPolynomial σ B ⧸ p) := by
  let := componentCoefficientFractionAlgebra (F := F) p hp
  let := componentCoefficientFractionAlgebra_tower (F := F) p hp
  exact coefficient_localization_residue_degree_eq_rank p hp

theorem coefficient_localization_quotient_length
    {B F σ : Type*} [CommRing B] [IsDomain B] [Field F]
    [Algebra B F] [IsFractionRing B F]
    (I p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    [(p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).IsPrime]
    (hp : p.comap MvPolynomial.C = ⊥) :
    let q := p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ I.map (algebraMap _ (Localization.AtPrime p))) =
    Module.length (Localization.AtPrime q)
      (Localization.AtPrime q ⧸
        (I.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).map
          (algebraMap _ (Localization.AtPrime q))) := by
  dsimp only
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  exact extended_quotient_length_eq (coefficientLocalizationLocalEquiv p hp) I

theorem coefficient_localization_component_finrank
    {B F σ : Type*} [CommRing B] [IsDomain B] [Field F] [Finite σ]
    [Algebra B F] [IsFractionRing B F]
    (I p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    [(p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).IsMaximal]
    (hp : p.comap MvPolynomial.C = ⊥) (hpI : p ∈ I.minimalPrimes) :
    let q := p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))
    (Module.finrank F
      (Localization.AtPrime q ⧸
        (I.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).map
          (algebraMap _ (Localization.AtPrime q))) : ℕ∞) =
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ I.map (algebraMap _ (Localization.AtPrime p))) *
        (Module.finrank F (IsLocalRing.ResidueField (Localization.AtPrime q)) : ℕ∞) := by
  let q := p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))
  let M : Submonoid (MvPolynomial σ B) := (nonZeroDivisors B).map MvPolynomial.C
  have hq : q ∈ (I.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map M (MvPolynomial σ F) I, Set.mem_preimage]
    change q.comap (algebraMap (MvPolynomial σ B) (MvPolynomial σ F)) ∈ I.minimalPrimes
    have he := IsLocalization.under_map_of_isPrime_disjoint M (MvPolynomial σ F)
      (show p.IsPrime from inferInstance) (coefficient_nonZeroDivisors_disjoint p hp)
    change q.comap (algebraMap (MvPolynomial σ B) (MvPolynomial σ F)) = p at he
    rwa [he]
  have h := isolated_component_finrank F (MvPolynomial σ F)
    (I.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))) q hq
  rw [← coefficient_localization_quotient_length I p hp] at h
  exact h

theorem coefficient_localization_component_finrank_eq_length_mul_rank
    {B F σ : Type*} [CommRing B] [IsDomain B] [Field F] [Finite σ]
    [Algebra B F] [IsFractionRing B F]
    (I p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    [(p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).IsMaximal]
    (hp : p.comap MvPolynomial.C = ⊥) (hpI : p ∈ I.minimalPrimes) :
    let q := p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))
    (Module.finrank F
      (Localization.AtPrime q ⧸
        (I.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).map
          (algebraMap _ (Localization.AtPrime q))) : ℕ∞) =
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ I.map (algebraMap _ (Localization.AtPrime p))) *
        (Module.finrank B (MvPolynomial σ B ⧸ p) : ℕ∞) := by
  rw [← projected_residue_degree_eq_component_rank (F := F) p hp]
  exact coefficient_localization_component_finrank I p hp hpI

end WeightedTorusJets.Geometry.DegreeBezout

end
end
end
end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_LinearVariableBasis
attribute [-instance] _root_.OAI.Erdos970.NumberTheoryLean.KernelWeightTransform.kernelPower_isSFiniteKernel _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.F_add _root_.Erdos970.F_mul _root_.Erdos970.F_neg _root_.Erdos970.F_sub _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.deriv_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
section
open scoped BigOperators
open Module
open MvPolynomial
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section
open Module TensorProduct
namespace WeightedTorusJets.Geometry.DegreeBezout

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem finite_normalization_local_finrank_eq_length_mul_rank
    {B F σ : Type*} [CommRing B] [IsDomain B] [Field F] [Finite σ]
    [Algebra B F] [IsFractionRing B F]
    (I p : Ideal (MvPolynomial σ B)) [p.IsPrime]
    [Module.Finite B (MvPolynomial σ B ⧸ p)]
    (hp : p.comap MvPolynomial.C = ⊥) (hpI : p ∈ I.minimalPrimes) :
    letI := coefficient_localization_isMaximal_of_finite (F := F) p hp
    let q := p.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))
    (Module.finrank F
      (Localization.AtPrime q ⧸
        (I.map (algebraMap (MvPolynomial σ B) (MvPolynomial σ F))).map
          (algebraMap _ (Localization.AtPrime q))) : ℕ∞) =
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ I.map (algebraMap _ (Localization.AtPrime p))) *
        (Module.finrank B (MvPolynomial σ B ⧸ p) : ℕ∞) := by
  let := coefficient_localization_isMaximal_of_finite (F := F) p hp
  exact coefficient_localization_component_finrank_eq_length_mul_rank I p hp hpI

end WeightedTorusJets.Geometry.DegreeBezout

namespace WeightedTorusJets.GeometryAcceptance

theorem mem_minimalPrimes_of_local_radical_eq_maximal
    {R : Type*} [CommRing R] (I p : Ideal R) [p.IsPrime]
    (hrad : (I.map (algebraMap R (Localization.AtPrime p))).radical =
      IsLocalRing.maximalIdeal (Localization.AtPrime p)) : p ∈ I.minimalPrimes := by
  have hlocal : IsLocalRing.maximalIdeal (Localization.AtPrime p) ∈
      (I.map (algebraMap R (Localization.AtPrime p))).minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes, hrad, Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  rwa [IsLocalization.minimalPrimes_map p.primeCompl (Localization.AtPrime p) I,
    Set.mem_preimage, Localization.AtPrime.under_maximalIdeal] at hlocal

end WeightedTorusJets.GeometryAcceptance

namespace WeightedTorusJets.Geometry.DegreeBezout

open MvPolynomial Module

noncomputable section

theorem normalization_linearForms_independent
    {K σ ι : Type*} [Field K] (P : Ideal (MvPolynomial σ K))
    (g : MvPolynomial ι K →ₐ[K] (MvPolynomial σ K ⧸ P))
    (hg : Function.Injective g) (l : ι → homogeneousSubmodule σ K 1)
    (hl : ∀ i, g (X i) = Ideal.Quotient.mk P (l i)) :
    LinearIndependent K l := by
  have hx : AlgebraicIndependent K (fun i => g (X i)) := by
    rw [algebraicIndependent_iff_injective_aeval]
    have he : aeval (fun i => g (X i)) = g := by ext i; simp
    simpa only [he] using hg
  have hcomp : (Ideal.Quotient.mkₐ K P).toLinearMap.comp
      (homogeneousSubmodule σ K 1).subtype ∘ l = (fun i => g (X i)) := by
    funext i
    exact (hl i).symm
  apply LinearIndependent.of_comp ((Ideal.Quotient.mkₐ K P).toLinearMap.comp
    (homogeneousSubmodule σ K 1).subtype)
  rw [hcomp]
  exact hx.linearIndependent

theorem symmetric_basis_coordinate_mem_degree_one
    {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    (b : Basis ι K M) (m : M) :
    SymmetricAlgebra.equivMvPolynomial b (SymmetricAlgebra.ι K M m) ∈
      homogeneousSubmodule ι K 1 := by
  let L := (SymmetricAlgebra.equivMvPolynomial b).toLinearMap.comp (SymmetricAlgebra.ι K M)
  have hs : Submodule.span K (Set.range b) ≤ (homogeneousSubmodule ι K 1).comap L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change SymmetricAlgebra.equivMvPolynomial b (SymmetricAlgebra.ι K M (b i)) ∈
      homogeneousSubmodule ι K 1
    simpa using (isHomogeneous_X K i)
  apply hs
  rw [b.span_eq]
  exact Submodule.mem_top

theorem symmetric_standard_coordinates
    {K σ : Type*} [Field K] (l : homogeneousSubmodule σ K 1) :
    SymmetricAlgebra.equivMvPolynomial (linearVariableBasis K σ)
      (SymmetricAlgebra.ι K (homogeneousSubmodule σ K 1) l) = (l : MvPolynomial σ K) := by
  have he : (SymmetricAlgebra.equivMvPolynomial (linearVariableBasis K σ)).toLinearMap.comp
      (SymmetricAlgebra.ι K (homogeneousSubmodule σ K 1)) =
      (homogeneousSubmodule σ K 1).subtype := by
    apply (linearVariableBasis K σ).ext
    intro i
    simp
  exact congrArg (fun f : homogeneousSubmodule σ K 1 →ₗ[K] MvPolynomial σ K => f l) he

@[simp] theorem polynomialCoordinatesOfLinearBasis_X
    {K σ ι : Type*} [Field K] (b : Basis ι K (homogeneousSubmodule σ K 1)) (i : ι) :
    polynomialCoordinatesOfLinearBasis b (X i) = (b i : MvPolynomial σ K) := by
  simp [polynomialCoordinatesOfLinearBasis, symmetric_standard_coordinates]

theorem polynomialCoordinatesOfLinearBasis_symm_X_homogeneous
    {K σ ι : Type*} [Field K] (b : Basis ι K (homogeneousSubmodule σ K 1)) (j : σ) :
    ((polynomialCoordinatesOfLinearBasis b).symm (X j)).IsHomogeneous 1 := by
  change ((SymmetricAlgebra.equivMvPolynomial b)
    ((SymmetricAlgebra.equivMvPolynomial (linearVariableBasis K σ)).symm (X j))).IsHomogeneous 1
  rw [SymmetricAlgebra.equivMvPolynomial_symm_X]
  exact symmetric_basis_coordinate_mem_degree_one b _

theorem polynomialCoordinatesOfLinearBasis_homogeneous
    {K σ ι : Type*} [Field K] (b : Basis ι K (homogeneousSubmodule σ K 1))
    {p : MvPolynomial ι K} {d : ℕ} (hp : p.IsHomogeneous d) :
    (polynomialCoordinatesOfLinearBasis b p).IsHomogeneous d := by
  have he : aeval (fun i => polynomialCoordinatesOfLinearBasis b (X i)) =
      (polynomialCoordinatesOfLinearBasis b).toAlgHom := by ext i; simp
  simpa only [one_mul, he, AlgEquiv.coe_toAlgHom] using hp.aeval (n := 1)
    (fun i => polynomialCoordinatesOfLinearBasis b (X i))
    (fun i => by rw [polynomialCoordinatesOfLinearBasis_X]; exact (b i).property)

theorem polynomialCoordinatesOfLinearBasis_symm_homogeneous
    {K σ ι : Type*} [Field K] (b : Basis ι K (homogeneousSubmodule σ K 1))
    {p : MvPolynomial σ K} {d : ℕ} (hp : p.IsHomogeneous d) :
    ((polynomialCoordinatesOfLinearBasis b).symm p).IsHomogeneous d := by
  have he : aeval (fun i => (polynomialCoordinatesOfLinearBasis b).symm (X i)) =
      (polynomialCoordinatesOfLinearBasis b).symm.toAlgHom := by ext i; simp
  simpa only [one_mul, he, AlgEquiv.coe_toAlgHom] using hp.aeval (n := 1)
    (fun i => (polynomialCoordinatesOfLinearBasis b).symm (X i))
    (polynomialCoordinatesOfLinearBasis_symm_X_homogeneous b)

theorem basis_sumExtend_inl {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    {v : ι → M} (hv : LinearIndependent K v) (i : ι) :
    Basis.sumExtend hv (Sum.inl i) = v i := by
  simp only [Basis.sumExtend, Basis.reindex_apply, Basis.coe_extend]
  rfl

theorem exists_linearBasis_extension
    {K σ ι : Type*} [Field K] [Finite σ] [Finite ι]
    {l : ι → homogeneousSubmodule σ K 1} (hl : LinearIndependent K l) :
    ∃ h : ℕ, Nat.card ι + h = Nat.card σ ∧
      ∃ b : Basis (ι ⊕ Fin h) K (homogeneousSubmodule σ K 1),
        ∀ i, b (Sum.inl i) = l i := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  let : Fintype ι := Fintype.ofFinite ι
  let : Module.Finite K (homogeneousSubmodule σ K 1) := Module.Finite.of_basis (linearVariableBasis K σ)
  let b₀ := Basis.sumExtend hl
  let J := Basis.sumExtendIndex hl
  have : Finite (ι ⊕ J) := Module.Finite.finite_basis b₀
  let : Finite J := Finite.of_injective (Sum.inr : J → ι ⊕ J) Sum.inr_injective
  let : Fintype J := Fintype.ofFinite J
  let e : (ι ⊕ J) ≃ (ι ⊕ Fin (Fintype.card J)) :=
    Equiv.sumCongr (Equiv.refl ι) (Fintype.equivFin J)
  refine ⟨Fintype.card J, ?_, b₀.reindex e, ?_⟩
  · have he := (Module.finrank_eq_card_basis b₀).symm.trans
      (Module.finrank_eq_card_basis (linearVariableBasis K σ))
    simpa only [Fintype.card_sum, Nat.card_eq_fintype_card] using he
  · intro i
    simpa [Basis.reindex_apply, e, b₀] using basis_sumExtend_inl hl i

end

end WeightedTorusJets.Geometry.DegreeBezout

namespace WeightedTorusJets.Geometry.DegreeBezout

open MvPolynomial Module

theorem totalDegree_algHom_le_of_linear_images
    {K σ τ : Type*} [Field K]
    (f : MvPolynomial σ K →ₐ[K] MvPolynomial τ K)
    (hf : ∀ i, (f (X i)).totalDegree ≤ 1) (p : MvPolynomial σ K) :
    (f p).totalDegree ≤ p.totalDegree := by
  have h := totalDegree_eval₂_le_of_linear_images (RingHom.id K)
    (fun i => f (X i)) hf p
  have he : eval₂Hom (C.comp (RingHom.id K)) (fun i => f (X i)) = f.toRingHom := by
    ext i <;> simp
  change ((eval₂Hom (C.comp (RingHom.id K)) (fun i => f (X i))) p).totalDegree ≤ _ at h
  rw [he] at h
  exact h

theorem polynomialCoordinatesOfLinearBasis_totalDegree
    {K σ ι : Type*} [Field K] (b : Basis ι K (homogeneousSubmodule σ K 1))
    (p : MvPolynomial ι K) :
    (polynomialCoordinatesOfLinearBasis b p).totalDegree = p.totalDegree := by
  let e := polynomialCoordinatesOfLinearBasis b
  have hf : ∀ i, (e (X i)).totalDegree ≤ 1 := by
    intro i
    change (polynomialCoordinatesOfLinearBasis b (X i)).totalDegree ≤ 1
    rw [polynomialCoordinatesOfLinearBasis_X]
    exact IsHomogeneous.totalDegree_le (b i).property
  have hb : ∀ i, (e.symm (X i)).totalDegree ≤ 1 := fun i =>
    (polynomialCoordinatesOfLinearBasis_symm_X_homogeneous b i).totalDegree_le
  apply le_antisymm (totalDegree_algHom_le_of_linear_images e.toAlgHom hf p)
  simpa only [AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using
    totalDegree_algHom_le_of_linear_images e.symm.toAlgHom hb (e p)

theorem polynomialCoordinatesOfLinearBasis_symm_totalDegree
    {K σ ι : Type*} [Field K] (b : Basis ι K (homogeneousSubmodule σ K 1))
    (p : MvPolynomial σ K) :
    ((polynomialCoordinatesOfLinearBasis b).symm p).totalDegree = p.totalDegree := by
  simpa only [AlgEquiv.apply_symm_apply] using
    (polynomialCoordinatesOfLinearBasis_totalDegree b
      ((polynomialCoordinatesOfLinearBasis b).symm p)).symm

theorem exists_normalization_linear_coordinates
    {K σ ι : Type*} [Field K] [Finite σ] [Finite ι]
    (P : Ideal (MvPolynomial σ K))
    (g : MvPolynomial ι K →ₐ[K] (MvPolynomial σ K ⧸ P))
    (hg : Function.Injective g)
    (hl : ∀ i, ∃ l : MvPolynomial σ K, l.IsHomogeneous 1 ∧ g (X i) = Ideal.Quotient.mk P l) :
    ∃ h : ℕ, Nat.card ι + h = Nat.card σ ∧
      ∃ e : MvPolynomial (ι ⊕ Fin h) K ≃ₐ[K] MvPolynomial σ K,
        (∀ i, g (X i) = Ideal.Quotient.mk P (e (X (Sum.inl i)))) ∧
        (∀ p, (e p).totalDegree = p.totalDegree) ∧
        (∀ p, (e.symm p).totalDegree = p.totalDegree) ∧
        (∀ p d, p.IsHomogeneous d → (e p).IsHomogeneous d) ∧
        (∀ p d, p.IsHomogeneous d → (e.symm p).IsHomogeneous d) := by
  classical
  choose l hlh hlg using hl
  let l' : ι → homogeneousSubmodule σ K 1 := fun i => ⟨l i, hlh i⟩
  have hli := normalization_linearForms_independent P g hg l' hlg
  obtain ⟨h, hc, b, hb⟩ := exists_linearBasis_extension hli
  refine ⟨h, hc, polynomialCoordinatesOfLinearBasis b, ?_,
    polynomialCoordinatesOfLinearBasis_totalDegree b,
    polynomialCoordinatesOfLinearBasis_symm_totalDegree b, ?_, ?_⟩
  · intro i
    rw [polynomialCoordinatesOfLinearBasis_X, hb]
    exact hlg i
  · intro p d hp
    exact polynomialCoordinatesOfLinearBasis_homogeneous b hp
  · intro p d hp
    exact polynomialCoordinatesOfLinearBasis_symm_homogeneous b hp

theorem exists_normalization_linear_coordinates_of_count
    {K σ : Type*} [Field K] [Finite σ] {s h : ℕ}
    (P : Ideal (MvPolynomial σ K))
    (g : MvPolynomial (Fin s) K →ₐ[K] (MvPolynomial σ K ⧸ P))
    (hg : Function.Injective g)
    (hl : ∀ i, ∃ l : MvPolynomial σ K,
      l.IsHomogeneous 1 ∧ g (X i) = Ideal.Quotient.mk P l)
    (hc : s + h = Nat.card σ) :
    ∃ e : MvPolynomial (Fin s ⊕ Fin h) K ≃ₐ[K] MvPolynomial σ K,
      (∀ i, g (X i) = Ideal.Quotient.mk P (e (X (Sum.inl i)))) ∧
      (∀ p, (e p).totalDegree = p.totalDegree) ∧
      (∀ p, (e.symm p).totalDegree = p.totalDegree) ∧
      (∀ p d, p.IsHomogeneous d → (e p).IsHomogeneous d) ∧
      (∀ p d, p.IsHomogeneous d → (e.symm p).IsHomogeneous d) := by
  obtain ⟨h', hc', e, he⟩ := exists_normalization_linear_coordinates P g hg hl
  have hh : h' = h := by
    apply Nat.add_left_cancel (n := s)
    simpa only [Nat.card_fin, hc] using hc'
  subst h'
  exact ⟨e, he⟩

end WeightedTorusJets.Geometry.DegreeBezout

namespace WeightedTorusJets.Geometry.DegreeBezout

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem quotient_length_congr_ideal
    {R : Type*} [CommRing R] (I J : Ideal R) (h : I = J) :
    Module.length R (R ⧸ I) = Module.length R (R ⧸ J) := by
  subst J
  rfl

theorem quotient_finrank_congr_ideal
    {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (I J : Ideal R) (h : I = J) :
    Module.finrank K (R ⧸ I) = Module.finrank K (R ⧸ J) := by
  subst J
  rfl

theorem coefficient_localization_weighted_length_le_pow
    {B F : Type*} [CommRing B] [IsDomain B] [Field F]
    [Algebra B F] [IsFractionRing B F]
    (h D : ℕ) (p : Ideal (MvPolynomial (Fin h) B)) [p.IsPrime]
    [Module.Finite B (MvPolynomial (Fin h) B ⧸ p)]
    (hp : p.comap MvPolynomial.C = ⊥)
    (f : Fin h → MvPolynomial (Fin h) B)
    (hf : ∀ i, (MvPolynomial.map (algebraMap B F) (f i)).totalDegree ≤ D)
    (hrad : (Ideal.span (Set.range (fun i =>
      algebraMap _ (Localization.AtPrime p) (f i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime p)) :
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ Ideal.span (Set.range (fun i =>
        algebraMap _ (Localization.AtPrime p) (f i)))) *
      (Module.finrank B (MvPolynomial (Fin h) B ⧸ p) : ℕ∞) ≤ (D ^ h : ℕ) := by
  let I := Ideal.span (Set.range f)
  have hm : p ∈ I.minimalPrimes :=
    GeometryAcceptance.mem_minimalPrimes_of_local_radical_eq_maximal I p
      (by simpa only [I, Ideal.map_span, ← Set.range_comp, Function.comp_def] using hrad)
  have hn := coefficient_localization_finrank_le_pow (F := F) h D p hp f hf hrad
  have he := finite_normalization_local_finrank_eq_length_mul_rank (F := F) I p hp hm
  let := coefficient_localization_isMaximal_of_finite (F := F) p hp
  let q := p.map (algebraMap (MvPolynomial (Fin h) B) (MvPolynomial (Fin h) F))
  let J := Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime p) (f i)))
  let JF := Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime q)
    (MvPolynomial.map (algebraMap B F) (f i))))
  have hI : I.map (algebraMap _ (Localization.AtPrime p)) = J := by
    dsimp only [I]
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hIF : (I.map (algebraMap (MvPolynomial (Fin h) B)
      (MvPolynomial (Fin h) F))).map (algebraMap _ (Localization.AtPrime q)) = JF := by
    dsimp only [I]
    rw [Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp]
    rfl
  have hlength := quotient_length_congr_ideal _ _ hI
  have hdimension := quotient_finrank_congr_ideal (K := F) _ _ hIF
  calc
    _ = Module.length (Localization.AtPrime p)
          (Localization.AtPrime p ⧸ I.map (algebraMap _ (Localization.AtPrime p))) *
          (Module.finrank B (MvPolynomial (Fin h) B ⧸ p) : ℕ∞) := by rw [hlength]
    _ = (Module.finrank F (Localization.AtPrime q ⧸
          (I.map (algebraMap (MvPolynomial (Fin h) B) (MvPolynomial (Fin h) F))).map
            (algebraMap _ (Localization.AtPrime q))) : ℕ∞) := he.symm
    _ = (Module.finrank F (Localization.AtPrime q ⧸ JF) : ℕ∞) := by rw [hdimension]
    _ ≤ (D ^ h : ℕ) := by exact_mod_cast hn

theorem linear_normalization_weighted_local_length_le_jb247_oai
    {K σ : Type*} [Field K] [Finite σ] {s h D : ℕ}
    (P : Ideal (MvPolynomial σ K)) [P.IsPrime]
    (g : MvPolynomial (Fin s) K →ₐ[K] (MvPolynomial σ K ⧸ P))
    (hg : Function.Injective g)
    (hfinite : letI := g.toAlgebra
      letI : Module (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ P) := Algebra.toModule
      Module.Finite (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ P))
    (hlin : ∀ i, ∃ l : MvPolynomial σ K,
      l.IsHomogeneous 1 ∧ g (MvPolynomial.X i) = Ideal.Quotient.mk P l)
    (hcount : s + h = Nat.card σ)
    (f : Fin h → MvPolynomial σ K)
    (hf : ∀ i, (f i).totalDegree ≤ D)
    (hrad : (Ideal.span (Set.range (fun i =>
      algebraMap (MvPolynomial σ K) (Localization.AtPrime P) (f i)))).radical =
        IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    letI := g.toAlgebra
    letI : Module (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ P) := Algebra.toModule
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ Ideal.span (Set.range (fun i =>
        algebraMap (MvPolynomial σ K) (Localization.AtPrime P) (f i)))) *
      (Module.finrank (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ P) : ℕ∞) ≤
        (D ^ h : ℕ) := by
  let := g.toAlgebra
  let : Module (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ P) := Algebra.toModule
  obtain ⟨e, he, _, heinv, _, _⟩ :=
    exists_normalization_linear_coordinates_of_count P g hg hlin hcount
  let p := P.comap (normalizationPresentation e).symm.toRingHom
  let : p.IsPrime := Ideal.IsPrime.comap _
  have hp : p.comap MvPolynomial.C = ⊥ :=
    normalizationPresentation_coefficient_comap_eq_bot e P g hg he
  let : Module.Finite (MvPolynomial (Fin s) K)
      (MvPolynomial (Fin h) (MvPolynomial (Fin s) K) ⧸ p) :=
    finite_normalizationPresentation_quotient e P g he hfinite
  have hdeg (i : Fin h) :
      (MvPolynomial.map (algebraMap (MvPolynomial (Fin s) K)
          (FractionRing (MvPolynomial (Fin s) K)))
        (normalizationPresentation e (f i))).totalDegree ≤ D :=
    (totalDegree_localized_normalizationPresentation_le e (f i)).trans
      ((heinv (f i)).le.trans (hf i))
  have hrad' := normalizationPresentation_radical_eq_maximal e P f hrad
  have hn := coefficient_localization_weighted_length_le_pow
    (F := FractionRing (MvPolynomial (Fin s) K)) h D p hp
    (fun i => normalizationPresentation e (f i)) hdeg hrad'
  have hlength := quotient_length_eq_of_commuting_images
    (normalizationPresentationLocalEquiv e P).toRingEquiv
    (fun i => algebraMap (MvPolynomial σ K) (Localization.AtPrime P) (f i))
    (fun i => algebraMap _ (Localization.AtPrime p) (normalizationPresentation e (f i)))
    (fun i => normalizationPresentationLocalEquiv_algebraMap e P (f i))
  have hrank := (normalizationPresentationQuotientEquiv e P g he).toLinearEquiv.finrank_eq
  rw [hlength, ← hrank]
  exact hn

end WeightedTorusJets.Geometry.DegreeBezout

end
end
end
end
end

end

end Erdos970

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos970.WeightedTorusJets.Geometry.DegreeBezout.linear_normalization_weighted_local_length_le_jb247_oai.{u_1, u_2} := @OAI.Erdos970.WeightedTorusJets.Geometry.DegreeBezout.linear_normalization_weighted_local_length_le_jb247_oai.{u_1, u_2}
