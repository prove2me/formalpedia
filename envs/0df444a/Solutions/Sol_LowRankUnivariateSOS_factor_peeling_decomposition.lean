-- Prove2me | solution 1 for LowRankUnivariateSOS.factor_peeling_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:51.314253+00:00
-- url     : https://prove2.me/submissions/90c79b66-7684-4106-8a67-ea06faa7089c

import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebraCore
import Definitions.Def_LowRankUnivariateSOS_PeelingStep
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Data.List.Prime
import Mathlib.Data.Multiset.Filter
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebra
import Theorems.Thm_LowRankUnivariateSOS_zero_fst
import Theorems.Thm_LowRankUnivariateSOS_zero_snd
import Theorems.Thm_LowRankUnivariateSOS_scalePair_zero
import Theorems.Thm_LowRankUnivariateSOS_sigma2_zero
import Theorems.Thm_LowRankUnivariateSOS_A_zero_left
import Theorems.Thm_LowRankUnivariateSOS_A_zero_right
import Theorems.Thm_LowRankUnivariateSOS_A_scalePair_left
import Theorems.Thm_LowRankUnivariateSOS_A_self_eq_sigma2
import Theorems.Thm_LowRankUnivariateSOS_A_smul_right
import Theorems.Thm_LowRankUnivariateSOS_dot_add_left
import Theorems.Thm_LowRankUnivariateSOS_dot_add_right
import Theorems.Thm_LowRankUnivariateSOS_dot_neg_left
import Theorems.Thm_LowRankUnivariateSOS_dot_neg_right
import Theorems.Thm_LowRankUnivariateSOS_dot_smul_left
import Theorems.Thm_LowRankUnivariateSOS_dot_smul_right
import Theorems.Thm_LowRankUnivariateSOS_dot_zero_left
import Theorems.Thm_LowRankUnivariateSOS_dot_zero_right
import Theorems.Thm_LowRankUnivariateSOS_no_real_roots_sigma_reduced
import Theorems.Thm_LowRankUnivariateSOS_perpPair_fst
import Theorems.Thm_LowRankUnivariateSOS_perpPair_snd
import Theorems.Thm_LowRankUnivariateSOS_scalePair_fst
import Theorems.Thm_LowRankUnivariateSOS_scalePair_snd
import Theorems.Thm_LowRankUnivariateSOS_sigma2_perpPair
import Theorems.Thm_LowRankUnivariateSOS_sigma2_scalePair
import Theorems.Thm_LowRankUnivariateSOS_sigma2_smul
import Theorems.Thm_LowRankUnivariateSOS_smul_fst
import Theorems.Thm_LowRankUnivariateSOS_smul_snd
attribute [local simp] LowRankUnivariateSOS.A_scalePair_left
attribute [local simp] LowRankUnivariateSOS.A_self_eq_sigma2
attribute [local simp] LowRankUnivariateSOS.A_smul_right
attribute [local simp] LowRankUnivariateSOS.dot_add_left
attribute [local simp] LowRankUnivariateSOS.dot_add_right
attribute [local simp] LowRankUnivariateSOS.dot_neg_left
attribute [local simp] LowRankUnivariateSOS.dot_neg_right
attribute [local simp] LowRankUnivariateSOS.dot_smul_left
attribute [local simp] LowRankUnivariateSOS.dot_smul_right
attribute [local simp] LowRankUnivariateSOS.dot_zero_left
attribute [local simp] LowRankUnivariateSOS.dot_zero_right
attribute [local simp] LowRankUnivariateSOS.perpPair_fst
attribute [local simp] LowRankUnivariateSOS.perpPair_snd
attribute [local simp] LowRankUnivariateSOS.scalePair_fst
attribute [local simp] LowRankUnivariateSOS.scalePair_snd
attribute [local simp] LowRankUnivariateSOS.sigma2_perpPair
attribute [local simp] LowRankUnivariateSOS.sigma2_scalePair
attribute [local simp] LowRankUnivariateSOS.sigma2_smul
attribute [local simp] LowRankUnivariateSOS.smul_fst
attribute [local simp] LowRankUnivariateSOS.smul_snd


attribute [local simp] LowRankUnivariateSOS.zero_fst
attribute [local simp] LowRankUnivariateSOS.zero_snd
attribute [local simp] LowRankUnivariateSOS.scalePair_zero
attribute [local simp] LowRankUnivariateSOS.sigma2_zero
attribute [local simp] LowRankUnivariateSOS.A_zero_left
attribute [local simp] LowRankUnivariateSOS.A_zero_right
section
noncomputable section
namespace LowRankUnivariateSOS
private theorem peelTerminalScale_isCoprime {gBase q : Poly} {rs : List Poly}
    (hX : IsCoprime (Polynomial.X ^ 2) q)
    (hg : IsCoprime gBase q) :
    IsCoprime (peelTerminalScale gBase rs) q := by
  induction rs generalizing gBase with
  | nil =>
      simpa [peelTerminalScale] using hg
  | cons r rs ih =>
      have hg' : IsCoprime ((Polynomial.X ^ 2) * gBase) q :=
        hX.mul_left hg
      simpa [peelTerminalScale] using ih hg'
private theorem factor_peeling_X_coprime
    (u : UPair) (data : ReducedFactorization u) :
    IsCoprime Polynomial.X (sigma2 data.u0) := by
  have hnot_dvd : ¬ Polynomial.X ∣ sigma2 data.u0 := by
    intro hX
    have hroot : Polynomial.IsRoot (sigma2 data.u0) 0 := by
      have hX' : Polynomial.X - Polynomial.C (0 : ℝ) ∣ sigma2 data.u0 := by
        simpa using hX
      exact Polynomial.dvd_iff_isRoot.mp hX'
    exact (no_real_roots_sigma_reduced u data 0) hroot
  rcases EuclideanDomain.dvd_or_coprime Polynomial.X (sigma2 data.u0) Polynomial.irreducible_X with
    hX | hcop
  · exact (hnot_dvd hX).elim
  · exact hcop
section DotForm
variable {B : DotForm}
end DotForm
end LowRankUnivariateSOS
end
end

set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
namespace LowRankUnivariateSOS
theorem _root_.solution
    (u : UPair) (data : ReducedFactorization u) (ha : data.a ≠ 0) :
    ∃ gBase g : Poly, ∃ rs : List Poly,
      gBase ≠ 0 ∧
        data.a = gBase * rs.prod ∧
        g = peelTerminalScale gBase rs ∧
        IsCoprime g (sigma2 data.u0) ∧
        ∀ r ∈ rs, r ∣ sigma2 data.u0 := by
  classical
  let sig : Poly := sigma2 data.u0
  let peeled : Multiset Poly :=
    (UniqueFactorizationMonoid.normalizedFactors data.a).filter (fun r => r ∣ sig)
  let keep : Multiset Poly :=
    (UniqueFactorizationMonoid.normalizedFactors data.a).filter (fun r => ¬ r ∣ sig)
  let rs : List Poly := peeled.toList
  let gBase : Poly := Polynomial.C data.a.leadingCoeff * keep.prod
  let g : Poly := peelTerminalScale gBase rs
  have hlead : data.a.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr ha
  have hC_ne_zero : Polynomial.C data.a.leadingCoeff ≠ 0 := by
    simpa using hlead
  have hkeep_ne_zero : keep.prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro hz
    have hz' : (0 : Poly) ∈ UniqueFactorizationMonoid.normalizedFactors data.a := by
      exact (by
        simpa [keep] using hz :
          (0 : Poly) ∈ UniqueFactorizationMonoid.normalizedFactors data.a ∧ ¬ (0 : Poly) ∣ sig).1
    exact UniqueFactorizationMonoid.zero_notMem_normalizedFactors data.a hz'
  have hgBase_ne_zero : gBase ≠ 0 := by
    exact mul_ne_zero hC_ne_zero hkeep_ne_zero
  have hsplit : peeled + keep = UniqueFactorizationMonoid.normalizedFactors data.a := by
    simpa [peeled, keep] using
      (Multiset.filter_add_not (p := fun r : Poly => r ∣ sig)
        (UniqueFactorizationMonoid.normalizedFactors data.a))
  have hXcop : IsCoprime Polynomial.X sig :=
    factor_peeling_X_coprime u data
  have hcop_gBase : IsCoprime gBase sig := by
    have hrel : IsRelPrime gBase sig := by
      refine (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hgBase_ne_zero).2 ?_
      intro d hdg hds hdprime
      have hC_unit : IsUnit (Polynomial.C data.a.leadingCoeff) := by
        exact Polynomial.isUnit_C.mpr hlead.isUnit
      have hdg' : d ∣ Polynomial.C data.a.leadingCoeff * keep.prod := by
        simpa [gBase] using hdg
      rcases hdprime.dvd_or_dvd hdg' with hdC | hdkeep
      · exact hdprime.not_unit (isUnit_of_dvd_unit hdC hC_unit)
      · have hkeep_not : ¬ d ∣ keep.prod := by
          have hlist : ∀ r ∈ keep.toList, ¬ d ∣ r := by
            intro r hr hd_r
            have hr_keep : r ∈ keep := by
              simpa using hr
            have hr_factor :
                r ∈ UniqueFactorizationMonoid.normalizedFactors data.a ∧ ¬ r ∣ sig := by
              simpa [keep] using hr_keep
            have hrirr : Irreducible r :=
              UniqueFactorizationMonoid.irreducible_of_normalized_factor r hr_factor.1
            have hassoc : Associated d r :=
              hdprime.irreducible.associated_of_dvd hrirr hd_r
            have hr_sig : r ∣ sig :=
              (hassoc.dvd_iff_dvd_left).1 hds
            exact hr_factor.2 hr_sig
          exact fun hdkeep' =>
            (Prime.not_dvd_prod hdprime hlist) (by simpa using hdkeep')
        exact hkeep_not hdkeep
    exact hrel.isCoprime
  have hcop_g : IsCoprime g sig := by
    have hXsq : IsCoprime (Polynomial.X ^ 2) sig := by
      simpa using hXcop.pow_left (m := 2)
    simpa [g] using peelTerminalScale_isCoprime hXsq hcop_gBase
  refine ⟨gBase, g, rs, hgBase_ne_zero, ?_, rfl, hcop_g, ?_⟩
  · calc
      data.a =
          Polynomial.C data.a.leadingCoeff *
            (UniqueFactorizationMonoid.normalizedFactors data.a).prod := by
        symm
        exact Polynomial.leadingCoeff_mul_prod_normalizedFactors data.a
      _ = Polynomial.C data.a.leadingCoeff * (peeled + keep).prod := by
        rw [hsplit]
      _ = Polynomial.C data.a.leadingCoeff * (peeled.prod * keep.prod) := by
        simp
      _ = gBase * peeled.prod := by
        simp [gBase]
        ac_rfl
      _ = gBase * rs.prod := by
        simp [rs]
  · intro r hr
    have hr_peeled : r ∈ peeled := by
      simpa [rs] using hr
    have hr_factor :
        r ∈ UniqueFactorizationMonoid.normalizedFactors data.a ∧ r ∣ sig := by
      simpa [peeled] using hr_peeled
    exact hr_factor.2
end LowRankUnivariateSOS
