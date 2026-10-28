-- Prove2me | solution 1 for OAI.PiExponent.localIsolatedBezout_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T08:59:02.343218+00:00
-- url     : https://prove2.me/submissions/7f155c13-9a15-4149-8d0b-38f77d996c17

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A010
import Theorems.Thm_OAI_PiExponentJets_W22_affine_local_regular_list_bezout_q68
import Theorems.Thm_OAI_PiExponentSiegel_W58_polynomialLocal_regular_prefix_maximal_not_associated_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_ParameterCombinations
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators

variable {k σ ι : Type*} [CommRing k]

theorem parameterCombination_totalDegree_le (s : Finset ι) (c : ι → k)
    (f : ι → MvPolynomial σ k) {d : ℕ}
    (hf : ∀ i ∈ s, (f i).totalDegree ≤ d) :
    (parameterCombination s c f).totalDegree ≤ d := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  calc
    (MvPolynomial.C (c i) * f i).totalDegree ≤
        (MvPolynomial.C (c i) : MvPolynomial σ k).totalDegree + (f i).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ = (f i).totalDegree := by rw [MvPolynomial.totalDegree_C, zero_add]
    _ ≤ d := hf i hi

theorem parameterCombination_mem (s : Finset ι) (c : ι → k)
    (f : ι → MvPolynomial σ k) (J : Ideal (MvPolynomial σ k))
    (hf : ∀ i ∈ s, f i ∈ J) : parameterCombination s c f ∈ J := by
  apply J.sum_mem
  intro i hi
  exact J.mul_mem_left _ (hf i hi)

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_FinsuppCandidates
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

variable {k σ ι : Type*} [CommRing k]

theorem linearCombination_eq_parameterCombination (f : ι → MvPolynomial σ k) (c : ι →₀ k) :
    Finsupp.linearCombination k f c = parameterCombination c.support c f := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, parameterCombination,
    MvPolynomial.C_mul']

theorem linearCombination_totalDegree_le (f : ι → MvPolynomial σ k) (c : ι →₀ k)
    {d : ℕ} (hf : ∀ i, (f i).totalDegree ≤ d) :
    (Finsupp.linearCombination k f c).totalDegree ≤ d := by
  rw [linearCombination_eq_parameterCombination]
  exact parameterCombination_totalDegree_le c.support c f (fun i _ => hf i)

theorem linearCombination_mem_ideal (f : ι → MvPolynomial σ k) (c : ι →₀ k)
    (J : Ideal (MvPolynomial σ k)) (hf : ∀ i, f i ∈ J) :
    Finsupp.linearCombination k f c ∈ J := by
  rw [linearCombination_eq_parameterCombination]
  exact parameterCombination_mem c.support c f J (fun i _ => hf i)

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_GenericCombination
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegel.W20

variable {K M I J : Type*} [Field K] [Infinite K]
  [AddCommGroup M] [Module K M] [Finite I]

theorem exists_linearCombination_avoiding_submodules
    (g : J → M) (P : I → Submodule K M)
    (h : ∀ i, ¬ Submodule.span K (Set.range g) ≤ P i) :
    ∃ c : J →₀ K, ∀ i, Finsupp.linearCombination K g c ∉ P i := by
  let bad : I → Submodule K (J →₀ K) :=
    fun i => (P i).comap (Finsupp.linearCombination K g)
  have hbad : ∀ i, bad i ≠ ⊤ := by
    intro i hi
    apply h i
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have hc : Finsupp.single j (1 : K) ∈ bad i := by
      rw [hi]
      trivial
    change Finsupp.linearCombination K g (Finsupp.single j 1) ∈ P i at hc
    simpa using hc
  obtain ⟨c, hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  exact ⟨c, hc⟩

variable {R : Type*} [CommRing R] [Algebra K R]

theorem exists_linearCombination_avoiding_ideals
    (g : J → R) (P : I → Ideal R)
    (h : ∀ i, ¬ Ideal.span (Set.range g) ≤ P i) :
    ∃ c : J →₀ K, ∀ i, Finsupp.linearCombination K g c ∉ P i := by
  apply exists_linearCombination_avoiding_submodules g
    (fun i => (P i).restrictScalars K)
  intro i hi
  apply h i
  apply Ideal.span_le.mpr
  intro x hx
  exact hi (Submodule.subset_span hx)

theorem exists_linearCombination_avoiding_primes_below_radical
    (g : J → R) (m : Ideal R)
    (hgen : (Ideal.span (Set.range g)).radical = m)
    (P : I → Ideal R) (hprime : ∀ i, (P i).IsPrime)
    (hbelow : ∀ i, P i < m) :
    ∃ c : J →₀ K, ∀ i, Finsupp.linearCombination K g c ∉ P i := by
  apply exists_linearCombination_avoiding_ideals g P
  intro i hle
  have hmle : m ≤ P i := by
    rw [← hgen]
    exact (hprime i).radical_le_iff.mpr hle
  exact (not_le_of_gt (hbelow i)) hmle

end PiExponentSiegel.W20

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalLength
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem quotient_length_antitone {P Q : Submodule R M} (hPQ : P ≤ Q) :
    Module.length R (M ⧸ Q) ≤ Module.length R (M ⧸ P) :=
  Module.length_le_of_surjective (Submodule.factor hPQ)
    (Submodule.factor_surjective hPQ)

theorem ideal_quotient_length_le {a J : Ideal R} (haJ : a ≤ J) :
    Module.length R (R ⧸ J) ≤ Module.length R (R ⧸ a) :=
  quotient_length_antitone haJ

theorem ideal_quotient_length_le_of_bound {a J : Ideal R} (haJ : a ≤ J)
    {B : ℕ∞} (hbound : Module.length R (R ⧸ a) ≤ B) :
    Module.length R (R ⧸ J) ≤ B :=
  (ideal_quotient_length_le haJ).trans hbound

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalizedComponent
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

variable {R : Type*} [CommRing R]

theorem radical_mem_minimalPrimes (I : Ideal R) [I.radical.IsPrime] :
    I.radical ∈ I.minimalPrimes := by
  rw [← Ideal.radical_minimalPrimes, Ideal.minimalPrimes_eq_subsingleton_self]
  exact Set.mem_singleton _

theorem mem_minimalPrimes_of_localized_radical
    (I P : Ideal R) [P.IsPrime]
    (hrad : (I.map (algebraMap R (Localization.AtPrime P))).radical =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    P ∈ I.minimalPrimes := by
  have hp : (I.map (algebraMap R (Localization.AtPrime P))).radical.IsPrime := by
    rw [hrad]
    infer_instance
  let := hp
  have hm := radical_mem_minimalPrimes (I.map (algebraMap R (Localization.AtPrime P)))
  rw [hrad, IsLocalization.minimalPrimes_map P.primeCompl (Localization.AtPrime P)] at hm
  change (IsLocalRing.maximalIdeal (Localization.AtPrime P)).comap
    (algebraMap R (Localization.AtPrime P)) ∈ I.minimalPrimes at hm
  simpa only [Localization.AtPrime.under_maximalIdeal] using hm

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalizedRadical
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

variable {R : Type*} [CommRing R]

theorem localized_radical_eq_maximal_of_mem_minimalPrimes
    (I P : Ideal R) [P.IsPrime] (hP : P ∈ I.minimalPrimes) :
    (I.map (algebraMap R (Localization.AtPrime P))).radical =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
  have hreverse : P.map (algebraMap R (Localization.AtPrime P)) ≤
      (I.map (algebraMap R (Localization.AtPrime P))).radical := by
    rw [Ideal.radical_eq_sInf, le_sInf_iff]
    rintro q ⟨hqI, hq⟩
    obtain ⟨hqprime, hqP⟩ :=
      ((IsLocalization.AtPrime.orderIsoOfPrime (Localization.AtPrime P) P) ⟨q, hq⟩).2
    rw [Ideal.map_le_iff_le_comap] at hqI ⊢
    exact hP.2 ⟨hqprime, hqI⟩ hqP
  have hmprime : (IsLocalRing.maximalIdeal (Localization.AtPrime P)).IsPrime := inferInstance
  apply le_antisymm
  · apply hmprime.radical_le_iff.mpr
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hP.1.2
  · simpa only [Localization.AtPrime.map_eq_maximalIdeal] using hreverse

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularDegreePositivity
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegel.W20

open scoped BigOperators

section Ring

variable {R : Type*} [CommRing R]

theorem regular_sequence_ideal_ne_top (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) : Ideal.ofList rs ≠ ⊤ := by
  intro htop
  apply hreg.top_ne_smul
  have hmul : (Ideal.ofList rs • (⊤ : Submodule R R)) = Ideal.ofList rs :=
    (Ideal.ofList rs).mul_top
  rw [hmul, htop]

end Ring

end PiExponentSiegel.W20

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularParameterAvoidance
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open IsLocalRing RingTheory.Sequence
namespace PiExponentSiegel.W58

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

theorem isSMulRegular_of_avoids_associatedPrimes
    (M : Type*) [AddCommGroup M] [Module R M] (x : R)
    (hx : ∀ P : Ideal R, IsAssociatedPrime P M → x ∉ P) :
    IsSMulRegular M x := by
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro y hy
  by_contra hne
  have hzero : x ∈ {r : R | ∃ z : M, z ≠ 0 ∧ r • z = 0} := ⟨y, hne, hy⟩
  rw [← biUnion_associatedPrimes_eq_zero_divisors R M] at hzero
  obtain ⟨P, hP, hxP⟩ := Set.mem_iUnion₂.mp hzero
  exact hx P hP hxP

variable [IsLocalRing R]

omit [IsNoetherianRing R] in
theorem regular_append_singleton_of_quotient_smulRegular
    (rs : List R) (hreg : IsRegular R rs) (x : R)
    (hx : x ∈ maximalIdeal R)
    (hregular : IsSMulRegular (R ⧸ Ideal.ofList rs) x) :
    IsRegular R (rs ++ [x]) := by
  apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
    (M := R) (rs := rs ++ [x]) ?_).mpr
  · apply (isWeaklyRegular_append_iff R rs [x]).mpr
    refine ⟨hreg.toIsWeaklyRegular, ?_⟩
    have heq : (Ideal.ofList rs • (⊤ : Submodule R R)) = Ideal.ofList rs :=
      (Ideal.ofList rs).mul_top
    rw [heq, isWeaklyRegular_singleton_iff]
    exact hregular
  · intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact (le_maximalIdeal (PiExponentSiegel.W20.regular_sequence_ideal_ne_top rs hreg))
        (Ideal.subset_span hy)
    · have heq : y = x := List.mem_singleton.mp hy
      simpa only [heq] using hx

variable {k J : Type*} [Field k] [Infinite k] [Algebra k R]

theorem exists_constant_regular_extension
    (generators : J → R)
    (hrad : (Ideal.span (Set.range generators)).radical = maximalIdeal R)
    (rs : List R) (hreg : IsRegular R rs)
    (hnot : ¬ IsAssociatedPrime (maximalIdeal R) (R ⧸ Ideal.ofList rs)) :
    ∃ c : J →₀ k,
      Finsupp.linearCombination k generators c ∈ Ideal.span (Set.range generators) ∧
      IsRegular R (rs ++ [Finsupp.linearCombination k generators c]) := by
  classical
  let ass := associatedPrimes R (R ⧸ Ideal.ofList rs)
  let : Fintype ass := (associatedPrimes.finite R (R ⧸ Ideal.ofList rs)).fintype
  have hbelow (P : ass) : P.val < maximalIdeal R := by
    refine lt_iff_le_and_ne.mpr ⟨le_maximalIdeal P.property.isPrime.ne_top, ?_⟩
    intro heq
    exact hnot (heq ▸ P.property)
  obtain ⟨c, hc⟩ := PiExponentSiegel.W20.exists_linearCombination_avoiding_primes_below_radical
    (K := k) generators (maximalIdeal R) hrad (fun P : ass => P.val)
    (fun P => P.property.isPrime) hbelow
  have hlin : Finsupp.linearCombination k generators c ∈
      Submodule.span k (Set.range generators) := by
    rw [← Finsupp.range_linearCombination]
    exact ⟨c, rfl⟩
  have hspan : Submodule.span k (Set.range generators) ≤
      (Ideal.span (Set.range generators)).restrictScalars k := by
    apply Submodule.span_le.mpr
    exact fun _ h => Ideal.subset_span h
  have hin : Finsupp.linearCombination k generators c ∈
      Ideal.span (Set.range generators) := hspan hlin
  refine ⟨c, hin, regular_append_singleton_of_quotient_smulRegular rs hreg _ ?_ ?_⟩
  · rw [← hrad]
    exact Ideal.le_radical hin
  · apply isSMulRegular_of_avoids_associatedPrimes
    intro P hP
    exact hc ⟨P, hP⟩

end PiExponentSiegel.W58

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularParameterSelection2
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open IsLocalRing RingTheory.Sequence
namespace PiExponentSiegel.W58

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

theorem regular_full_length_radical_eq_maximalIdeal (rs : List R)
    (hreg : IsRegular R rs) (hdim : ringKrullDim R = rs.length) :
    (Ideal.ofList rs).radical = maximalIdeal R := by
  let I := Ideal.ofList rs
  have hproper : I ≠ ⊤ := PiExponentSiegel.W20.regular_sequence_ideal_ne_top rs hreg
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hproper
  let : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hzero : ringKrullDim (R ⧸ I) = 0 := by
    apply (ENat.WithBot.add_natCast_cancel (c := rs.length)).mp
    simpa only [zero_add, hdim] using
      ringKrullDim_add_length_eq_ringKrullDim_of_isRegular rs hreg
  let : Ring.KrullDimLE 0 (R ⧸ I) :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hzero
  have hnil := Ring.KrullDimLE.radical_eq_maximalIdeal
    (⊥ : Ideal (R ⧸ I)) bot_ne_top
  have hc := congrArg (Ideal.comap (Ideal.Quotient.mk I)) hnil
  rw [Ideal.comap_radical, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
    IsLocalRing.maximalIdeal_comap] at hc
  exact hc

variable {k J : Type*} [Field k] [Infinite k] [Algebra k R]

omit [IsNoetherianRing R] [IsLocalRing R] [Infinite k] in
theorem constant_linearCombination_mem_ideal (generators : J → R) (c : J →₀ k) :
    Finsupp.linearCombination k generators c ∈ Ideal.span (Set.range generators) := by
  have hspan : Submodule.span k (Set.range generators) ≤
      (Ideal.span (Set.range generators)).restrictScalars k :=
    Submodule.span_le.mpr (fun _ h => Ideal.subset_span h)
  apply hspan
  rw [← Finsupp.range_linearCombination]
  exact ⟨c, rfl⟩

theorem exists_constant_regular_parameters_of_no_maximal_associated
    (generators : J → R)
    (hrad : (Ideal.span (Set.range generators)).radical = maximalIdeal R)
    (h : ℕ) (hdim : ringKrullDim R = h)
    (hnot : ∀ rs : List R, IsRegular R rs → rs.length < h →
      ¬ IsAssociatedPrime (maximalIdeal R) (R ⧸ Ideal.ofList rs)) :
    ∃ cs : List (J →₀ k), cs.length = h ∧
      IsRegular R (cs.map (Finsupp.linearCombination k generators)) ∧
      Ideal.ofList (cs.map (Finsupp.linearCombination k generators)) ≤
        Ideal.span (Set.range generators) ∧
      (Ideal.ofList (cs.map (Finsupp.linearCombination k generators))).radical =
        maximalIdeal R := by
  have build : ∀ t : ℕ, t ≤ h → ∃ cs : List (J →₀ k), cs.length = t ∧
      IsRegular R (cs.map (Finsupp.linearCombination k generators)) := by
    intro t
    induction t with
    | zero =>
      intro _
      exact ⟨[], rfl, IsRegular.nil R R⟩
    | succ t ih =>
      intro ht
      obtain ⟨cs, hlen, hreg⟩ := ih (Nat.le_trans (Nat.le_succ t) ht)
      have hshort : (cs.map (Finsupp.linearCombination k generators)).length < h := by
        simpa only [List.length_map, hlen] using (Nat.lt_of_succ_le ht)
      obtain ⟨c, _, hc⟩ := exists_constant_regular_extension (k := k) generators hrad _ hreg
        (hnot _ hreg hshort)
      refine ⟨cs ++ [c], by simp [hlen], ?_⟩
      simpa only [List.map_append, List.map_cons, List.map_nil] using hc
  obtain ⟨cs, hlen, hreg⟩ := build h le_rfl
  refine ⟨cs, hlen, hreg, ?_, regular_full_length_radical_eq_maximalIdeal _ hreg ?_⟩
  · apply Ideal.span_le.mpr
    intro x hx
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
    exact constant_linearCombination_mem_ideal generators c
  · simpa only [List.length_map, hlen] using hdim

end PiExponentSiegel.W58

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularParameterSelection
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe u
open IsLocalRing RingTheory.Sequence CategoryTheory CategoryTheory.Abelian
namespace PiExponentSiegel.W58

variable (k : Type u) [Field k] (n : ℕ)
variable (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]

variable [Infinite k]

theorem polynomialLocal_exists_constant_regular_parameters
    {J : Type*} (generators : J → Localization.AtPrime P)
    (hrad : (Ideal.span (Set.range generators)).radical =
      maximalIdeal (Localization.AtPrime P))
    (h : ℕ) (hheight : P.height = (h : ℕ∞)) :
    ∃ cs : List (J →₀ k), cs.length = h ∧
      IsRegular (Localization.AtPrime P)
        (cs.map (Finsupp.linearCombination k generators)) ∧
      Ideal.ofList (cs.map (Finsupp.linearCombination k generators)) ≤
        Ideal.span (Set.range generators) ∧
      (Ideal.ofList (cs.map (Finsupp.linearCombination k generators))).radical =
        maximalIdeal (Localization.AtPrime P) := by
  apply exists_constant_regular_parameters_of_no_maximal_associated
    (k := k) generators hrad h
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P), hheight]
    rfl
  · intro rs hreg hshort
    apply polynomialLocal_regular_prefix_maximal_not_associated_q68 k n P rs hreg
    rw [hheight]
    exact_mod_cast hshort

theorem polynomialLocal_exists_degree_bounded_regular_parameters
    {J : Type*} (f : J → MvPolynomial (Fin n) k) (d h : ℕ)
    (hdegree : ∀ j, (f j).totalDegree ≤ d)
    (hheight : P.height = (h : ℕ∞))
    (hrad : ((Ideal.span (Set.range f)).map
      (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))).radical =
        maximalIdeal (Localization.AtPrime P)) :
    ∃ cs : List (J →₀ k), cs.length = h ∧
      let gs := cs.map (Finsupp.linearCombination k f)
      gs.length = h ∧
      (∀ g ∈ gs, g.totalDegree ≤ d) ∧
      Ideal.ofList gs ≤ Ideal.span (Set.range f) ∧
      IsRegular (Localization.AtPrime P)
        (gs.map (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))) ∧
      ((Ideal.ofList gs).map
        (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))).radical =
          maximalIdeal (Localization.AtPrime P) := by
  let φ : MvPolynomial (Fin n) k →ₐ[k] Localization.AtPrime P :=
    IsScalarTower.toAlgHom k (MvPolynomial (Fin n) k) (Localization.AtPrime P)
  have hgen : (Ideal.span (Set.range (φ ∘ f))).radical =
      maximalIdeal (Localization.AtPrime P) := by
    change (Ideal.span (Set.range
      (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P) ∘ f))).radical = _
    simpa only [Ideal.map_span, ← Set.range_comp] using hrad
  obtain ⟨cs, hlen, hreg, _, hmax⟩ :=
    polynomialLocal_exists_constant_regular_parameters k n P (φ ∘ f) hgen h hheight
  have hmap : (cs.map (Finsupp.linearCombination k f)).map
      (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P)) =
      cs.map (Finsupp.linearCombination k (φ ∘ f)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro c _
    exact Finsupp.apply_linearCombination k φ.toLinearMap f c
  refine ⟨cs, hlen, by simpa only [List.length_map] using hlen, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hg
    exact PiExponentJets.W22.linearCombination_totalDegree_le f c hdegree
  · apply Ideal.span_le.mpr
    intro g hg
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hg
    exact PiExponentJets.W22.linearCombination_mem_ideal f c _
      (fun j => Ideal.subset_span (Set.mem_range_self j))
  · rwa [hmap]
  · rwa [Ideal.map_ofList, hmap]

end PiExponentSiegel.W58

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalBezout
attribute [-instance] _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent

open PiExponentJets.W22

theorem localIsolatedBezout_q68_oai
    (k : Type) [Field k] [Infinite k] (n : ℕ)
    {J : Type*} (f : J → MvPolynomial (Fin n) k) (D h : ℕ)
    (hdegree : ∀ j, (f j).totalDegree ≤ D)
    (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]
    (hminimal : P ∈ (Ideal.span (Set.range f)).minimalPrimes)
    (hheight : P.height = (h : ℕ∞)) (hbound : h ≤ n) :
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ (Ideal.span (Set.range f)).map
        (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))) ≤
      ((D ^ h : ℕ) : ℕ∞) := by
  have hrad := localized_radical_eq_maximal_of_mem_minimalPrimes
    (Ideal.span (Set.range f)) P hminimal
  obtain ⟨cs, _hcslength, hgslen, hgsdegree, hgscontained, hgsreg, hgsrad⟩ :=
    PiExponentSiegel.W58.polynomialLocal_exists_degree_bounded_regular_parameters
      k n P f D h hdegree hheight hrad
  let gs := cs.map (Finsupp.linearCombination k f)
  have hlen : gs.length = h := hgslen
  have hgsmin : P ∈ (Ideal.ofList gs).minimalPrimes :=
    mem_minimalPrimes_of_localized_radical (Ideal.ofList gs) P hgsrad
  have hselected := affine_local_regular_list_bezout_q68 n P gs D
    hgsdegree hgsreg (hlen.le.trans hbound) hgsmin
  have htransfer := ideal_quotient_length_le_of_bound
    (Ideal.map_mono hgscontained) hselected
  simpa only [hlen] using htransfer

end PiExponent

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PiExponent.localIsolatedBezout_q68_oai.{u_1} := @OAI.PiExponent.localIsolatedBezout_q68_oai.{u_1}
