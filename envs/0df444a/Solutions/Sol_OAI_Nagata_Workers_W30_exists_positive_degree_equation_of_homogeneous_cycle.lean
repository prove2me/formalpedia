-- Prove2me | solution 1 for OAI.Nagata.Workers.W30.exists_positive_degree_equation_of_homogeneous_cycle
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T08:34:54.524779+00:00
-- url     : https://prove2.me/submissions/29aaf5c8-e7ee-4d2c-abe7-f3f1f5dbd773

import Mathlib
import Definitions.Def_Nagata
import Definitions.Def_OAIQ7T1000

section
-- module Solutions.OAIQ7_T1.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ7_T1.PlaneCurves_Factorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Homogeneous factorization and height-one prime generators
-/

section

namespace Nagata.Workers.W30

open UniqueFactorizationMonoid

noncomputable section

attribute [local instance] OAI.Nagata.Workers.W30.instDecidableEqAssociatesTernaryPolynomial
/-- No equation multiplicity is discarded: equality of canonical multiplicity
vectors is equivalent to association of nonzero polynomial equations. -/
theorem equationMultiplicity_eq_iff {F G : TernaryPolynomial} (hF : F ≠ 0) (hG : G ≠ 0) :
    equationMultiplicity F = equationMultiplicity G ↔ Associated F G := by
  constructor
  · intro h
    have ha := associated_of_factorization_eq (Associates.mk F) (Associates.mk G)
      (Associates.mk_ne_zero.mpr hF) (Associates.mk_ne_zero.mpr hG) h
    exact Associates.mk_eq_mk_iff_associated.mp (associated_iff_eq.mp ha)
  · intro h
    unfold equationMultiplicity
    rw [Associates.mk_eq_mk_iff_associated.mpr h]

theorem associatePrincipalIdeal_injective : Function.Injective associatePrincipalIdeal := by
  intro a b h
  apply (Ideal.associatesEquivIsPrincipal TernaryPolynomial).injective
  exact Subtype.ext h

theorem equationIdealCycle_eq_iff {F G : TernaryPolynomial} (hF : F ≠ 0) (hG : G ≠ 0) :
    equationIdealCycle F = equationIdealCycle G ↔ Associated F G := by
  change Finsupp.mapDomain associatePrincipalIdeal (equationMultiplicity F) =
    Finsupp.mapDomain associatePrincipalIdeal (equationMultiplicity G) ↔ _
  rw [(Finsupp.mapDomain_injective associatePrincipalIdeal_injective).eq_iff,
    equationMultiplicity_eq_iff hF hG]

/-- Each cycle coefficient is the full factor multiplicity, without merging
nonassociated factors. -/
theorem equationIdealCycle_coefficient (F : TernaryPolynomial)
    (a : Associates TernaryPolynomial) :
    equationIdealCycle F (associatePrincipalIdeal a) = equationMultiplicity F a := by
  exact Finsupp.mapDomain_apply associatePrincipalIdeal_injective _ _

end
end Nagata.Workers.W30

end

section

/-! Homogeneous factorization by degree induction on actual multivariate polynomials. -/

namespace Nagata.Workers.W30

open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [Field K]

/-- The top homogeneous component never vanishes for a nonzero polynomial. -/
lemma topHomogeneousComponent_ne_zero {p : MvPolynomial σ K} (hp : p ≠ 0) :
    homogeneousComponent p.totalDegree p ≠ 0 := by
  classical
  obtain ⟨a,ha,hdeg⟩ := Finset.exists_mem_eq_sup p.support
    (support_nonempty.mpr hp) (fun a => a.sum fun _ e => e)
  intro hz
  have hz' := congrArg (fun polynomial : MvPolynomial σ K => polynomial.coeff a) hz
  have heq : a.degree = p.totalDegree := hdeg.symm
  have hc : p.coeff a = 0 := by
    simpa [coeff_homogeneousComponent, heq] using hz'
  exact (mem_support_iff.mp ha) hc

/-- Only the two top-degree components contribute to the top component of a product. -/
lemma topHomogeneousComponent_mul (p q : MvPolynomial σ K) :
    homogeneousComponent (p.totalDegree + q.totalDegree) (p*q) =
      homogeneousComponent p.totalDegree p * homogeneousComponent q.totalDegree q := by
  classical
  have hdecomp : p*q =
      (∑ i ∈ Finset.range (p.totalDegree+1), homogeneousComponent i p) *
      (∑ j ∈ Finset.range (q.totalDegree+1), homogeneousComponent j q) := by
    rw [sum_homogeneousComponent, sum_homogeneousComponent]
  rw [hdecomp]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, map_sum]
  rw [Finset.sum_eq_single p.totalDegree]
  · rw [Finset.sum_eq_single q.totalDegree]
    · rw [homogeneousComponent_of_mem
        ((homogeneousComponent_isHomogeneous p.totalDegree p).mul
          (homogeneousComponent_isHomogeneous q.totalDegree q))]
      simp
    · intro j hj hne
      rw [homogeneousComponent_of_mem
        ((homogeneousComponent_isHomogeneous p.totalDegree p).mul
          (homogeneousComponent_isHomogeneous j q))]
      simp only [ite_eq_right_iff]
      intro h
      exfalso
      apply hne
      omega
    · simp
  · intro i hi hne
    apply Finset.sum_eq_zero
    intro j hj
    rw [homogeneousComponent_of_mem
      ((homogeneousComponent_isHomogeneous i p).mul
        (homogeneousComponent_isHomogeneous j q))]
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have hne' : p.totalDegree + q.totalDegree ≠ i+j := by omega
    simp [hne']
  · simp

lemma degree_pos_of_nonzero_nonunit {p : MvPolynomial σ K} (hp : p ≠ 0)
    (hu : ¬ IsUnit p) : 0 < p.totalDegree := by
  by_contra hn
  have hz : p.totalDegree = 0 := by omega
  have heq := totalDegree_eq_zero_iff_eq_C.mp hz
  have hc : p.coeff 0 ≠ 0 := by
    intro hc
    apply hp
    rw [heq,hc,C_0]
  apply hu
  rw [heq]
  exact (isUnit_iff_ne_zero.mpr hc).map C

/-- Every nonzero homogeneous polynomial is, up to a unit, a finite product of
irreducible homogeneous polynomials. Repeated factors are retained in the multiset. -/
theorem exists_homogeneous_irreducible_factors (p : MvPolynomial σ K) {d : ℕ}
    (hp : p ≠ 0) (hhom : p.IsHomogeneous d) :
    ∃ L : Multiset (MvPolynomial σ K),
      (∀ P ∈ L, Irreducible P ∧ P.IsHomogeneous P.totalDegree) ∧ Associated L.prod p := by
  classical
  suffices H : ∀ n (p : MvPolynomial σ K), p.totalDegree = n → p ≠ 0 →
      p.IsHomogeneous n → ∃ L : Multiset (MvPolynomial σ K),
      (∀ P ∈ L, Irreducible P ∧ P.IsHomogeneous P.totalDegree) ∧ Associated L.prod p from
    H d p (hhom.totalDegree hp) hp hhom
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p hdeg hp hhom
    by_cases hu : IsUnit p
    · refine ⟨0, by simp, ?_⟩
      simpa using (associated_one_iff_isUnit.mpr hu).symm
    rcases irreducible_or_factor hu with hirr | ⟨a,b,hau,hbu,hab⟩
    · refine ⟨{p}, ?_, ?_⟩
      · intro P hP
        have heq : P = p := Multiset.mem_singleton.mp hP
        subst P
        exact ⟨hirr, by simpa only [hdeg] using hhom⟩
      · simp
    · have ha : a ≠ 0 := by intro h; simp [h] at hab; exact hp hab
      have hb : b ≠ 0 := by intro h; simp [h] at hab; exact hp hab
      have hsum : a.totalDegree+b.totalDegree = n := by
        rw [← totalDegree_mul_of_isDomain ha hb, ← hab, hdeg]
      have hapos := degree_pos_of_nonzero_nonunit ha hau
      have hbpos := degree_pos_of_nonzero_nonunit hb hbu
      let A := homogeneousComponent a.totalDegree a
      let B := homogeneousComponent b.totalDegree b
      have hA : A ≠ 0 := topHomogeneousComponent_ne_zero ha
      have hB : B ≠ 0 := topHomogeneousComponent_ne_zero hb
      have hAh : A.IsHomogeneous a.totalDegree := homogeneousComponent_isHomogeneous _ _
      have hBh : B.IsHomogeneous b.totalDegree := homogeneousComponent_isHomogeneous _ _
      have hprod : A*B = p := by
        change homogeneousComponent a.totalDegree a * homogeneousComponent b.totalDegree b = p
        rw [← topHomogeneousComponent_mul, ← hab, hsum,
          homogeneousComponent_of_mem hhom]
        simp
      obtain ⟨L,hL,hLp⟩ := ih a.totalDegree (by omega) A (hAh.totalDegree hA) hA hAh
      obtain ⟨M,hM,hMp⟩ := ih b.totalDegree (by omega) B (hBh.totalDegree hB) hB hBh
      refine ⟨L+M, ?_, ?_⟩
      · intro P hP
        exact (Multiset.mem_add.mp hP).elim (hL P) (hM P)
      · rw [Multiset.prod_add, ← hprod]
        exact hLp.mul_mul hMp

end Nagata.Workers.W30

end

section

/-! Units preserve genuine homogeneity; all irreducible factors of homogeneous forms are homogeneous. -/
namespace Nagata.Workers.W30
open MvPolynomial UniqueFactorizationMonoid
variable {σ K : Type*} [Field K]

lemma unit_polynomial_totalDegree (u : (MvPolynomial σ K)ˣ) :
    (u : MvPolynomial σ K).totalDegree = 0 := by
  have h := totalDegree_mul_of_isDomain u.ne_zero (u⁻¹).ne_zero
  simp only [← Units.val_mul, mul_inv_cancel, Units.val_one, totalDegree_one] at h
  omega

lemma homogeneous_of_associated {p q : MvPolynomial σ K} {d : ℕ}
    (hp : p.IsHomogeneous d) (h : Associated p q) : q.IsHomogeneous d := by
  obtain ⟨u,rfl⟩ := h
  have hu : (u : MvPolynomial σ K).IsHomogeneous 0 :=
    (totalDegree_zero_iff_isHomogeneous σ).mp (unit_polynomial_totalDegree u)
  simpa only [add_zero] using hp.mul hu

/-- All irreducible factors returned by the actual UFD factorization are homogeneous. -/
theorem factors_homogeneous {p : MvPolynomial σ K} {d : ℕ}
    (hp : p ≠ 0) (hhom : p.IsHomogeneous d) :
    ∀ f ∈ factors p, f.IsHomogeneous f.totalDegree := by
  classical
  obtain ⟨L,hL,hprod⟩ := exists_homogeneous_irreducible_factors p hp hhom
  have hrel : Multiset.Rel Associated (factors p) L :=
    factors_unique irreducible_of_factor (fun f hf => (hL f hf).1)
      ((factors_prod hp).trans hprod.symm)
  intro f hf
  obtain ⟨g,hg,hfg⟩ := Multiset.exists_mem_of_rel_of_mem hrel hf
  have hgHom := homogeneous_of_associated (hL g hg).2 hfg.symm
  have hf0 : f ≠ 0 := (prime_of_factor f hf).ne_zero
  simpa only [hgHom.totalDegree hf0] using hgHom

end Nagata.Workers.W30

end

section

/-! Arbitrary divisors, including reducible and nonreduced divisors, preserve homogeneity. -/
namespace Nagata.Workers.W30
open MvPolynomial UniqueFactorizationMonoid
variable {σ K : Type*} [Field K]

lemma homogeneous_multiset_prod (L : Multiset (MvPolynomial σ K))
    (hL : ∀ f ∈ L, f.IsHomogeneous f.totalDegree) :
    L.prod.IsHomogeneous (L.map MvPolynomial.totalDegree).sum := by
  induction L using Multiset.induction_on with
  | empty => simpa using (isHomogeneous_one σ K)
  | @cons f L ih =>
    simpa only [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons] using
      (hL f (Multiset.mem_cons_self _ _)).mul
        (ih (fun g hg => hL g (Multiset.mem_cons_of_mem hg)))

/-- Every actual polynomial divisor of a nonzero homogeneous polynomial is homogeneous. -/
theorem homogeneous_of_dvd {p f : MvPolynomial σ K} {d : ℕ}
    (hp : p ≠ 0) (hhom : p.IsHomogeneous d) (hf : f ∣ p) :
    f.IsHomogeneous f.totalDegree := by
  classical
  have hf0 : f ≠ 0 := by rintro rfl; exact hp (by simpa using hf)
  have hfac : ∀ a ∈ factors f, a.IsHomogeneous a.totalDegree := by
    intro a ha
    have hairr : Irreducible a := irreducible_of_factor a ha
    have hadvd : a ∣ p :=
      (Multiset.dvd_prod ha).trans ((factors_prod hf0).dvd.trans hf)
    obtain ⟨b,hb,hab⟩ := exists_mem_factors_of_dvd hp hairr hadvd
    have hah := homogeneous_of_associated (factors_homogeneous hp hhom b hb) hab.symm
    simpa only [hah.totalDegree hairr.ne_zero] using hah
  have hprod := homogeneous_multiset_prod (factors f) hfac
  have hfh := homogeneous_of_associated hprod (factors_prod hf0)
  simpa only [hfh.totalDegree hf0] using hfh

end Nagata.Workers.W30

end

section

/-! Homogeneity of a principal ideal is equivalent to genuine polynomial homogeneity. -/
namespace Nagata.Workers.W30
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {σ K : Type*} [Field K]

/-- A homogeneous principal ideal has a homogeneous generator. -/
theorem homogeneous_of_span_homogeneous {f : MvPolynomial σ K} (hf : f ≠ 0)
    (hI : (Ideal.span ({f} : Set (MvPolynomial σ K))).IsHomogeneous
      (homogeneousSubmodule σ K)) : f.IsHomogeneous f.totalDegree := by
  have hfmem : f ∈ Ideal.span ({f} : Set (MvPolynomial σ K)) := Ideal.subset_span (by simp)
  have hcompEq (D : DirectSum.Decomposition (homogeneousSubmodule σ K)) :
      (D.decompose' f f.totalDegree : MvPolynomial σ K) = homogeneousComponent f.totalDegree f := by
    rw [Subsingleton.elim D MvPolynomial.decomposition,
      MvPolynomial.decomposition.decompose'_apply]
  have hcomp := (hI.mem_iff.mp hfmem) f.totalDegree
  rw [← DirectSum.Decomposition.decompose'_eq, hcompEq] at hcomp
  exact homogeneous_of_dvd (topHomogeneousComponent_ne_zero hf)
    (homogeneousComponent_isHomogeneous _ _) (Ideal.mem_span_singleton.mp hcomp)

end Nagata.Workers.W30

end

end OAI
end

section
-- module Solutions.OAIQ7_T1.PlaneCurves_IdealCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reconstruction of effective homogeneous prime ideal cycles
-/

section

/-! Reconstruct an equation from any finite effective cycle of prime associate classes. -/
namespace Nagata.Workers.W30
open UniqueFactorizationMonoid
noncomputable section

theorem cycleEquation_nonzero (D : Associates TernaryPolynomial →₀ ℕ)
    (hD : ∀ a ∈ D.support, Prime a) : cycleEquation D ≠ 0 := by
  classical
  apply Associates.mk_ne_zero.mp
  rw [cycleEquation_mk, ← Finsupp.prod_toMultiset]
  exact Multiset.prod_ne_zero_of_prime D.toMultiset (fun a ha => hD a ((D.mem_toMultiset a).mp ha))

/-- Full multiplicities of an arbitrary finite effective prime cycle are recovered exactly. -/
theorem cycleEquation_multiplicity (D : Associates TernaryPolynomial →₀ ℕ)
    (hD : ∀ a ∈ D.support, Prime a) : equationMultiplicity (cycleEquation D) = D := by
  letI : DecidableEq (Associates TernaryPolynomial) := instDecidableEqAssociatesTernaryPolynomial
  classical
  unfold equationMultiplicity factorization
  rw [cycleEquation_mk, ← Finsupp.prod_toMultiset,
    normalizedFactors_prod_of_prime (fun a ha => hD a ((D.mem_toMultiset a).mp ha)),
    Finsupp.toMultiset_toFinsupp]

theorem cycleEquation_idealCycle (D : Associates TernaryPolynomial →₀ ℕ)
    (hD : ∀ a ∈ D.support, Prime a) :
    equationIdealCycle (cycleEquation D) = D.mapDomain associatePrincipalIdeal := by
  classical
  rw [equationIdealCycle, cycleEquation_multiplicity D hD]

end
end Nagata.Workers.W30

end

section

/-! Zero-cycle exclusion and multiplicities of nonreduced equations. -/
namespace Nagata.Workers.W30

theorem equationIdealCycle_zero_iff {F : TernaryPolynomial} (hF : F ≠ 0) :
    equationIdealCycle F = 0 ↔ IsUnit F := by
  rw [← equationIdealCycle_one, equationIdealCycle_eq_iff hF one_ne_zero,
    associated_one_iff_isUnit]

/-- A nonzero effective cycle has positive polynomial degree. -/
theorem degree_pos_of_equationIdealCycle_ne_zero {F : TernaryPolynomial}
    (hF : F ≠ 0) (hcycle : equationIdealCycle F ≠ 0) : 0 < F.totalDegree := by
  exact degree_pos_of_nonzero_nonunit hF (fun hu => hcycle ((equationIdealCycle_zero_iff hF).mpr hu))

end Nagata.Workers.W30

end

section

/-! Exact divisibility meaning of prime ideal cycle support. -/
namespace Nagata.Workers.W30
open UniqueFactorizationMonoid
noncomputable section

attribute [local instance] OAI.Nagata.Workers.W30.supportAssociateDecidableEq
/-- A principal ideal occurs precisely when its generator is a prime divisor of the equation. -/
theorem span_mem_equationIdealCycle_iff (F f : TernaryPolynomial) (hF : F ≠ 0) :
    Ideal.span ({f} : Set TernaryPolynomial) ∈ (equationIdealCycle F).support ↔
      Prime f ∧ f ∣ F := by
  classical
  rw [Finsupp.mem_support_iff, ← associatePrincipalIdeal_mk,
    equationIdealCycle_coefficient, ← Finsupp.mem_support_iff]
  change Associates.mk f ∈ (factorization (Associates.mk F)).support ↔ _
  rw [support_factorization, Multiset.mem_toFinset,
    mem_normalizedFactors_iff (Associates.mk_ne_zero.mpr hF),
    Associates.prime_mk, Associates.mk_dvd_mk]

end
end Nagata.Workers.W30

end

section

/-! Reconstructing actual finite cycles of nonzero prime principal ideals. -/
namespace Nagata.Workers.W30
noncomputable section

theorem associatePrincipalIdeal_principalIdealAssociate (I : Ideal TernaryPolynomial)
    (hI : I.IsPrincipal) : associatePrincipalIdeal (principalIdealAssociate I) = I := by
  classical
  simp only [principalIdealAssociate, dite_eq_left hI, associatePrincipalIdeal]
  exact congrArg Subtype.val ((Ideal.associatesEquivIsPrincipal TernaryPolynomial).apply_symm_apply ⟨I,hI⟩)

theorem principalIdealAssociate_prime (I : Ideal TernaryPolynomial)
    (hI : I.IsPrime) (hI0 : I ≠ ⊥) (hprin : I.IsPrincipal) :
    Prime (principalIdealAssociate I) := by
  obtain ⟨f,hf⟩ := Associates.mk_surjective (principalIdealAssociate I)
  have hid : Ideal.span ({f} : Set TernaryPolynomial) = I := by
    rw [← associatePrincipalIdeal_mk, hf,
      associatePrincipalIdeal_principalIdealAssociate I hprin]
  have hf0 : f ≠ 0 := by
    intro h
    apply hI0
    rw [← hid,h,Ideal.span_singleton_eq_bot.mpr rfl]
  rw [← hf]
  exact Associates.prime_mk.mpr ((Ideal.span_singleton_prime hf0).mp (hid.symm ▸ hI))

/-- Every finite effective cycle on actual nonzero prime principal ideals is the
factor cycle of a nonzero polynomial. -/
theorem exists_equation_of_prime_principal_cycle (D : Ideal TernaryPolynomial →₀ ℕ)
    (hD : ∀ I ∈ D.support, I.IsPrime ∧ I ≠ ⊥ ∧ I.IsPrincipal) :
    ∃ F : TernaryPolynomial, F ≠ 0 ∧ equationIdealCycle F = D := by
  classical
  let A := D.mapDomain principalIdealAssociate
  have hA : ∀ a ∈ A.support, Prime a := by
    intro a ha
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ha)
    exact principalIdealAssociate_prime I (hD I hI).1 (hD I hI).2.1 (hD I hI).2.2
  refine ⟨cycleEquation A, cycleEquation_nonzero A hA, ?_⟩
  rw [cycleEquation_idealCycle A hA]
  change (D.mapDomain principalIdealAssociate).mapDomain associatePrincipalIdeal = D
  rw [← Finsupp.mapDomain_comp]
  calc
    D.mapDomain (associatePrincipalIdeal ∘ principalIdealAssociate) = D.mapDomain id :=
      Finsupp.mapDomain_congr (fun I hI =>
        associatePrincipalIdeal_principalIdealAssociate I (hD I hI).2.2)
    _ = D := Finsupp.mapDomain_id

end
end Nagata.Workers.W30

end

section

/-! Homogeneous equations correspond to finite effective cycles of homogeneous prime principal ideals. -/
namespace Nagata.Workers.W30
open MvPolynomial UniqueFactorizationMonoid
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section

/-- If every ideal in the factor cycle is homogeneous, the equation is homogeneous. -/
theorem homogeneous_of_equationIdealCycle {F : TernaryPolynomial} (hF : F ≠ 0)
    (hhom : ∀ I ∈ (equationIdealCycle F).support,
      I.IsHomogeneous (homogeneousSubmodule (Fin 3) ℂ)) :
    F.IsHomogeneous F.totalDegree := by
  have hfac : ∀ f ∈ factors F, f.IsHomogeneous f.totalDegree := by
    intro f hf
    have hprime : Prime f := prime_of_factor f hf
    have hdiv : f ∣ F := (Multiset.dvd_prod hf).trans (factors_prod hF).dvd
    have hs := (span_mem_equationIdealCycle_iff F f hF).mpr ⟨hprime,hdiv⟩
    exact homogeneous_of_span_homogeneous hprime.ne_zero (hhom _ hs)
  have hprod := homogeneous_multiset_prod (factors F) hfac
  have hFhom := homogeneous_of_associated hprod (factors_prod hF)
  simpa only [hFhom.totalDegree hF] using hFhom

/-- Every finite effective cycle of actual homogeneous nonzero prime principal ideals
comes from a nonzero homogeneous polynomial, with every multiplicity preserved. -/
theorem exists_homogeneous_equation_of_prime_principal_cycle
    (D : Ideal TernaryPolynomial →₀ ℕ)
    (hD : ∀ I ∈ D.support, I.IsPrime ∧ I ≠ ⊥ ∧ I.IsPrincipal ∧
      I.IsHomogeneous (homogeneousSubmodule (Fin 3) ℂ)) :
    ∃ F : TernaryPolynomial, F ≠ 0 ∧ F.IsHomogeneous F.totalDegree ∧
      equationIdealCycle F = D := by
  obtain ⟨F,hF,hcycle⟩ := exists_equation_of_prime_principal_cycle D
    (fun I hI => ⟨(hD I hI).1,(hD I hI).2.1,(hD I hI).2.2.1⟩)
  refine ⟨F,hF,homogeneous_of_equationIdealCycle hF ?_,hcycle⟩
  intro I hI
  rw [hcycle] at hI
  exact (hD I hI).2.2.2

end
end Nagata.Workers.W30

end

section

/-! Preserve the nonzero-curve and positive-degree conditions in cycle reconstruction. -/
namespace Nagata.Workers.W30
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A nonzero finite effective cycle of homogeneous prime principal ideals is
represented by a nonzero homogeneous equation of positive degree, with exact weights. -/
theorem exists_positive_degree_equation_of_homogeneous_cycle_oai
    (D : Ideal TernaryPolynomial →₀ ℕ) (hD0 : D ≠ 0)
    (hD : ∀ I ∈ D.support, I.IsPrime ∧ I ≠ ⊥ ∧ I.IsPrincipal ∧
      I.IsHomogeneous (homogeneousSubmodule (Fin 3) ℂ)) :
    ∃ F : TernaryPolynomial, F ≠ 0 ∧ F.IsHomogeneous F.totalDegree ∧
      0 < F.totalDegree ∧ equationIdealCycle F = D := by
  obtain ⟨F,hF,hhom,hcycle⟩ := exists_homogeneous_equation_of_prime_principal_cycle D hD
  exact ⟨F,hF,hhom,degree_pos_of_equationIdealCycle_ne_zero hF (hcycle.symm ▸ hD0),hcycle⟩

end Nagata.Workers.W30

end

end OAI
end

theorem solution : type_of% @OAI.Nagata.Workers.W30.exists_positive_degree_equation_of_homogeneous_cycle_oai := @OAI.Nagata.Workers.W30.exists_positive_degree_equation_of_homogeneous_cycle_oai
