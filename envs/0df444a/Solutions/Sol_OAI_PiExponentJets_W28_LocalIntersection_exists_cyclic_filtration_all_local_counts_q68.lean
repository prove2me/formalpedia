-- Prove2me | solution 1 for OAI.PiExponentJets.W28.LocalIntersection.exists_cyclic_filtration_all_local_counts_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T08:59:27.114984+00:00
-- url     : https://prove2.me/submissions/cb4b983f-7cbc-4c57-bb99-ab193b182a06

import Mathlib
import Definitions.Def_OAIQ068A003
import Theorems.Thm_OAI_PiExponentJets_W22_localized_cyclic_filtration_length_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalIntersectionPrimeFiltration
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

open scoped BigOperators

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

omit [IsNoetherianRing A] in
theorem quotient_annihilator_eq_colon (J : Ideal A) (f : A) :
    (⊥ : Submodule A (A ⧸ J)).colon {J.mkQ f} = J.colon {f} := by
  ext a
  simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
  change a • J.mkQ f = 0 ↔ a * f ∈ J
  rw [← J.mkQ.map_smul, smul_eq_mul, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]

theorem exists_cyclic_prime_filtration_nat :
    ∃ (n : ℕ) (J : ℕ → Ideal A) (f : ℕ → A),
      (∀ i, J i ≤ J (i + 1)) ∧ J 0 = ⊥ ∧ J n = ⊤ ∧
      ∀ i < n, ((J i).colon {f i}).IsPrime ∧
        J (i + 1) = J i ⊔ Ideal.span {f i} := by
  classical
  obtain ⟨s, hshead, hslast⟩ :=
    IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime A A
  have hsmono : Monotone s := Fin.monotone_iff_le_succ.mpr fun i => (s.step i).1
  let J : ℕ → Ideal A := fun i =>
    s ⟨min i s.length, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hd : ∀ i : Fin s.length, ∃ f : A,
      ((s i.castSucc).colon {f}).IsPrime ∧
        s i.succ = s i.castSucc ⊔ Ideal.span {f} := by
    intro i
    obtain ⟨f, hp, hf⟩ :=
      Submodule.isQuotientEquivQuotientPrime_iff.mp (s.step i)
    exact ⟨f, by simpa only [quotient_annihilator_eq_colon] using hp, hf⟩
  let generators : Fin s.length → A := fun i => (hd i).choose
  let f : ℕ → A := fun i => if hi : i < s.length then generators ⟨i, hi⟩ else 0
  refine ⟨s.length, J, f, ?_, ?_, ?_, ?_⟩
  · intro i
    apply hsmono
    exact min_le_min_right s.length (Nat.le_succ i)
  · change s.head = (⊥ : Submodule A A)
    exact hshead
  · simpa only [J, min_self, RelSeries.last, Fin.last] using hslast
  · intro i hi
    have hleft : J i = s (Fin.castSucc ⟨i, hi⟩) := by
      apply congrArg s
      apply Fin.ext
      exact min_eq_left (Nat.le_of_lt hi)
    have hright : J (i + 1) = s (Fin.succ ⟨i, hi⟩) := by
      apply congrArg s
      apply Fin.ext
      exact min_eq_left (Nat.succ_le_of_lt hi)
    simpa only [f, dite_eq_left hi, generators, hleft, hright] using (hd ⟨i, hi⟩).choose_spec

theorem exists_cyclic_filtration_all_local_counts_q68_oai :
    ∃ (n : ℕ) (J : ℕ → Ideal A) (f : ℕ → A),
      (∀ i, J i ≤ J (i + 1)) ∧ J 0 = ⊥ ∧ J n = ⊤ ∧
      (∀ i < n, ((J i).colon {f i}).IsPrime ∧
        J (i + 1) = J i ⊔ Ideal.span {f i}) ∧
      ∀ (P : Ideal A) [P.IsPrime], P ∈ minimalPrimes A →
        Module.length (Localization.AtPrime P)
          (Localization.AtPrime P ⧸ (⊥ : Ideal A).map
            (algebraMap A (Localization.AtPrime P))) =
          ∑ i ∈ Finset.range n, if (J i).colon {f i} = P then 1 else 0 := by
  obtain ⟨n, J, f, hmono, hstart, hend, hstep⟩ :=
    exists_cyclic_prime_filtration_nat (A := A)
  refine ⟨n, J, f, hmono, hstart, hend, hstep, ?_⟩
  intro P hP hp
  exact W22.localized_cyclic_filtration_length_q68 ⊥ P hp J hmono hstart n hend f
    (fun i hi => (hstep i hi).2) (fun i hi => (hstep i hi).1)

end PiExponentJets.W28.LocalIntersection

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PiExponentJets.W28.LocalIntersection.exists_cyclic_filtration_all_local_counts_q68_oai.{u_1} := @OAI.PiExponentJets.W28.LocalIntersection.exists_cyclic_filtration_all_local_counts_q68_oai.{u_1}
