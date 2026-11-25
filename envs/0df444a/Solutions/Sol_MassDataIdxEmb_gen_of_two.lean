-- Prove2me | solution 1 for MassDataIdxEmb.gen_of_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:29:27.245239+00:00
-- url     : https://prove2.me/submissions/ad8e62ed-82d6-4780-bf50-68027d8c8e3a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_QuadRoot
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_GenOfTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace MassDataIdxEmb
open NumberField IsDedekindDomain Polynomial
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
private theorem mem_iff_algebraMap_mem_of_liesOver (P : Ideal (𝓞 E)) (q : Ideal (𝓞 F)) [P.LiesOver q]
    (c : 𝓞 F) : c ∈ q ↔ algebraMap (𝓞 F) (𝓞 E) c ∈ P := by
  rw [Ideal.over_def P q]
  exact Iff.rfl
private theorem exists_mem_not_mem_of_ne_of_isMaximal {R : Type*} [CommRing R] (Q Q' : Ideal R)
    [hQ : Q.IsMaximal] [hQ' : Q'.IsMaximal] (hne : Q ≠ Q') : ∃ a ∈ Q, a ∉ Q' := by
  by_contra h
  push Not at h
  exact hne (hQ.eq_of_le hQ'.ne_top (fun x hx => h x hx))
end MassDataIdxEmb
end
end

set_option autoImplicit false
noncomputable section
open MassDataIdxEmb
open NumberField IsDedekindDomain Polynomial
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace MassDataIdxEmb
theorem _root_.solution (h2 : Module.finrank F E = 2) (p : HeightOneSpectrum (𝓞 F)) (Q Q' : Ideal (𝓞 E)) [hQ : Q.IsMaximal]
    [hQ' : Q'.IsMaximal] (hne : Q ≠ Q') [Q.LiesOver p.asIdeal] [Q'.LiesOver p.asIdeal] :
    ∃ a : 𝓞 E, ∃ c0 c1 : 𝓞 F, (∀ c : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) c ≠ a) ∧
      a * a + algebraMap (𝓞 F) (𝓞 E) c1 * a + algebraMap (𝓞 F) (𝓞 E) c0 = 0 ∧
      minpoly (𝓞 F) a = X ^ 2 + C c1 * X + C c0 ∧ (minpoly (𝓞 F) a).natDegree = 2 ∧
      c0 ∈ p.asIdeal ∧ c1 ∉ p.asIdeal := by
  obtain ⟨a, ha, ha'⟩ := exists_mem_not_mem_of_ne_of_isMaximal Q Q' hne
  have hnot : ∀ c : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) c ≠ a := by
    intro c hc
    apply ha'
    have hcQ : c ∈ p.asIdeal := (mem_iff_algebraMap_mem_of_liesOver Q p.asIdeal c).2 (by rw [hc]; exact ha)
    rw [← hc]
    exact (mem_iff_algebraMap_mem_of_liesOver Q' p.asIdeal c).1 hcQ
  have hint_r : IsIntegral (𝓞 F) a := Algebra.IsIntegral.isIntegral a
  have hFE : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  have hfield : minpoly F (algebraMap (𝓞 E) E a) = (minpoly (𝓞 F) a).map (algebraMap (𝓞 F) F) :=
    minpoly.isIntegrallyClosed_eq_field_fractions F E hint_r
  have hle : (minpoly (𝓞 F) a).natDegree ≤ 2 := by
    have h : (minpoly F (algebraMap (𝓞 E) E a)).natDegree ≤ Module.finrank F E := by
      apply minpoly.natDegree_le
    rw [hfield, (minpoly.monic hint_r).natDegree_map, h2] at h
    exact h
  have hpos : 0 < (minpoly (𝓞 F) a).natDegree := minpoly.natDegree_pos hint_r
  have hne1 : (minpoly (𝓞 F) a).natDegree ≠ 1 := by
    intro h1
    have hX := (minpoly.monic hint_r).eq_X_add_C h1
    have hev := minpoly.aeval (𝓞 F) a
    rw [hX] at hev
    simp only [map_add, aeval_X, aeval_C] at hev
    apply hnot (-(minpoly (𝓞 F) a).coeff 0)
    rw [map_neg]
    linear_combination -hev
  have hdeg : (minpoly (𝓞 F) a).natDegree = 2 := by omega
  have hP : minpoly (𝓞 F) a =
      X ^ 2 + C ((minpoly (𝓞 F) a).coeff 1) * X + C ((minpoly (𝓞 F) a).coeff 0) := by
    refine (minpoly.monic hint_r).as_sum.trans ?_
    rw [hdeg]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, mul_one,
      zero_add]
    ring
  have hev := minpoly.aeval (𝓞 F) a
  rw [hP] at hev
  simp only [map_add, map_mul, map_pow, aeval_X, aeval_C] at hev
  have heq : a * a + algebraMap (𝓞 F) (𝓞 E) ((minpoly (𝓞 F) a).coeff 1) * a +
      algebraMap (𝓞 F) (𝓞 E) ((minpoly (𝓞 F) a).coeff 0) = 0 := by
    linear_combination hev
  have hc0 : (minpoly (𝓞 F) a).coeff 0 ∈ p.asIdeal := by
    refine (mem_iff_algebraMap_mem_of_liesOver Q p.asIdeal _).2 ?_
    have h : algebraMap (𝓞 F) (𝓞 E) ((minpoly (𝓞 F) a).coeff 0) =
        -(a * (a + algebraMap (𝓞 F) (𝓞 E) ((minpoly (𝓞 F) a).coeff 1))) := by
      linear_combination heq
    rw [h]
    exact neg_mem (Q.mul_mem_right _ ha)
  have hc1 : (minpoly (𝓞 F) a).coeff 1 ∉ p.asIdeal := by
    intro h
    have h1 := (mem_iff_algebraMap_mem_of_liesOver Q' p.asIdeal _).1 h
    have h0 := (mem_iff_algebraMap_mem_of_liesOver Q' p.asIdeal _).1 hc0
    have haa : a * a ∈ Q' := by
      have h' : a * a = -(algebraMap (𝓞 F) (𝓞 E) ((minpoly (𝓞 F) a).coeff 1) * a +
          algebraMap (𝓞 F) (𝓞 E) ((minpoly (𝓞 F) a).coeff 0)) := by
        linear_combination heq
      rw [h']
      exact neg_mem (add_mem (Q'.mul_mem_right _ h1) h0)
    rcases hQ'.isPrime.mem_or_mem haa with h | h <;> exact ha' h
  exact ⟨a, _, _, hnot, heq, hP, hdeg, hc0, hc1⟩
end MassDataIdxEmb
