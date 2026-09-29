-- Prove2me | solution 1 for MvPolynomial.CrossingQuotient.minimalPrimes_span_algebraMap_eq_pair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/7ca1791a-8ec1-58ff-873c-69bf54364c22

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolution
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_CrossingQuotient_minimalPrimes_span_algebraMap_eq_pair

set_option autoImplicit false

namespace CrossingResolutionBranch

open MvPolynomial MvPolynomial.CrossingQuotient

variable {W : Type*} [CommRing W] (s : W)

theorem mk_C_eq (w : W) : mk s (C w) = algebraMap W (CrossingQuotient W s) w := by
  change mk s (algebraMap W (MvPolynomial (Fin 2) W) w) = _
  exact AlgHom.commutes _ w

theorem exists_normalForm (f : CrossingQuotient W s) :
    ∃ p q : Polynomial W, f = Polynomial.aeval (U s) p + V s * Polynomial.aeval (V s) q := by
  obtain ⟨F, rfl⟩ := mk_surjective s f
  induction F using MvPolynomial.induction_on with
  | C a =>
    refine ⟨Polynomial.C a, 0, ?_⟩
    simp only [Polynomial.aeval_C, map_zero, mul_zero, add_zero]
    exact mk_C_eq s a
  | add p q hp hq =>
    obtain ⟨p₁, q₁, h₁⟩ := hp
    obtain ⟨p₂, q₂, h₂⟩ := hq
    refine ⟨p₁ + p₂, q₁ + q₂, ?_⟩
    rw [map_add, h₁, h₂, map_add, map_add]
    ring
  | mul_X p i hp =>
    obtain ⟨P, Q, hPQ⟩ := hp
    have hxy := U_mul_V s
    fin_cases i
    · refine ⟨Polynomial.X * P + Polynomial.C (s * Q.coeff 0), Polynomial.C s * Q.divX, ?_⟩
      have hQ : Polynomial.aeval (V s) Q = V s * Polynomial.aeval (V s) Q.divX +
          algebraMap W _ (Q.coeff 0) := by
        conv_lhs => rw [← Polynomial.X_mul_divX_add Q]
        simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
      rw [map_mul, hPQ]
      simp only [Fin.zero_eta, Fin.isValue, map_add, map_mul, Polynomial.aeval_X,
        Polynomial.aeval_C]
      rw [hQ]
      change _ * U s = U s * _ + _ + _
      linear_combination (Polynomial.aeval (V s) Q.divX * V s + (algebraMap W _ (Q.coeff 0))) * hxy
    · refine ⟨Polynomial.C s * P.divX, Polynomial.C (P.coeff 0) + Polynomial.X * Q, ?_⟩
      have hP : Polynomial.aeval (U s) P = U s * Polynomial.aeval (U s) P.divX +
          algebraMap W _ (P.coeff 0) := by
        conv_lhs => rw [← Polynomial.X_mul_divX_add P]
        simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
      rw [map_mul, hPQ]
      simp only [Fin.mk_one, Fin.isValue, map_add, map_mul, Polynomial.aeval_X,
        Polynomial.aeval_C]
      rw [hP]
      change _ * V s = _
      linear_combination (Polynomial.aeval (U s) P.divX) * hxy

variable (I : Ideal W)

theorem algebraMap_quot_s (hs : s ∈ I) : algebraMap W (Polynomial (W ⧸ I)) s = 0 := by
  rw [Polynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr hs, map_zero]

noncomputable def branchY (hs : s ∈ I) : CrossingQuotient W s →ₐ[W] Polynomial (W ⧸ I) :=
  CrossingQuotient.lift s 0 Polynomial.X (by rw [zero_mul, algebraMap_quot_s s I hs])

noncomputable def branchX (hs : s ∈ I) : CrossingQuotient W s →ₐ[W] Polynomial (W ⧸ I) :=
  CrossingQuotient.lift s Polynomial.X 0 (by rw [mul_zero, algebraMap_quot_s s I hs])

@[scoped simp] theorem branchY_U (hs : s ∈ I) : branchY s I hs (U s) = 0 := lift_U _ _ _ _
@[scoped simp] theorem branchY_V (hs : s ∈ I) : branchY s I hs (V s) = Polynomial.X := lift_V _ _ _ _
@[scoped simp] theorem branchX_U (hs : s ∈ I) : branchX s I hs (U s) = Polynomial.X := lift_U _ _ _ _
@[scoped simp] theorem branchX_V (hs : s ∈ I) : branchX s I hs (V s) = 0 := lift_V _ _ _ _

theorem branchY_aeval_U (hs : s ∈ I) (p : Polynomial W) : branchY s I hs (Polynomial.aeval (U s) p) =
    Polynomial.C (algebraMap W (W ⧸ I) (p.coeff 0)) := by
  rw [← Polynomial.aeval_algHom_apply, branchY_U, ← Polynomial.coeff_zero_eq_aeval_zero',
    Polynomial.algebraMap_apply]

theorem branchY_aeval_V (hs : s ∈ I) (q : Polynomial W) :
    branchY s I hs (Polynomial.aeval (V s) q) = q.map (algebraMap W (W ⧸ I)) := by
  rw [← Polynomial.aeval_algHom_apply, branchY_V, Polynomial.aeval_X_left_eq_map]

theorem branchX_aeval_U (hs : s ∈ I) (p : Polynomial W) :
    branchX s I hs (Polynomial.aeval (U s) p) = p.map (algebraMap W (W ⧸ I)) := by
  rw [← Polynomial.aeval_algHom_apply, branchX_U, Polynomial.aeval_X_left_eq_map]

theorem branchX_aeval_V (hs : s ∈ I) (q : Polynomial W) : branchX s I hs (Polynomial.aeval (V s) q) =
    Polynomial.C (algebraMap W (W ⧸ I) (q.coeff 0)) := by
  rw [← Polynomial.aeval_algHom_apply, branchX_V, ← Polynomial.coeff_zero_eq_aeval_zero',
    Polynomial.algebraMap_apply]

theorem branchY_surjective (hs : s ∈ I) : Function.Surjective (branchY s I hs) := fun g => by
  obtain ⟨G, hG⟩ := Polynomial.map_surjective (algebraMap W (W ⧸ I))
    Ideal.Quotient.mk_surjective g
  exact ⟨Polynomial.aeval (V s) G, by rw [branchY_aeval_V, hG]⟩

theorem branchX_surjective (hs : s ∈ I) : Function.Surjective (branchX s I hs) := fun g => by
  obtain ⟨G, hG⟩ := Polynomial.map_surjective (algebraMap W (W ⧸ I))
    Ideal.Quotient.mk_surjective g
  exact ⟨Polynomial.aeval (U s) G, by rw [branchX_aeval_U, hG]⟩

theorem aeval_mem_map_of_map_eq_zero {A : Type*} [CommRing A] [Algebra W A] (a : A)
    {q : Polynomial W} (hq : q.map (algebraMap W (W ⧸ I)) = 0) :
    Polynomial.aeval a q ∈ I.map (algebraMap W A) := by
  have hmem : q ∈ RingHom.ker (Polynomial.mapRingHom (algebraMap W (W ⧸ I))) := hq
  rw [Polynomial.ker_mapRingHom, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker] at hmem
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
  refine Ideal.sum_mem _ (fun n _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_))
  exact (Ideal.mem_map_C_iff.mp hmem) n

theorem coeff_zero_mem_of_map_eq_zero {q : Polynomial W} (hq : q.map (algebraMap W (W ⧸ I)) = 0) :
    q.coeff 0 ∈ I := by
  have := congrArg (fun g => Polynomial.coeff g 0) hq
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at this
  rwa [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at this

theorem ker_branchY (hs : s ∈ I) : RingHom.ker (branchY s I hs) =
    Ideal.span {U s} ⊔ I.map (algebraMap W (CrossingQuotient W s)) := by
  apply le_antisymm
  · intro f hf
    rw [RingHom.mem_ker] at hf
    obtain ⟨p, q, rfl⟩ := exists_normalForm s f
    rw [map_add, map_mul, branchY_aeval_U, branchY_V, branchY_aeval_V] at hf
    have hq : q.map (algebraMap W (W ⧸ I)) = 0 := by
      ext n
      have := congrArg (fun g => Polynomial.coeff g (n+1)) hf
      simpa [Polynomial.coeff_C, Polynomial.coeff_X_mul] using this
    have hp0 : algebraMap W (W ⧸ I) (p.coeff 0) = 0 := by
      have := congrArg (fun g => Polynomial.coeff g 0) hf
      simpa [hq] using this
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at hp0
    have hP : Polynomial.aeval (U s) p = U s * Polynomial.aeval (U s) p.divX +
        algebraMap W _ (p.coeff 0) := by
      conv_lhs => rw [← Polynomial.X_mul_divX_add p]
      simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [hP]
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
    · exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hp0)
    · exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (aeval_mem_map_of_map_eq_zero I _ hq))
  · rw [sup_le_iff, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, branchY_U,
      Ideal.map_le_iff_le_comap]
    refine ⟨rfl, fun w hw => ?_⟩
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, Polynomial.algebraMap_apply,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hw, map_zero]

theorem ker_branchX (hs : s ∈ I) : RingHom.ker (branchX s I hs) =
    Ideal.span {V s} ⊔ I.map (algebraMap W (CrossingQuotient W s)) := by
  apply le_antisymm
  · intro f hf
    rw [RingHom.mem_ker] at hf
    obtain ⟨p, q, rfl⟩ := exists_normalForm s f
    rw [map_add, map_mul, branchX_aeval_U, branchX_V, zero_mul, add_zero] at hf
    refine Ideal.add_mem _ ?_ ?_
    · exact Ideal.mem_sup_right (aeval_mem_map_of_map_eq_zero I _ hf)
    · exact Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  · rw [sup_le_iff, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, branchX_V,
      Ideal.map_le_iff_le_comap]
    refine ⟨rfl, fun w hw => ?_⟩
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, Polynomial.algebraMap_apply,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hw, map_zero]

theorem algebraMap_mem_span_U : algebraMap W (CrossingQuotient W s) s ∈ Ideal.span {U s} := by
  rw [← U_mul_V]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

theorem algebraMap_mem_span_V : algebraMap W (CrossingQuotient W s) s ∈ Ideal.span {V s} := by
  rw [← U_mul_V]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

theorem map_span_le_span_U :
    (Ideal.span {s}).map (algebraMap W (CrossingQuotient W s)) ≤ Ideal.span {U s} := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
  exact algebraMap_mem_span_U s

theorem map_span_le_span_V :
    (Ideal.span {s}).map (algebraMap W (CrossingQuotient W s)) ≤ Ideal.span {V s} := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
  exact algebraMap_mem_span_V s

theorem ker_branchY_self : RingHom.ker (branchY s (Ideal.span {s}) (Ideal.mem_span_singleton_self s))
    = Ideal.span {U s} := by
  rw [ker_branchY, sup_eq_left]; exact map_span_le_span_U s

theorem ker_branchX_self : RingHom.ker (branchX s (Ideal.span {s}) (Ideal.mem_span_singleton_self s))
    = Ideal.span {V s} := by
  rw [ker_branchX, sup_eq_left]; exact map_span_le_span_V s

end CrossingResolutionBranch
p2m_reactivate "P2MW.S_MvPolynomial_CrossingQuotient_minimalPrimes_span_algebraMap_eq_pair.CrossingResolutionBranch"

namespace CrossingResolutionR3b

open MvPolynomial MvPolynomial.CrossingQuotient CrossingResolutionBranch

variable {W : Type*} [CommRing W] (t : W)

theorem V_notMem_span_U [Nontrivial (W ⧸ Ideal.span {t})] : V t ∉ Ideal.span {U t} := by
  intro h
  rw [← ker_branchY_self t, RingHom.mem_ker, branchY_V] at h
  exact Polynomial.X_ne_zero h

theorem U_notMem_span_V [Nontrivial (W ⧸ Ideal.span {t})] : U t ∉ Ideal.span {V t} := by
  intro h
  rw [← ker_branchX_self t, RingHom.mem_ker, branchX_U] at h
  exact Polynomial.X_ne_zero h

theorem span_t_le_span_U : Ideal.span {algebraMap W (CrossingQuotient W t) t} ≤ Ideal.span {U t} := by
  rw [Ideal.span_singleton_le_iff_mem]; exact algebraMap_mem_span_U t

theorem span_t_le_span_V : Ideal.span {algebraMap W (CrossingQuotient W t) t} ≤ Ideal.span {V t} := by
  rw [Ideal.span_singleton_le_iff_mem]; exact algebraMap_mem_span_V t

theorem le_or_le_of_isPrime {q : Ideal (CrossingQuotient W t)} (hq : q.IsPrime)
    (hle : Ideal.span {algebraMap W (CrossingQuotient W t) t} ≤ q) :
    Ideal.span {U t} ≤ q ∨ Ideal.span {V t} ≤ q := by
  have ht : U t * V t ∈ q := by
    rw [U_mul_V]; exact hle (Ideal.subset_span rfl)
  rcases hq.mem_or_mem ht with h | h
  · left; rwa [Ideal.span_singleton_le_iff_mem]
  · right; rwa [Ideal.span_singleton_le_iff_mem]

variable [IsDomain (W ⧸ Ideal.span {t})]

theorem isPrime_span_U : (Ideal.span {U t}).IsPrime := by
  rw [← ker_branchY_self t]; exact RingHom.ker_isPrime _

theorem isPrime_span_V : (Ideal.span {V t}).IsPrime := by
  rw [← ker_branchX_self t]; exact RingHom.ker_isPrime _

theorem main :
    (Ideal.span {algebraMap W (CrossingQuotient W t) t}).minimalPrimes =
        {Ideal.span {U t}, Ideal.span {V t}} ∧
    Ideal.span {U t} ≠ Ideal.span {V t} := by
  have hUV : Ideal.span {U t} ≠ Ideal.span {V t} := fun h =>
    V_notMem_span_U t (h ▸ Ideal.subset_span rfl)
  refine ⟨?_, hUV⟩
  ext p
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hp, hle⟩, hmin⟩
    rcases le_or_le_of_isPrime t hp hle with h | h
    · exact Or.inl (le_antisymm (hmin ⟨isPrime_span_U t, span_t_le_span_U t⟩ h) h)
    · exact Or.inr (le_antisymm (hmin ⟨isPrime_span_V t, span_t_le_span_V t⟩ h) h)
  · rintro (rfl | rfl)
    · refine ⟨⟨isPrime_span_U t, span_t_le_span_U t⟩, fun q ⟨hq, hle⟩ hqU => ?_⟩
      rcases le_or_le_of_isPrime t hq hle with h | h
      · exact h
      · exact absurd (hqU (h (Ideal.subset_span rfl))) (V_notMem_span_U t)
    · refine ⟨⟨isPrime_span_V t, span_t_le_span_V t⟩, fun q ⟨hq, hle⟩ hqV => ?_⟩
      rcases le_or_le_of_isPrime t hq hle with h | h
      · exact absurd (hqV (h (Ideal.subset_span rfl))) (U_notMem_span_V t)
      · exact h

end CrossingResolutionR3b
p2m_reactivate "P2MW.S_MvPolynomial_CrossingQuotient_minimalPrimes_span_algebraMap_eq_pair.CrossingResolutionBranch"

open MvPolynomial MvPolynomial.CrossingQuotient in

theorem solution
    {W : Type*} [CommRing W] (t : W) [IsDomain (W ⧸ Ideal.span {t})] :
    (Ideal.span {algebraMap W (CrossingQuotient W t) t}).minimalPrimes =
        {Ideal.span {U t}, Ideal.span {V t}} ∧
    Ideal.span {U t} ≠ Ideal.span {V t} :=
  CrossingResolutionR3b.main t

end S_MvPolynomial_CrossingQuotient_minimalPrimes_span_algebraMap_eq_pair
end P2MW
export P2MW.S_MvPolynomial_CrossingQuotient_minimalPrimes_span_algebraMap_eq_pair (solution)
