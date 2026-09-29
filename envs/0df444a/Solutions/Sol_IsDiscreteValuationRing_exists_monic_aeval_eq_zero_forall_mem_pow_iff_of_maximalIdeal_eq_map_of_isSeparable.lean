-- Prove2me | solution 1 for IsDiscreteValuationRing.exists_monic_aeval_eq_zero_forall_mem_pow_iff_of_maximalIdeal_eq_map_of_isSeparable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/f9d38eaa-0cbc-5b7f-809f-db23970fec9a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_exists_monic_aeval_eq_zero_forall_mem_pow_iff_of_maximalIdeal_eq_map_of_isSeparable

set_option autoImplicit false

open IsLocalRing Polynomial

theorem solution
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀] [Algebra A₀ W₀] [IsLocalHom (algebraMap A₀ W₀)]
    (hW₀ : IsLocalRing.maximalIdeal W₀ = (IsLocalRing.maximalIdeal A₀).map (algebraMap A₀ W₀))
    [Module.Finite (ResidueField A₀) (ResidueField W₀)]
    [Algebra.IsSeparable (ResidueField A₀) (ResidueField W₀)] :
    ∃ (P : Polynomial A₀) (θ : W₀), P.Monic ∧ Irreducible (P.map (residue A₀)) ∧
      (P.map (residue A₀)).Separable ∧ aeval θ P = 0 ∧
      (∀ n : ℕ, ∀ w : W₀, ∃ g : Polynomial A₀, w - aeval θ g ∈ IsLocalRing.maximalIdeal W₀ ^ n) ∧
      (∀ n : ℕ, ∀ g : Polynomial A₀, aeval θ g ∈ IsLocalRing.maximalIdeal W₀ ^ n ↔
        g ∈ Ideal.span {P} ⊔ (IsLocalRing.maximalIdeal A₀ ^ n).map (Polynomial.C : A₀ →+* Polynomial A₀)) := by
  classical

  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ResidueField A₀) (ResidueField W₀)
  have hαint : IsIntegral (ResidueField A₀) α := Algebra.IsIntegral.isIntegral α
  let f : Polynomial (ResidueField A₀) := minpoly (ResidueField A₀) α
  have hfmonic : f.Monic := minpoly.monic hαint
  have hfirr : Irreducible f := minpoly.irreducible hαint
  have hfsep : f.Separable := Algebra.IsSeparable.isSeparable (ResidueField A₀) α
  have hfα : aeval α f = 0 := minpoly.aeval _ _
  have hf0 : f ≠ 0 := hfmonic.ne_zero

  have hres₀surj : Function.Surjective (residue A₀) := residue_surjective
  obtain ⟨P, hPf, -, hPmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.mem_lifts _).mpr (Polynomial.map_surjective (residue A₀) hres₀surj f)) hfmonic
  have hres : (residue W₀).comp (algebraMap A₀ W₀) =
      (algebraMap (ResidueField A₀) (ResidueField W₀)).comp (residue A₀) :=
    RingHom.ext fun a => (IsLocalRing.ResidueField.algebraMap_residue (R := A₀) (S := W₀) a).symm
  have hev : ∀ (g : Polynomial A₀) (x : W₀),
      residue W₀ (aeval x g) = aeval (residue W₀ x) (g.map (residue A₀)) := by
    intro g x
    rw [aeval_def, hom_eval₂, hres, aeval_def, eval₂_map]

  obtain ⟨θ₀, hθ₀⟩ := residue_surjective (R := W₀) α
  have hPW : (P.map (algebraMap A₀ W₀)).Monic := hPmonic.map _
  have hev' : ∀ (g : Polynomial A₀) (x : W₀), (g.map (algebraMap A₀ W₀)).eval x = aeval x g := by
    intro g x; rw [eval_map, ← aeval_def]
  have h1 : (P.map (algebraMap A₀ W₀)).eval θ₀ ∈ maximalIdeal W₀ := by
    rw [hev', ← residue_eq_zero_iff, hev, hθ₀, hPf]; exact hfα
  have h2' : residue W₀ ((P.map (algebraMap A₀ W₀)).derivative.eval θ₀) ≠ 0 := by
    rw [derivative_map, hev', hev, hθ₀, ← derivative_map, hPf]
    exact hfsep.aeval_derivative_ne_zero hfα
  have h2 : IsUnit (Ideal.Quotient.mk (maximalIdeal W₀)
      ((P.map (algebraMap A₀ W₀)).derivative.eval θ₀)) := by
    have hu : IsUnit ((P.map (algebraMap A₀ W₀)).derivative.eval θ₀) := by
      by_contra h
      exact h2' ((residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h)))
    exact hu.map _
  obtain ⟨θ, hθroot, hθθ₀⟩ :=
    HenselianRing.is_henselian (I := maximalIdeal W₀) (P.map (algebraMap A₀ W₀)) hPW θ₀ h1 h2
  have hPθ : aeval θ P = 0 := by rw [← hev']; exact hθroot
  have hθα : residue W₀ θ = α := by
    rw [← hθ₀, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hθθ₀

  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible A₀
  have hϖ : maximalIdeal A₀ = Ideal.span {ϖ} := hϖirr.maximalIdeal_eq
  have hϖW : maximalIdeal W₀ = Ideal.span {algebraMap A₀ W₀ ϖ} := by
    rw [hW₀, hϖ, Ideal.map_span, Set.image_singleton]
  have hϖWn : ∀ n : ℕ, maximalIdeal W₀ ^ n = Ideal.span {algebraMap A₀ W₀ ϖ ^ n} := fun n => by
    rw [hϖW, Ideal.span_singleton_pow]
  have hϖn : ∀ n : ℕ, maximalIdeal A₀ ^ n = Ideal.span {ϖ ^ n} := fun n => by
    rw [hϖ, Ideal.span_singleton_pow]
  have hϖW0 : algebraMap A₀ W₀ ϖ ≠ 0 := by
    intro h
    apply IsDiscreteValuationRing.not_a_field W₀
    rw [hϖW, h, Ideal.span_singleton_eq_bot]

  have hbase : ∀ w : W₀, ∃ g : Polynomial A₀, w - aeval θ g ∈ maximalIdeal W₀ := by
    intro w
    have hmem : residue W₀ w ∈ (IntermediateField.adjoin (ResidueField A₀) {α}).toSubalgebra := by
      rw [hα]; trivial
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hαint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at hmem
    obtain ⟨q, hq⟩ := hmem
    obtain ⟨g, rfl⟩ := Polynomial.map_surjective (residue A₀) hres₀surj q
    refine ⟨g, ?_⟩
    rw [← residue_eq_zero_iff, map_sub, hev, hθα, sub_eq_zero]
    exact hq.symm

  have hsurj : ∀ n : ℕ, ∀ w : W₀, ∃ g : Polynomial A₀, w - aeval θ g ∈ maximalIdeal W₀ ^ n := by
    intro n
    induction n with
    | zero => intro w; exact ⟨0, by rw [pow_zero, Ideal.one_eq_top]; trivial⟩
    | succ n ih =>
      intro w
      obtain ⟨g, hg⟩ := ih w
      rw [hϖWn, Ideal.mem_span_singleton'] at hg
      obtain ⟨w', hw'⟩ := hg
      obtain ⟨g₁, hg₁⟩ := hbase w'
      refine ⟨g + C (ϖ ^ n) * g₁, ?_⟩
      have : w - aeval θ (g + C (ϖ ^ n) * g₁) = (w' - aeval θ g₁) * algebraMap A₀ W₀ ϖ ^ n := by
        rw [map_add, map_mul, aeval_C, map_pow, ← sub_sub, ← hw']; ring
      rw [this, hϖWn]
      rw [hϖW] at hg₁
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hg₁
      rw [← hc, Ideal.mem_span_singleton']
      exact ⟨c, by ring⟩

  have hP1 : P ≠ 1 := by
    intro h
    have : f = 1 := by rw [← hPf, h, Polynomial.map_one]
    exact hfirr.not_isUnit (this ▸ isUnit_one)

  have hsmall : ∀ r : Polynomial A₀, r.natDegree < P.natDegree → aeval θ r ∈ maximalIdeal W₀ →
      ∃ r' : Polynomial A₀, r = C ϖ * r' := by
    intro r hr hrθ
    have hrbar : r.map (residue A₀) = 0 := by
      by_contra hne
      have h0 : aeval α (r.map (residue A₀)) = 0 := by
        rw [← hθα, ← hev, residue_eq_zero_iff]; exact hrθ
      have hle := Polynomial.natDegree_le_natDegree (minpoly.degree_le_of_ne_zero (ResidueField A₀) (x := α) hne h0)
      change f.natDegree ≤ (r.map (residue A₀)).natDegree at hle
      have hle' : (r.map (residue A₀)).natDegree ≤ r.natDegree := natDegree_map_le
      have hPdeg : P.natDegree = f.natDegree := by rw [← hPf, hPmonic.natDegree_map]
      omega
    have hdvd : C ϖ ∣ r := by
      rw [C_dvd_iff_dvd_coeff]
      intro i
      have : r.coeff i ∈ maximalIdeal A₀ := by
        rw [← residue_eq_zero_iff, ← Polynomial.coeff_map, hrbar, coeff_zero]
      rwa [hϖ, Ideal.mem_span_singleton] at this
    exact hdvd

  have hker_mpr : ∀ (n : ℕ) (g : Polynomial A₀),
      g ∈ Ideal.span {P} ⊔ (maximalIdeal A₀ ^ n).map (C : A₀ →+* Polynomial A₀) →
      aeval θ g ∈ maximalIdeal W₀ ^ n := by
    intro n g hg
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hg
    rw [map_add]
    refine Ideal.add_mem _ ?_ ?_
    · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hs
      rw [map_mul, hPθ, mul_zero]; exact Ideal.zero_mem _
    · have hdvd : C (ϖ ^ n) ∣ t := by
        rw [C_dvd_iff_dvd_coeff]
        intro i
        have := (Ideal.mem_map_C_iff.mp ht) i
        rwa [hϖn, Ideal.mem_span_singleton] at this
      obtain ⟨t', rfl⟩ := hdvd
      rw [map_mul, aeval_C, map_pow, hϖWn]
      exact Ideal.mem_span_singleton'.mpr ⟨aeval θ t', by ring⟩

  have hker_mp : ∀ (n : ℕ) (g : Polynomial A₀), aeval θ g ∈ maximalIdeal W₀ ^ n →
      g ∈ Ideal.span {P} ⊔ (maximalIdeal A₀ ^ n).map (C : A₀ →+* Polynomial A₀) := by
    intro n
    induction n with
    | zero =>
      intro g _
      rw [pow_zero, Ideal.one_eq_top, Ideal.map_top, sup_top_eq]
      trivial
    | succ n ih =>
      intro g hg
      have hgr : g %ₘ P + P * (g /ₘ P) = g := modByMonic_add_div g P
      have hrdeg : (g %ₘ P).natDegree < P.natDegree := natDegree_modByMonic_lt g hPmonic hP1
      have hrθ : aeval θ (g %ₘ P) ∈ maximalIdeal W₀ ^ (n + 1) := by
        have : aeval θ g = aeval θ (g %ₘ P) := by
          have h := congrArg (aeval θ) hgr
          rw [map_add, map_mul, hPθ, zero_mul, add_zero] at h
          exact h.symm
        rwa [this] at hg
      obtain ⟨r', hr'⟩ := hsmall (g %ₘ P) hrdeg (Ideal.pow_le_self (Nat.succ_ne_zero n) hrθ)
      have hr'θ : aeval θ r' ∈ maximalIdeal W₀ ^ n := by
        rw [hr', map_mul, aeval_C, hϖWn, Ideal.mem_span_singleton'] at hrθ
        obtain ⟨b, hb⟩ := hrθ
        rw [hϖWn, Ideal.mem_span_singleton']
        refine ⟨b, mul_left_cancel₀ hϖW0 ?_⟩
        rw [← hb]; ring
      have hr'mem := ih r' hr'θ
      have hrmem : g %ₘ P ∈ Ideal.span {P} ⊔ (maximalIdeal A₀ ^ (n + 1)).map (C : A₀ →+* Polynomial A₀) := by
        rw [hr']
        obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp hr'mem
        rw [← hst, mul_add]
        refine Submodule.add_mem_sup (Ideal.mul_mem_left _ _ hs) ?_
        rw [Ideal.mem_map_C_iff] at ht
        rw [Ideal.mem_map_C_iff]
        intro i
        rw [coeff_C_mul, pow_succ']
        exact Ideal.mul_mem_mul ((hϖ ▸ Ideal.mem_span_singleton_self ϖ :)) (ht i)
      rw [← hgr]
      exact Ideal.add_mem _ hrmem (Submodule.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self P)))
  refine ⟨P, θ, hPmonic, ?_, ?_, hPθ, hsurj, fun n g => ⟨hker_mp n g, hker_mpr n g⟩⟩
  · rw [hPf]; exact hfirr
  · rw [hPf]; exact hfsep

end S_IsDiscreteValuationRing_exists_monic_aeval_eq_zero_forall_mem_pow_iff_of_maximalIdeal_eq_map_of_isSeparable
end P2MW
export P2MW.S_IsDiscreteValuationRing_exists_monic_aeval_eq_zero_forall_mem_pow_iff_of_maximalIdeal_eq_map_of_isSeparable (solution)
