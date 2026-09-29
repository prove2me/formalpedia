-- Prove2me | solution 1 for M4aHerbrand.Bridge.valued_finiteConorm_apply_and_finprod_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/e62c6a40-9d49-5748-a0c1-5dc76cda0648

import Mathlib
import Definitions.Def_M4aHerbrand_FiniteConorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_Bridge_valued_finiteConorm_apply_and_finprod_pow_eq

set_option autoImplicit false
set_option maxSynthPendingDepth 3
open IsDedekindDomain
open scoped nonZeroDivisors

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

namespace P2mS25F0c

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped nonZeroDivisors

noncomputable section

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B]

section exponent
variable (R : Type*) [CommRing R] [IsDedekindDomain R] (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]

def expAt (x : (FiniteAdeleRing R F)ˣ) (v : HeightOneSpectrum R) : ℤ := -log (Valued.v ((x : FiniteAdeleRing R F) v))

lemma expAt_def (x : (FiniteAdeleRing R F)ˣ) (v : HeightOneSpectrum R) :
    expAt R F x v = -log (Valued.v ((x : FiniteAdeleRing R F) v)) := rfl

lemma valued_ne_zero (x : (FiniteAdeleRing R F)ˣ) (v : HeightOneSpectrum R) : Valued.v ((x : FiniteAdeleRing R F) v) ≠ 0 := by
  have h : IsUnit ((x : FiniteAdeleRing R F) v) := (Units.map (RestrictedProduct.evalRingHom _ v).toMonoidHom x).isUnit
  exact (Valuation.ne_zero_iff _).2 h.ne_zero

lemma expAt_eq_zero_of_integral {x : (FiniteAdeleRing R F)ˣ} {v : HeightOneSpectrum R}
    (h1 : (x : FiniteAdeleRing R F) v ∈ v.adicCompletionIntegers F)
    (h2 : ((x⁻¹ : (FiniteAdeleRing R F)ˣ) : FiniteAdeleRing R F) v ∈ v.adicCompletionIntegers F) :
    expAt R F x v = 0 := by
  rw [mem_adicCompletionIntegers] at h1 h2
  have hmul : Valued.v ((x : FiniteAdeleRing R F) v) * Valued.v (((x⁻¹ : (FiniteAdeleRing R F)ˣ) : FiniteAdeleRing R F) v) = 1 := by
    rw [← map_mul, ← show ((x * x⁻¹ : (FiniteAdeleRing R F)ˣ) : FiniteAdeleRing R F) v =
      (x : FiniteAdeleRing R F) v * ((x⁻¹ : (FiniteAdeleRing R F)ˣ) : FiniteAdeleRing R F) v from rfl, mul_inv_cancel,
      Units.val_one]
    exact map_one _
  have h1' : Valued.v ((x : FiniteAdeleRing R F) v) = 1 := by
    apply le_antisymm h1
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v ((x : FiniteAdeleRing R F) v) *
          Valued.v (((x⁻¹ : (FiniteAdeleRing R F)ˣ) : FiniteAdeleRing R F) v) := hmul.symm
      _ ≤ Valued.v ((x : FiniteAdeleRing R F) v) * 1 := mul_le_mul_right h2 _
      _ = _ := mul_one _
  rw [expAt_def, h1', log_one, neg_zero]

theorem finite_support_expAt (x : (FiniteAdeleRing R F)ˣ) : (Function.support (expAt R F x)).Finite := by
  have hx := (x : FiniteAdeleRing R F).2
  have hx' := ((x⁻¹ : (FiniteAdeleRing R F)ˣ) : FiniteAdeleRing R F).2
  rw [Filter.eventually_cofinite] at hx hx'
  refine (hx.union hx').subset fun v hv => ?_
  by_contra h
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
  exact hv (expAt_eq_zero_of_integral R F h.1 h.2)

theorem eventually_expAt_eq_zero (x : (FiniteAdeleRing R F)ˣ) : ∀ᶠ v in Filter.cofinite, expAt R F x v = 0 := by
  rw [Filter.eventually_cofinite]
  exact finite_support_expAt R F x

end exponent

abbrev conormUnit (x : (FiniteAdeleRing A K)ˣ) : (FiniteAdeleRing B L)ˣ :=
  Units.map (M4aHerbrand.Bridge.finiteConorm A K L B).toMonoidHom x

abbrev e (w : HeightOneSpectrum B) : ℕ := (w.under A).asIdeal.ramificationIdx' w.asIdeal

theorem valued_conormUnit (x : (FiniteAdeleRing A K)ˣ) (w : HeightOneSpectrum B) :
    Valued.v ((conormUnit A K L B x : FiniteAdeleRing B L) w) = Valued.v ((x : FiniteAdeleRing A K) (w.under A)) ^ e A B w := by
  rw [Units.coe_map]
  change Valued.v (M4aHerbrand.Bridge.finiteConorm A K L B (x : FiniteAdeleRing A K) w) = _
  rw [M4aHerbrand.Bridge.finiteConorm_apply]
  exact HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom K L (⟨w, rfl⟩ : (w.under A).Extension B) ((x : FiniteAdeleRing A K) (w.under A))

theorem expAt_conormUnit (x : (FiniteAdeleRing A K)ˣ) (w : HeightOneSpectrum B) :
    expAt B L (conormUnit A K L B x) w = (e A B w : ℤ) * expAt A K x (w.under A) := by
  rw [expAt_def, valued_conormUnit, log_pow, expAt_def, nsmul_eq_mul, mul_neg]

section counts
variable (R : Type*) [CommRing R] [IsDedekindDomain R] (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]

def content (x : (FiniteAdeleRing R F)ˣ) : FractionalIdeal R⁰ F :=
  ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ F) ^ expAt R F x v

lemma content_def (x : (FiniteAdeleRing R F)ˣ) :
    content R F x = ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ F) ^ (-log (Valued.v ((x : FiniteAdeleRing R F) v))) := rfl

omit [IsDedekindDomain R] in
lemma coeIdeal_asIdeal_ne_zero (v : HeightOneSpectrum R) : (v.asIdeal : FractionalIdeal R⁰ F) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot

lemma mulSupport_zpow_subset (ex : HeightOneSpectrum R → ℤ) :
    Function.mulSupport (fun v : HeightOneSpectrum R => (v.asIdeal : FractionalIdeal R⁰ F) ^ ex v) ⊆ Function.support ex := by
  intro v hv
  simp only [Function.mem_mulSupport, Function.mem_support, ne_eq] at hv ⊢
  intro h0
  exact hv (by rw [h0, zpow_zero])

lemma content_ne_zero (x : (FiniteAdeleRing R F)ˣ) : content R F x ≠ 0 := by
  rw [content, finprod_eq_prod_of_mulSupport_subset _ (s := (finite_support_expAt R F x).toFinset)
    (by simpa using mulSupport_zpow_subset R F _)]
  exact Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (coeIdeal_asIdeal_ne_zero R F v)

theorem count_content (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R F)ˣ) :
    FractionalIdeal.count F v (content R F x) = expAt R F x v :=
  FractionalIdeal.count_finprod F v _ (eventually_expAt_eq_zero R F x)

theorem eq_of_count_eq {I J : FractionalIdeal R⁰ F} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count F v I = FractionalIdeal.count F v J) : I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' F hI, ← FractionalIdeal.finprod_heightOneSpectrum_factorization' F hJ]
  exact finprod_congr fun v => by rw [h v]

end counts

include K L in
omit [IsDedekindDomain A] [Algebra.IsIntegral A B] [IsDedekindDomain B] [IsFractionRing B L] in
theorem faithfulSMul_AB : FaithfulSMul A B :=
  (faithfulSMul_iff_algebraMap_injective A B).2 (algebraMap_injective_of_field_isFractionRing A B K L)

include K in

theorem count_coe_map (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) :
    FractionalIdeal.count L w ((v.asIdeal.map (algebraMap A B) : Ideal B) : FractionalIdeal B⁰ L) =
      (v.asIdeal.ramificationIdx' w.asIdeal : ℤ) * (if w.asIdeal.under A = v.asIdeal then 1 else 0) := by
  classical
  haveI : FaithfulSMul A B := faithfulSMul_AB A K L B
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have hne : ∀ P ∈ (v.asIdeal.primesOver B).toFinset, P ≠ ⊥ := fun P hP =>
    Ideal.ne_bot_of_mem_primesOver v.ne_bot (Set.mem_toFinset.1 hP)
  have hcoe : ((v.asIdeal.map (algebraMap A B) : Ideal B) : FractionalIdeal B⁰ L) =
      ∏ P ∈ (v.asIdeal.primesOver B).toFinset, (P : FractionalIdeal B⁰ L) ^ v.asIdeal.ramificationIdx' P := by
    rw [Ideal.map_algebraMap_eq_finsetProd_pow (R := B) (p := v.asIdeal) v.ne_bot]
    exact (map_prod (FractionalIdeal.coeIdealHom B⁰ L) _ _).trans (Finset.prod_congr rfl fun P hP => by
      haveI := (Set.mem_toFinset.1 hP).1
      haveI := (Set.mem_toFinset.1 hP).2
      rw [map_pow, ← Ideal.ramificationIdx'_eq_ramificationIdx (p := v.asIdeal) (q := P) v.ne_bot]
      rfl)
  rw [hcoe, FractionalIdeal.count_prod]
  ·
    have hterm : ∀ P ∈ (v.asIdeal.primesOver B).toFinset,
        FractionalIdeal.count L w ((P : FractionalIdeal B⁰ L) ^ v.asIdeal.ramificationIdx' P) =
          (v.asIdeal.ramificationIdx' P : ℤ) * (if P = w.asIdeal then 1 else 0) := by
      intro P hP
      have hP' := Set.mem_toFinset.1 hP
      let wP : HeightOneSpectrum B := ⟨P, hP'.1, hne P hP⟩
      rw [FractionalIdeal.count_pow, show (P : FractionalIdeal B⁰ L) = (wP.asIdeal : FractionalIdeal B⁰ L) from rfl]
      by_cases h : P = w.asIdeal
      · have : wP = w := HeightOneSpectrum.ext h
        rw [this, FractionalIdeal.count_self, if_pos h]
      · have : wP ≠ w := fun h' => h (congrArg HeightOneSpectrum.asIdeal h')
        rw [FractionalIdeal.count_maximal_coprime L w this, if_neg h]
    rw [Finset.sum_congr rfl hterm]
    by_cases hw : w.asIdeal.under A = v.asIdeal
    · have hmem : w.asIdeal ∈ (v.asIdeal.primesOver B).toFinset :=
        Set.mem_toFinset.2 ⟨w.isPrime, ⟨hw.symm⟩⟩
      rw [Finset.sum_eq_single_of_mem w.asIdeal hmem (fun P _ hPw => by rw [if_neg hPw, mul_zero]), if_pos rfl, if_pos hw]
    · rw [if_neg hw, mul_zero]
      refine Finset.sum_eq_zero fun P hP => ?_
      have hP' := Set.mem_toFinset.1 hP
      have : P ≠ w.asIdeal := fun h => hw (by rw [← h]; exact hP'.2.over.symm)
      rw [if_neg this, mul_zero]
  · intro P hP
    exact pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr (hne P hP))

include K in
theorem coe_map_ne_zero (v : HeightOneSpectrum A) : ((v.asIdeal.map (algebraMap A B) : Ideal B) : FractionalIdeal B⁰ L) ≠ 0 := by
  haveI : FaithfulSMul A B := faithfulSMul_AB A K L B
  exact FractionalIdeal.coeIdeal_ne_zero.mpr (Ideal.map_ne_bot_of_ne_bot v.ne_bot)

omit [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L] [Algebra.IsIntegral A B] in

theorem rhs_eq_prod (x : (FiniteAdeleRing A K)ˣ) :
    ∏ᶠ v : HeightOneSpectrum A, ((v.asIdeal.map (algebraMap A B) : Ideal B) : FractionalIdeal B⁰ L) ^ expAt A K x v =
      ∏ v ∈ (finite_support_expAt A K x).toFinset, ((v.asIdeal.map (algebraMap A B) : Ideal B) : FractionalIdeal B⁰ L) ^ expAt A K x v := by
  apply finprod_eq_prod_of_mulSupport_subset
  intro v hv
  simp only [Function.mem_mulSupport, ne_eq, Set.Finite.coe_toFinset, Function.mem_support] at hv ⊢
  intro h0
  exact hv (by rw [h0, zpow_zero])

theorem content_conormUnit (x : (FiniteAdeleRing A K)ˣ) :
    content B L (conormUnit A K L B x) =
      ∏ᶠ v : HeightOneSpectrum A, ((v.asIdeal.map (algebraMap A B) : Ideal B) : FractionalIdeal B⁰ L) ^ expAt A K x v := by
  classical
  rw [rhs_eq_prod]
  apply eq_of_count_eq B L (content_ne_zero B L _)
    (Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (coe_map_ne_zero A K L B v))
  intro w
  rw [count_content, expAt_conormUnit, FractionalIdeal.count_prod L w _ _
    (fun v _ => zpow_ne_zero _ (coe_map_ne_zero A K L B v))]
  simp_rw [FractionalIdeal.count_zpow, count_coe_map A K L B]

  have key : ∀ v : HeightOneSpectrum A, (w.asIdeal.under A = v.asIdeal) ↔ w.under A = v := fun v =>
    ⟨fun h => HeightOneSpectrum.ext h, fun h => by rw [← h]; rfl⟩
  by_cases hmem : w.under A ∈ (finite_support_expAt A K x).toFinset
  · rw [Finset.sum_eq_single_of_mem (w.under A) hmem]
    · rw [if_pos (show w.asIdeal.under A = (w.under A).asIdeal from rfl), mul_one, mul_comm]
    · intro v _ hv
      rw [if_neg (fun h => hv ((key v).1 h).symm), mul_zero, mul_zero]
  · have h0 : expAt A K x (w.under A) = 0 := by
      simpa [Set.Finite.mem_toFinset, Function.mem_support] using hmem
    rw [h0, mul_zero]
    refine (Finset.sum_eq_zero fun v hv => ?_).symm
    by_cases hvw : w.asIdeal.under A = v.asIdeal
    · exact absurd (((key v).1 hvw) ▸ hv) hmem
    · rw [if_neg hvw, mul_zero, mul_zero]

end
end P2mS25F0c

open IsDedekindDomain in
open scoped nonZeroDivisors in
theorem solution
    (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B]
    (x : (FiniteAdeleRing A K)ˣ) :
    (∀ w : HeightOneSpectrum B,
      Valued.v (((Units.map (M4aHerbrand.Bridge.finiteConorm A K L B).toMonoidHom x : (FiniteAdeleRing B L)ˣ) :
        FiniteAdeleRing B L) w) =
        Valued.v ((x : FiniteAdeleRing A K) (w.under A)) ^ (w.under A).asIdeal.ramificationIdx' w.asIdeal) ∧
    ∏ᶠ w : HeightOneSpectrum B, (w.asIdeal : FractionalIdeal B⁰ L) ^
        (-(WithZero.log (Valued.v (((Units.map (M4aHerbrand.Bridge.finiteConorm A K L B).toMonoidHom x :
          (FiniteAdeleRing B L)ˣ) : FiniteAdeleRing B L) w)))) =
      ∏ᶠ v : HeightOneSpectrum A, ((v.asIdeal.map (algebraMap A B) : Ideal B) : FractionalIdeal B⁰ L) ^
        (-(WithZero.log (Valued.v ((x : FiniteAdeleRing A K) v)))) :=
  ⟨P2mS25F0c.valued_conormUnit A K L B x, P2mS25F0c.content_conormUnit A K L B x⟩

end S_M4aHerbrand_Bridge_valued_finiteConorm_apply_and_finprod_pow_eq
end P2MW
export P2MW.S_M4aHerbrand_Bridge_valued_finiteConorm_apply_and_finprod_pow_eq (solution)
