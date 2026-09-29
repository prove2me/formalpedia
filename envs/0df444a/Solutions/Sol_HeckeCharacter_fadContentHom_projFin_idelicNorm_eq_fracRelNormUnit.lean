-- Prove2me | solution 1 for HeckeCharacter.fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/2e5ab203-c4be-566a-af54-4410ccfafc42

import Theorems.Thm_M4aHerbrand_valuation_adelicNorm_eq_finprod_pow_inertiaDeg
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCharacter_fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter
open scoped nonZeroDivisors
open scoped WithZero

private theorem projFin_val' {A : Type*} [Field A] [NumberField A] (u : (AdeleRing (𝓞 A) A)ˣ) :
    ((projFin A u : (FiniteAdeleRing (𝓞 A) A)ˣ) : FiniteAdeleRing (𝓞 A) A) =
      (u : AdeleRing (𝓞 A) A).2 := rfl

private theorem coe_fadContentHom' {A : Type*} [Field A] [NumberField A]
    (u : (FiniteAdeleRing (𝓞 A) A)ˣ) :
    ((fadContentHom A u : (FractionalIdeal (𝓞 A)⁰ A)ˣ) : FractionalIdeal (𝓞 A)⁰ A)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 A),
          (v.asIdeal : FractionalIdeal (𝓞 A)⁰ A) ^ (placeOrd A u v) := by
  rw [show fadContentHom A u = ∏ᶠ v : HeightOneSpectrum (𝓞 A), (primeUnit A v) ^ (placeOrd A u v)
        from rfl,
    ← Units.coeHom_apply,
    (Units.coeHom _).map_finprod_of_preimage_one (fun _ h => Units.ext h)
      (fun v => primeUnit A v ^ placeOrd A u v)]
  refine finprod_congr fun v => ?_
  rw [Units.coeHom_apply, Units.val_zpow_eq_zpow_val, primeUnit_val]

private theorem count_fadContentHom' {A : Type*} [Field A] [NumberField A]
    (u : (FiniteAdeleRing (𝓞 A) A)ˣ) (w : HeightOneSpectrum (𝓞 A)) :
    FractionalIdeal.count A w ((fadContentHom A u : (FractionalIdeal (𝓞 A)⁰ A)ˣ) :
      FractionalIdeal (𝓞 A)⁰ A) = placeOrd A u w := by
  rw [coe_fadContentHom']
  exact FractionalIdeal.count_finprod A w (placeOrd A u) (by
    rw [Filter.eventually_cofinite]
    exact finite_support_placeOrd A u)

private theorem count_ext {A : Type*} [Field A] [NumberField A]
    {I J : FractionalIdeal (𝓞 A)⁰ A} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ u : IsDedekindDomain.HeightOneSpectrum (𝓞 A),
      FractionalIdeal.count A u I = FractionalIdeal.count A u J) : I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := A) hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := A) hJ]
  exact finprod_congr fun u => by rw [h u]

private theorem log_finprod_pow {ι : Type*} (V : ι → ℤᵐ⁰) (n : ι → ℕ)
    (hV : ∀ i, V i ≠ 0) (hfin : (Function.mulSupport V).Finite) :
    WithZero.log (∏ᶠ i, V i ^ n i) = ∑ᶠ i, (n i : ℤ) * WithZero.log (V i) := by
  classical
  have hsub : (Function.mulSupport fun i => V i ^ n i) ⊆ ↑hfin.toFinset := by
    intro i hi
    rw [Set.Finite.coe_toFinset]
    by_contra h1
    rw [Function.mem_mulSupport] at hi h1
    rw [not_not] at h1
    exact hi (by rw [h1, one_pow])
  have hsub' : (Function.support fun i => (n i : ℤ) * WithZero.log (V i)) ⊆ ↑hfin.toFinset := by
    intro i hi
    rw [Set.Finite.coe_toFinset]
    by_contra h1
    rw [Function.mem_support] at hi
    rw [Function.mem_mulSupport, not_not] at h1
    exact hi (by rw [h1, WithZero.log_one, mul_zero])
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, finsum_eq_sum_of_support_subset _ hsub']
  induction hfin.toFinset using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      WithZero.log_mul (pow_ne_zero _ (hV a))
        (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hV i)),
      WithZero.log_pow, ih]
    ring

private theorem placeOrd_idelicNorm_eq_finsum {A B : Type*} [Field A] [NumberField A] [Field B]
    [NumberField B] [Algebra A B] (v : (AdeleRing (𝓞 B) B)ˣ)
    (u : IsDedekindDomain.HeightOneSpectrum (𝓞 A)) :
    placeOrd A (projFin A ((M4aHerbrand.GenuineDescent.genuineBaseChange A B).idelicNorm v)) u =
      ∑ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 B),
        (Ideal.inertiaDeg' u.asIdeal w.asIdeal : ℤ) * placeOrd B (projFin B v) w := by
  have hserved := M4aHerbrand.valuation_adelicNorm_eq_finprod_pow_inertiaDeg A B
    (M4aHerbrand.GenuineDescent.genuineBaseChange A B) (↑v) u
  have hV : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 B),
      Valued.v (((v : AdeleRing (𝓞 B) B).2 : FiniteAdeleRing (𝓞 B) B) w) ≠ 0 := fun w => by
    have h := valued_ne_zero_of_unit B (projFin B v) w
    rwa [projFin_val'] at h
  have hfin : (Function.mulSupport fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 B) =>
      Valued.v (((v : AdeleRing (𝓞 B) B).2 : FiniteAdeleRing (𝓞 B) B) w)).Finite := by
    refine (finite_support_placeOrd B (projFin B v)).subset ?_
    intro w hw
    rw [Function.mem_mulSupport] at hw
    rw [Function.mem_support, placeOrd]
    simp only [ne_eq, neg_eq_zero]
    intro hlog
    apply hw
    have hVw : Valued.v (((v : AdeleRing (𝓞 B) B).2 : FiniteAdeleRing (𝓞 B) B) w) ≠ 0 :=
      valued_ne_zero_of_unit B (projFin B v) w
    have hlog' : (Valued.v (((v : AdeleRing (𝓞 B) B).2 : FiniteAdeleRing (𝓞 B) B) w)).log = 0 :=
      hlog
    rw [← WithZero.exp_log hVw, hlog', WithZero.exp_zero]
  show -WithZero.log (Valued.v (((projFin A
      ((M4aHerbrand.GenuineDescent.genuineBaseChange A B).idelicNorm v) :
      (FiniteAdeleRing (𝓞 A) A)ˣ) : FiniteAdeleRing (𝓞 A) A) u)) = _
  rw [projFin_val']
  have hcoe : (((M4aHerbrand.GenuineDescent.genuineBaseChange A B).idelicNorm v :
      (AdeleRing (𝓞 A) A)ˣ) : AdeleRing (𝓞 A) A) =
      (M4aHerbrand.GenuineDescent.genuineBaseChange A B).adelicNorm ↑v := rfl
  rw [hcoe, hserved, log_finprod_pow _ _ hV hfin]
  rw [← finsum_neg_distrib]
  refine finsum_congr fun w => ?_
  show -((Ideal.inertiaDeg' u.asIdeal w.asIdeal : ℤ) * WithZero.log _) = _
  rw [placeOrd, projFin_val', mul_neg]

private theorem count_units_finprod {A : Type*} [Field A] [NumberField A] {ι : Type*}
    (g : ι → (FractionalIdeal (𝓞 A)⁰ A)ˣ) (hfin : (Function.mulSupport g).Finite)
    (u : IsDedekindDomain.HeightOneSpectrum (𝓞 A)) :
    FractionalIdeal.count A u ((∏ᶠ i, g i : (FractionalIdeal (𝓞 A)⁰ A)ˣ) :
      FractionalIdeal (𝓞 A)⁰ A) =
      ∑ᶠ i, FractionalIdeal.count A u ((g i : (FractionalIdeal (𝓞 A)⁰ A)ˣ) :
        FractionalIdeal (𝓞 A)⁰ A) := by
  classical
  have h1 : ((∏ᶠ i, g i : (FractionalIdeal (𝓞 A)⁰ A)ˣ) : FractionalIdeal (𝓞 A)⁰ A) =
      ∏ᶠ i, ((g i : (FractionalIdeal (𝓞 A)⁰ A)ˣ) : FractionalIdeal (𝓞 A)⁰ A) :=
    MonoidHom.map_finprod_of_preimage_one (Units.coeHom _) (fun x h => Units.ext h) g
  rw [h1]
  have hsubc : (Function.mulSupport fun i => ((g i : (FractionalIdeal (𝓞 A)⁰ A)ˣ) :
      FractionalIdeal (𝓞 A)⁰ A)) ⊆ ↑hfin.toFinset := by
    intro i hi
    rw [Set.Finite.coe_toFinset]
    by_contra h1
    rw [Function.mem_mulSupport] at hi
    rw [Function.mem_mulSupport, not_not] at h1
    exact hi (by rw [h1, Units.val_one])
  have hsubs : (Function.support fun i => FractionalIdeal.count A u
      ((g i : (FractionalIdeal (𝓞 A)⁰ A)ˣ) : FractionalIdeal (𝓞 A)⁰ A)) ⊆ ↑hfin.toFinset := by
    intro i hi
    rw [Set.Finite.coe_toFinset]
    by_contra h1
    rw [Function.mem_support] at hi
    rw [Function.mem_mulSupport, not_not] at h1
    exact hi (by rw [h1, Units.val_one, FractionalIdeal.count_one])
  rw [finprod_eq_prod_of_mulSupport_subset _ hsubc, finsum_eq_sum_of_support_subset _ hsubs]
  exact FractionalIdeal.count_prod A u _ _ fun i _ => Units.ne_zero _

private theorem count_fracRelNormUnit_content {A B : Type*} [Field A] [NumberField A] [Field B]
    [NumberField B] [Algebra A B] (v : (AdeleRing (𝓞 B) B)ˣ)
    (u : IsDedekindDomain.HeightOneSpectrum (𝓞 A)) :
    FractionalIdeal.count A u
        ((fracRelNormUnit A B (fadContentHom B (projFin B v)) :
          (FractionalIdeal (𝓞 A)⁰ A)ˣ) : FractionalIdeal (𝓞 A)⁰ A) =
      ∑ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 B),
        (Ideal.inertiaDeg' u.asIdeal w.asIdeal : ℤ) * placeOrd B (projFin B v) w := by
  classical
  have hray : fracRelNormUnit A B (fadContentHom B (projFin B v)) =
      ∏ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 B),
        (primeUnit A (placeUnder' A B w) ^
          ((placeUnder' A B w).asIdeal.inertiaDeg' w.asIdeal)) ^
          FractionalIdeal.count B w ((fadContentHom B (projFin B v) :
            (FractionalIdeal (𝓞 B)⁰ B)ˣ) : FractionalIdeal (𝓞 B)⁰ B) := rfl
  rw [hray, count_units_finprod _ (hasFiniteMulSupport_raySymbol_factors B _ _) u]
  refine finsum_congr fun w => ?_
  rw [count_fadContentHom']
  by_cases hwu : placeUnder' A B w = u
  · have he : (placeUnder' A B w).asIdeal.inertiaDeg' w.asIdeal =
        u.asIdeal.inertiaDeg' w.asIdeal := by rw [hwu]
    rw [Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, primeUnit_val,
      FractionalIdeal.count_zpow, FractionalIdeal.count_pow, ← hwu,
      FractionalIdeal.count_self, mul_one, he, mul_comm]
  · have hz : Ideal.inertiaDeg' u.asIdeal w.asIdeal = 0 := by
      have hne : w.asIdeal.under (𝓞 A) ≠ u.asIdeal := fun h =>
        hwu (IsDedekindDomain.HeightOneSpectrum.ext (by rw [placeUnder'_asIdeal, h]))
      unfold Ideal.inertiaDeg'
      exact dif_neg (by rwa [Ideal.under_def] at hne)
    rw [hz, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, primeUnit_val,
      FractionalIdeal.count_zpow, FractionalIdeal.count_pow,
      FractionalIdeal.count_maximal, if_neg (fun h =>
        hwu (IsDedekindDomain.HeightOneSpectrum.ext (by
          have h2 := congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h
          rwa [placeUnder'_asIdeal] at h2))),
      mul_zero, mul_zero, Nat.cast_zero, zero_mul]

theorem solution (A B : Type*)
    [Field A] [NumberField A] [Field B] [NumberField B] [Algebra A B]
    (v : (AdeleRing (𝓞 B) B)ˣ) :
    HeckeCharacter.fadContentHom A (HeckeCharacter.projFin A
        ((M4aHerbrand.GenuineDescent.genuineBaseChange A B).idelicNorm v)) =
      HeckeCharacter.fracRelNormUnit A B
        (HeckeCharacter.fadContentHom B (HeckeCharacter.projFin B v)) := by
  refine Units.ext (count_ext (Units.ne_zero _) (Units.ne_zero _) fun u => ?_)
  rw [count_fadContentHom', count_fracRelNormUnit_content,
    placeOrd_idelicNorm_eq_finsum]

end

end S_HeckeCharacter_fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit
end P2MW
export P2MW.S_HeckeCharacter_fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit (solution)
