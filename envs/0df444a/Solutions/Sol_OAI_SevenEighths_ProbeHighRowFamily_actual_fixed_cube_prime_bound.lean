-- Prove2me | solution 1 for OAI.SevenEighths.ProbeHighRowFamily.actual_fixed_cube_prime_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T05:35:14.784983+00:00
-- url     : https://prove2.me/submissions/db97c107-ca78-4522-8f12-2d1dd74a2a35

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027
import Theorems.Thm_OAI_SevenEighths_HeckePrimeAmplitudeActual_ray_amplitude_bins
import Theorems.Thm_OAI_SevenEighths_ProbeCentralPrimeSum_actual_central_prime_sum

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ConductorBounds
namespace OAI

namespace SevenEighths.FiniteConductor

open SevenEighths.FiniteFourier
open scoped Classical

noncomputable section

section QuotientBounds

variable {R : Type*} [CommRing R]

theorem quotient_inf_card_le_mul (I J : Ideal R) [Finite (R ⧸ I)] [Finite (R ⧸ J)] :
    Nat.card (R ⧸ I ⊓ J) ≤ Nat.card (R ⧸ I) * Nat.card (R ⧸ J) := by
  let f : R ⧸ I ⊓ J →+* (R ⧸ I) × (R ⧸ J) :=
    (Ideal.Quotient.factor inf_le_left).prod (Ideal.Quotient.factor inf_le_right)
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact ⟨Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.fst hx),
      Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.snd hx)⟩
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hf

end QuotientBounds

variable {A : Type*} [CommRing A] [IsDedekindDomain A] [Infinite A]
  [Module.Free ℤ A] [Module.Finite ℤ A]

theorem absNorm_inf_le_mul (I J : Ideal A) [Finite (A ⧸ I)] [Finite (A ⧸ J)] :
    (I ⊓ J).absNorm ≤ I.absNorm * J.absNorm := by
  simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply] using
    quotient_inf_card_le_mul I J

end

end SevenEighths.FiniteConductor

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Calibration
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem calibrationForSet_span (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    Ideal.span {(calibrationForSet S hS).generator} = ∏ P ∈ S, P := by
  change Ideal.span {finitePrimeModulus (fun P : S => P.val)} = _
  rw [span_finitePrimeModulus]
  exact Finset.prod_coe_sort S (fun P : Ideal O => P)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CalibrationSupport
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O

theorem calibrationForSet_coprime_iff (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal)
    (a : O) : IsCoprime (calibrationForSet S hS).generator a ↔ ∀ P ∈ S, a ∉ P := by
  rw [← Ideal.isCoprime_span_singleton_iff, calibrationForSet_span, IsCoprime.prod_left_iff]
  constructor
  · intro h P hP
    let : P.IsMaximal := hS P hP
    exact (SixthPowerAverage.prime_coprime_span_iff P a).mp (h P hP)
  · intro h P hP
    let : P.IsMaximal := hS P hP
    exact (SixthPowerAverage.prime_coprime_span_iff P a).mpr (h P hP)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.PrimePower
namespace OAI

open scoped BigOperators Classical
open NumberField
namespace SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

local instance instInfiniteRingOfIntegers_solutions_r2384f5_1 : Infinite (𝓞 K) := Module.Free.infinite ℤ (𝓞 K)
omit [NumberField K] in
theorem primePowerReduction_surjective (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c) :
    Function.Surjective (primePowerReduction P hc) :=
  Ideal.Quotient.factor_surjective _

end
end SevenEighths.CenteredMomentCorrelation

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Canonical
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentCanonical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCorrelation

theorem actualSextic_order_six (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    orderOf (actualSextic P hg) = 6 := by
  let Φ : MulChar (O ⧸ P) O →* MulChar (O ⧸ P) ℂ :=
    MulChar.ringHomCompHom eisEmbedding
  have hΦ : Function.Injective Φ := by
    intro x y h
    apply MulChar.ext
    intro t
    apply eisEmbedding_injective
    exact congrArg (fun f : MulChar (O ⧸ P) ℂ => f t) h
  exact (orderOf_injective Φ hΦ _).trans (sexticChar_order P hg hchar)

theorem canonicalPrimePowerCharacter_mk (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) {c : ℕ} (hc : 1 ≤ c) (x : O) :
    canonicalPrimePowerCharacter P hg hc (Ideal.Quotient.mk (P ^ c) x) =
      CanonicalRowCompletion.idealRowHom x (P ^ c) := by
  change (actualSextic P hg ^ c) (Ideal.Quotient.mk P x) = _
  rw [MulChar.pow_apply' _ (by omega), map_pow,
    CanonicalRowCompletion.idealRowHom_prime x P hg]

end SevenEighths.CenteredMomentCanonical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsCentralLower
namespace OAI

noncomputable section
open scoped Topology
open Filter
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

theorem central_correction_threshold (eps : ℝ) (heps : 0<eps) :
    ∃Q0 : ℝ,480≤Q0 ∧ ∀Q : ℝ,Q0≤Q→198*Q^(-10*eps)≤1/2 := by
  have hh : Tendsto (fun Q : ℝ=>198*Q^(-10*eps)) atTop (nhds 0) := by
    simpa only [mul_zero,neg_mul] using
      (tendsto_rpow_neg_atTop (show 0<10*eps by positivity)).const_mul (198:ℝ)
  have he := hh.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))
  obtain ⟨Q0,hQ0⟩ := Filter.eventually_atTop.mp he
  refine ⟨max 480 Q0,le_max_left _ _,?_⟩
  intro Q hQ
  exact (hQ0 Q ((le_max_right _ _).trans hQ)).le

variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Operations
namespace OAI

noncomputable section
namespace SevenEighths.HeckeFamily

theorem elementCoeff_inverse (χ : Character) (z : O) :
    elementCoeff χ.inverse z = (elementCoeff χ z)⁻¹ := by
  exact MulChar.inv_apply_eq_inv' _ _

end SevenEighths.HeckeFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeCounting.AnnularPrimeMass
namespace OAI

namespace SevenEighths.PNT.AnnularPrimeMass

open ActualEisensteinCubic ArithmeticFunction Filter MeasureTheory
open SevenEighths.IdealMangoldt SevenEighths.PNT.IdealPrimeMass
open scoped BigOperators Classical Topology ContDiff

noncomputable section

theorem norm_bounds_of_mem_annularPrimeIdeals {C : Set (Ideal O)} {a b x : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hx : 0 < x) {P : Ideal O}
    (hP : P ∈ annularPrimeIdeals C a b x) :
    x * a < (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ x * b := by
  have h := (mem_annularPrimeIdeals C a b x P).mp hP
  exact ⟨(Nat.floor_lt (mul_nonneg hx.le ha)).mp h.2.2.1,
    (Nat.le_floor_iff (mul_nonneg hx.le (ha.trans hab))).mp h.2.2.2⟩

end

end SevenEighths.PNT.AnnularPrimeMass

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RaySlots
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical PNT.AnnularPrimeMass
open PrincipalSignalComparison ProbePrincipalResidueActual
local notation "Id" => Ideal HeckeFamily.O

theorem pool_norm_bounds (C : Set Id) (S : Finset Id) {a b x : ℝ}
    (ha : 0≤a) (hab : a≤b) (hx : 0<x) (P : PrimeIdeal) (hP : P∈pool C S a b x) :
    x*a<(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤x*b :=
  norm_bounds_of_mem_annularPrimeIdeals ha hab hx
    (Finset.mem_sdiff.mp (Finset.mem_subtype.mp hP)).1

variable (M : Id) [NeZero M]
variable (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

include hH

end SevenEighths.ProbeRaySlots
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DyadicTailBudget
namespace OAI

noncomputable section
namespace SevenEighths.HeckeDyadic

theorem constant_absorbed_eventually (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ Z : ℝ in Filter.atTop, C≤Z^ε := by
  exact (tendsto_rpow_atTop hε).eventually (Filter.eventually_ge_atTop C)

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RayPhaseAmplitude
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical PNT.AnnularPrimeMass
local notation "Id" => Ideal HeckeFamily.O

lemma pool_sum_complex (C : Set Id) (S : Finset Id) (a b x : ℝ) (f : Id→ℂ) :
    (∑P∈pool C S a b x,f P.val)=∑P∈annularPrimeIdeals C a b x\S,f P := by
  apply Finset.sum_bij (fun P _=>P.val)
  · intro P hP;exact Finset.mem_subtype.mp hP
  · intro P hP Q hQ he;exact Subtype.ext he
  · intro P hP
    have hp : Prime P := ((mem_annularPrimeIdeals C a b x P).mp (Finset.mem_sdiff.mp hP).1).2.1
    exact ⟨⟨P,hp⟩,Finset.mem_subtype.mpr hP,rfl⟩
  · intro P hP;rfl

theorem weighted_pool_eq_annular (C : Set Id) (S : Finset Id)
    (W : ℝ→ℂ) (a b D : ℝ) (ha : 0<a) (_hab : a≤b) (hD : 0<D)
    (hW : Function.support W⊆Set.Ioo a b)
    (hS : ∀P∈S,(P.absNorm:ℝ)≤a*D) (g : Id→ℂ) :
    (∑P∈pool C S a b D,W ((P.val.absNorm:ℝ)/D)*g P.val)=
      ∑P∈(HeckePrimeAnnular.annulusSet b D).filter (fun P=>Prime P ∧ P∈C),
        W ((P.absNorm:ℝ)/D)*g P := by
  rw [pool_sum_complex C S a b D (fun P=>W ((P.absNorm:ℝ)/D)*g P)]
  have hsub : annularPrimeIdeals C a b D\S⊆
      (HeckePrimeAnnular.annulusSet b D).filter (fun P=>Prime P ∧ P∈C) := by
    intro P hP
    have hp := (mem_annularPrimeIdeals C a b D P).mp (Finset.mem_sdiff.mp hP).1
    apply Finset.mem_filter.mpr
    refine ⟨?_,hp.2.1,hp.1⟩
    apply ConcretePrimeRowBridge.mem_idealsUpTo.mpr
    refine ⟨Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp.2.1.ne_zero),?_⟩
    apply hp.2.2.2.trans
    apply Nat.floor_mono
    nlinarith [le_max_right (1:ℝ) b]
  apply Finset.sum_subset hsub
  intro P hP hnot
  have hw : W ((P.absNorm:ℝ)/D)=0 := by
    by_contra hn
    have hy := hW hn
    have hp := (Finset.mem_filter.mp hP).2
    apply hnot
    apply Finset.mem_sdiff.mpr
    constructor
    · apply (mem_annularPrimeIdeals C a b D P).mpr
      refine ⟨hp.2,hp.1,?_,?_⟩
      · apply (Nat.floor_lt (mul_nonneg hD.le ha.le)).mpr
        have := (lt_div_iff₀ hD).mp hy.1
        nlinarith
      · apply Nat.le_floor
        have := (div_lt_iff₀ hD).mp hy.2
        nlinarith
    · intro hs
      have := hS P hs
      have := (lt_div_iff₀ hD).mp hy.1
      linarith
  simp only [hw,zero_mul]

theorem central_phase_eq_amplitude (M : Id) [NeZero M]
    [Finite (HeckeFamily.O ⧸ M)] (H : Subgroup (HeckeFamily.O ⧸ M)ˣ)
    (S : Finset Id) (u : HeckeFamily.O) (W : ℝ→ℂ) (a b D : ℝ)
    (ha : 0<a) (hab : a≤b) (hD : 0<D) (hW : Function.support W⊆Set.Ioo a b)
    (hS : ∀P∈S,(P.absNorm:ℝ)≤a*D) (z : ℂ) :
    (∑P∈pool (RayQuotient.identityClass M H) S a b D,
      W ((P.val.absNorm:ℝ)/D)*(P.val.absNorm:ℂ)^(z-1)*
        (-star (CanonicalRowCompletion.idealRowHom u P.val)))=
      -(D:ℂ)^(z-1/2)*HeckePrimeRow.canonicalPrimeAmplitude M H u W b D z := by
  have he := weighted_pool_eq_annular (RayQuotient.identityClass M H) S W a b D ha hab hD hW hS
    (fun P=>(P.absNorm:ℂ)^(z-1)*(-star (CanonicalRowCompletion.idealRowHom u P)))
  simp_rw [mul_assoc] at ⊢
  rw [he]
  unfold HeckePrimeRow.canonicalPrimeAmplitude
  rw [←mul_assoc,neg_mul,←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
  have hexp : (z-(1/2:ℂ)) + -(1/2:ℂ)=z-1 := by ring
  rw [hexp,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  have hprime := (Finset.mem_filter.mp hP).2.1
  have hn : (0:ℝ)<P.absNorm := by exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hprime.ne_zero)
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg hn.le hD.le]
  have hd : (D:ℂ)^(z-1)≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hD.ne'))
  field_simp
  simp only [starRingEnd_apply,Complex.ofReal_natCast]
  ring

theorem central_phase_norm (M : Id) [NeZero M]
    [Finite (HeckeFamily.O ⧸ M)] (H : Subgroup (HeckeFamily.O ⧸ M)ˣ)
    (S : Finset Id) (u : HeckeFamily.O) (W : ℝ→ℂ) (a b D : ℝ)
    (ha : 0<a) (hab : a≤b) (hD : 0<D) (hW : Function.support W⊆Set.Ioo a b)
    (hS : ∀P∈S,(P.absNorm:ℝ)≤a*D) (z : ℂ) :
    ‖∑P∈pool (RayQuotient.identityClass M H) S a b D,
      W ((P.val.absNorm:ℝ)/D)*(P.val.absNorm:ℂ)^(z-1)*
        (-star (CanonicalRowCompletion.idealRowHom u P.val))‖=
      D^(z.re-1/2)*‖HeckePrimeRow.canonicalPrimeAmplitude M H u W b D z‖ := by
  rw [central_phase_eq_amplitude M H S u W a b D ha hab hD hW hS z,
    norm_mul,norm_neg,Complex.norm_cpow_eq_rpow_re_of_pos hD]
  norm_num

theorem power_fixed_exclusions (S : Finset Id) (a ellMin : ℝ) (ha : 0<a) (hmin : 0<ellMin)
    {ι : Type*} (ell : ι→ℝ) (hell : ∀j,ellMin≤ell j) :
    ∀ᶠZ : ℝ in Filter.atTop,∀j,∀P∈S,(P.absNorm:ℝ)≤a*Z^(ell j) := by
  have ht := (tendsto_rpow_atTop hmin).const_mul_atTop ha
  filter_upwards [ht.eventually (Filter.eventually_ge_atTop (∑P∈S,(P.absNorm:ℝ))),
    Filter.eventually_ge_atTop (1:ℝ)] with Z hnorm hZ j P hP
  calc
    (P.absNorm:ℝ) ≤ ∑Q∈S,(Q.absNorm:ℝ) := Finset.single_le_sum (fun Q _=>Nat.cast_nonneg _) hP
    _ ≤ a*Z^ellMin := hnorm
    _ ≤ a*Z^(ell j) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (hell j)) ha.le

end SevenEighths.ProbeRaySlots
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.ExceptionalRows
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeExceptionalRows
open HeckeFamily UniqueFactorizationMonoid

theorem row_ideal_dvd (S : Finset (Ideal O)) {u : O} (hu : u ∈ rows S) :
    (Ideal.span {u} : Ideal O) ∣ (∏ P ∈ S, P)^5 := by
  have hI : (Ideal.span {u} : Ideal O) ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hu.1
  have hle : normalizedFactors (Ideal.span {u}) ≤ 5 • S.val := by
    apply Multiset.le_iff_count.mpr
    intro P
    by_cases hP : P ∈ normalizedFactors (Ideal.span {u})
    · have hp := hu.2 P hP
      have hc : S.val.count P = 1 := Multiset.count_eq_one_of_mem S.nodup hp.1
      rw [Multiset.count_nsmul, hc]
      omega
    · simp only [Multiset.count_eq_zero.mpr hP]
      exact Nat.zero_le _
  have hd := Multiset.prod_dvd_prod_of_le hle
  rw [Ideal.prod_normalizedFactors_eq_self hI, Multiset.prod_nsmul] at hd
  change (Ideal.span {u} : Ideal O) ∣ (S.prod id)^5
  simpa only [Finset.prod_val] using hd

theorem row_norm_bound (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    {u : O} (hu : u ∈ rows S) : (Ideal.span {u}).absNorm ≤ bound S := by
  have hd := map_dvd Ideal.absNorm (row_ideal_dvd S hu)
  apply Nat.le_of_dvd _ hd
  apply Nat.pos_of_ne_zero
  rw [ne_eq, Ideal.absNorm_eq_zero_iff]
  exact pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero))

end SevenEighths.HeckeExceptionalRows

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.LocalRamification
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeLocalRamification
open CenteredMomentCorrelation CenteredMomentCanonical
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O

theorem primePowerCharacter_eq_one_iff (P : Ideal O) [P.IsMaximal]
    {c : ℕ} (hc : 1 ≤ c) (χ : MulChar (O ⧸ P) ℂ) :
    primePowerCharacter P hc χ = 1 ↔ χ = 1 := by
  constructor
  · intro h
    apply MulChar.ext
    intro u
    obtain ⟨x,hx⟩ := primePowerReduction_surjective P hc (u : O ⧸ P)
    have hux : IsUnit x := by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      apply (Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk P (by omega)).mpr
      change Ideal.Quotient.mk P a = (u : O ⧸ P) at hx
      rw [hx]
      exact u.isUnit
    have heq := congrArg (fun f : MulChar (O ⧸ P^c) ℂ => f x) h
    rw [primePowerCharacter_apply, hx, MulChar.one_apply hux] at heq
    simpa only [MulChar.one_apply u.isUnit] using heq
  · rintro rfl
    apply MulChar.ext
    intro u
    rw [primePowerCharacter_apply, MulChar.one_apply u.isUnit,
      MulChar.one_apply (u.isUnit.map (primePowerReduction P hc))]

theorem canonicalPrimePowerCharacter_eq_one_iff (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {c : ℕ} (hc : 1 ≤ c) : canonicalPrimePowerCharacter P hg hc = 1 ↔ 6 ∣ c := by
  rw [canonicalPrimePowerCharacter, primePowerCharacter_eq_one_iff,
    ← orderOf_dvd_iff_pow_eq_one, actualSextic_order_six P hg hchar]

end SevenEighths.HeckeLocalRamification

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.RowNonprincipal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeRowNonprincipal
open HeckeFamily CanonicalRowCompletion CenteredMomentCanonical
open ConcretePrimeRowBridge hiding O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem nonprincipal_of_local_factor (χ : Character)
    (Q J P : Ideal O) [P.IsMaximal]
    (hQ : Q ≤ Ideal.span {λ₀ ^ 2})
    (φ : O →* ℂ) (hφ : CanonicalCoefficientClass.FactorsModulo Q φ)
    (hJ : CanonicalQuadraticSieve.Supported J)
    (hg : λ₀ ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {c : ℕ} (hc : 1 ≤ c) (hc6 : ¬ 6 ∣ c)
    (hcop : IsCoprime (Q * J) (P ^ c))
    (hrow : ∀ n : O, λ₀ ^ 2 ∣ n - 1 →
      elementCoeff χ n = φ n * idealRowHom n (P ^ c * J)) :
    χ.residue ≠ 1 := by
  let ψ := canonicalPrimePowerCharacter P hg hc
  have hψ : ψ ≠ 1 := fun h => hc6 ((HeckeLocalRamification.canonicalPrimePowerCharacter_eq_one_iff P hg hchar hc).mp h)
  obtain ⟨u, hu⟩ : ∃ u : (O ⧸ P ^ c)ˣ, ψ (u : O ⧸ P ^ c) ≠ 1 := by
    by_contra! h
    apply hψ
    apply MulChar.ext
    intro u
    rw [MulChar.one_apply u.isUnit]
    exact h u
  let e := Ideal.quotientInfEquivQuotientProd (Q * J) (P ^ c) hcop
  obtain ⟨x, hx⟩ := e.surjective ((1 : O ⧸ Q * J), (u : O ⧸ P ^ c))
  obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (Ideal.Quotient.mk (Q * J) n, Ideal.Quotient.mk (P ^ c) n) = (1, (u : O ⧸ P ^ c)) at hx
  have hnQJ := congrArg Prod.fst hx
  have hnP := congrArg Prod.snd hx
  dsimp only at hnQJ hnP
  have hn : n - 1 ∈ Q * J := Ideal.Quotient.eq.mp (by simpa using hnQJ)
  have hnQ : n - 1 ∈ Q := Ideal.mul_le_left hn
  have hnJ : n - 1 ∈ J := Ideal.mul_le_right hn
  have hnprimary : λ₀ ^ 2 ∣ n - 1 := Ideal.mem_span_singleton.mp (hQ hnQ)
  have hv : elementCoeff χ n = ψ (u : O ⧸ P ^ c) := by
    rw [hrow n hnprimary, map_mul, hφ n 1 hnQ, map_one, one_mul,
      idealRowHom_congr_mod J n 1 hnJ, idealRowHom_one_supported J hJ, mul_one]
    rw [← canonicalPrimePowerCharacter_mk P hg hc n, hnP]
  have hv0 : elementCoeff χ n ≠ 0 := hv ▸ (MulChar.apply_ne_zero_iff.mpr u.isUnit)
  intro hχ
  have hunit : IsUnit (Ideal.Quotient.mk χ.modulus n) := MulChar.apply_ne_zero_iff.mp hv0
  have hv1 : elementCoeff χ n = 1 := by
    change χ.residue _ = 1
    rw [hχ, MulChar.one_apply hunit]
  exact hu (hv.symm.trans hv1)

theorem actual_row_nonprincipal (η χ : Character) (m f z : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀ ^ 2 ∣ r - 1) (hx : f ^ 4 * z = (u : O) * λ₀ ^ a * (2 : O) ^ b * r)
    (P J : Ideal O) [P.IsMaximal]
    (hg : λ₀ ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (hJ : CanonicalQuadraticSieve.Supported J)
    {c : ℕ} (hc : 1 ≤ c) (hc6 : ¬ 6 ∣ c)
    (hsplit : Ideal.span {r} = P ^ c * J)
    (hcop : IsCoprime ((η.modulus * Ideal.span {m} * Ideal.span {(72 : O)}) * J) (P ^ c))
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m f z n) :
    χ.residue ≠ 1 := by
  let φ := HeckeRowClosure.elementHom η * coprimalityMask m * numeratorBadTwist u a b r hr
  refine nonprincipal_of_local_factor χ (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)}) J P
      ?_ φ ?_ hJ hg hchar hc hc6 hcop ?_
  · have hd3 : λ₀ ^ 2 ∣ (3 : O) := ActualEisensteinCubic.lambda_sq_dvd_three
    have hd72 : λ₀ ^ 2 ∣ (72 : O) := hd3.trans ⟨24, by norm_num⟩
    exact Ideal.mul_le_right.trans ((Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.mem_span_singleton.mpr hd72))
  · intro x y hxy
    change ((HeckeRowClosure.elementHom η x * coprimalityMask m x) * numeratorBadTwist u a b r hr x) =
      ((HeckeRowClosure.elementHom η y * coprimalityMask m y) * numeratorBadTwist u a b r hr y)
    rw [HeckeRowClosure.elementHom_periodic η x y (Ideal.mul_le_left (Ideal.mul_le_left hxy)),
      coprimalityMask_periodic m x y (Ideal.mul_le_right (Ideal.mul_le_left hxy)),
      numeratorBadTwist_periodic u a b r hr x y (Ideal.mul_le_right hxy)]
  · intro n hn
    rw [hχ n, rowTwist_eq_actualPeriodicRow_primary _ _ _ _ hmLam hm2 u a b r hr hpr hx n hn]
    change φ n * idealRowHom n (Ideal.span {r}) = φ n * idealRowHom n (P ^ c * J)
    rw [hsplit]

open UniqueFactorizationMonoid in

theorem extract_prime_power (I : Ideal O) (hI : CanonicalQuadraticSieve.Supported I)
    (P : Ideal O) (hP : P ∈ normalizedFactors I) :
    ∃ J : Ideal O, I = P ^ (normalizedFactors I).count P * J ∧
      CanonicalQuadraticSieve.Supported J ∧ IsCoprime J P := by
  let S := (normalizedFactors I).toFinset
  let J := ∏ Q ∈ S.erase P, Q ^ (normalizedFactors I).count Q
  have hPS : P ∈ S := Multiset.mem_toFinset.mpr hP
  have hsplit : I = P ^ (normalizedFactors I).count P * J := by
    calc
      I = (normalizedFactors I).prod := (Ideal.prod_normalizedFactors_eq_self hI.1).symm
      _ = ∏ Q ∈ S, Q ^ (normalizedFactors I).count Q := Finset.prod_multiset_count _
      _ = P ^ (normalizedFactors I).count P * J :=
        (Finset.mul_prod_erase S (fun Q => Q ^ (normalizedFactors I).count Q) hPS).symm
  have hgood := supported_factors_good I hI P hP
  let : P.IsMaximal := hgood.1
  refine ⟨J, hsplit, ?_, ?_⟩
  · exact (CanonicalQuadraticSieve.supported_mul_iff _ _).mp (hsplit ▸ hI) |>.2
  · apply IsCoprime.prod_left
    intro Q hQ
    obtain ⟨hQP, hQS⟩ := Finset.mem_erase.mp hQ
    have hgoodQ := supported_factors_good I hI Q (Multiset.mem_toFinset.mp hQS)
    let : Q.IsMaximal := hgoodQ.1
    exact (Ideal.isCoprime_of_isMaximal hQP).pow_left

open UniqueFactorizationMonoid in

theorem principal_row_multiplicity (η χ : Character) (m f z : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀ ^ 2 ∣ r - 1) (hx : f ^ 4 * z = (u : O) * λ₀ ^ a * (2 : O) ^ b * r)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m f z n)
    (hprincipal : χ.residue = 1)
    (P : Ideal O) (hP : P ∈ normalizedFactors (Ideal.span {r}))
    (hcop : IsCoprime (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)}) P) :
    6 ∣ (normalizedFactors (Ideal.span {r})).count P := by
  by_contra hc6
  have hgood := supported_factors_good (Ideal.span {r}) hr P hP
  let : P.IsMaximal := hgood.1
  obtain ⟨J, hsplit, hJ, hJP⟩ := extract_prime_power _ hr P hP
  have hc : 1 ≤ (normalizedFactors (Ideal.span {r})).count P := Multiset.count_pos.mpr hP
  exact actual_row_nonprincipal η χ m f z hmLam hm2 u a b r hr hpr hx P J
    hgood.2.1 hgood.2.2 hJ hc hc6 hsplit ((hcop.mul_left hJP).pow_right) hχ hprincipal

open UniqueFactorizationMonoid in

theorem principal_row_fixed_support (η χ : Character) (m f z : O)
    (hm : m ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀ ^ 2 ∣ r - 1) (hx : f ^ 4 * z = (u : O) * λ₀ ^ a * (2 : O) ^ b * r)
    (hχ : ∀ n, elementCoeff χ n = rowTwist (HeckeRowClosure.elementHom η) m f z n)
    (hprincipal : χ.residue = 1)
    (hfree : ∀ P ∈ normalizedFactors (Ideal.span {r}),
      (normalizedFactors (Ideal.span {r})).count P < 6) :
    r ∈ HeckeExceptionalRows.rows
      (normalizedFactors (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)})).toFinset := by
  let Q := η.modulus * Ideal.span {m} * Ideal.span {(72 : O)}
  have hQ : Q ≠ ⊥ := mul_ne_zero
    (mul_ne_zero η.modulus_ne_bot (Ideal.span_singleton_eq_bot.not.mpr hm))
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))
  refine ⟨Ideal.span_singleton_eq_bot.not.mp hr.1, ?_⟩
  intro P hP
  refine ⟨?_, hfree P hP⟩
  apply Multiset.mem_toFinset.mpr
  have hgood := supported_factors_good (Ideal.span {r}) hr P hP
  let : P.IsMaximal := hgood.1
  apply (Ideal.mem_normalizedFactors_iff hQ).mpr
  refine ⟨Ideal.isPrime_of_prime (prime_of_normalized_factor P hP), ?_⟩
  by_contra hQP
  have hcop : IsCoprime Q P := by
    apply Ideal.coprime_of_no_prime_ge
    intro J hQJ hPJ hJ
    have hPJ' : P = J := hgood.1.eq_of_le hJ.ne_top hPJ
    exact hQP (hPJ' ▸ hQJ)
  have hd := principal_row_multiplicity η χ m f z hmLam hm2 u a b r hr hpr hx hχ hprincipal P hP hcop
  exact Nat.not_dvd_of_pos_of_lt (Multiset.count_pos.mpr hP) (hfree P hP) hd

end SevenEighths.HeckeRowNonprincipal

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.PrimeNonprincipal
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckePrimeNonprincipal
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem inverse_twist_elementCoeff (η χ θ : Character) (m f z : O)
    (hχ : ∀ n, elementCoeff χ n=rowTwist (elementHom η) m f z n) (n : O) :
    elementCoeff ((χ.inverse.product θ).inverse) n =
      rowTwist (elementHom (η.product θ.inverse)) m f z n := by
  rw [elementCoeff_inverse,elementCoeff_product,elementCoeff_inverse,mul_inv_rev,inv_inv,hχ]
  change _ = elementCoeff (η.product θ.inverse) n * idealRowHom (m^6*f^4*z) (Ideal.span {n})
  rw [elementCoeff_product,elementCoeff_inverse]
  change (elementCoeff θ n)⁻¹ *
    (elementCoeff η n * idealRowHom (m^6*f^4*z) (Ideal.span {n})) = _
  ring

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end SevenEighths.HeckePrimeNonprincipal

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.PrimeScale
namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace SevenEighths.HeckePrimeScale
open HeckeFamily

theorem product_modulus_bound (χ ψ : Character) :
    (χ.product ψ).modulus.absNorm≤χ.modulus.absNorm*ψ.modulus.absNorm := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Finite (O ⧸ ψ.modulus) := Ring.HasFiniteQuotients.finiteQuotient ψ.modulus_ne_bot
  exact FiniteConductor.absNorm_inf_le_mul χ.modulus ψ.modulus

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.HeckePrimeScale.instFiniteQuotientOIdeal
theorem twisted_modulus_bound (χ : Character) (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH χ θ).modulus.absNorm≤χ.modulus.absNorm*M.absNorm :=
  product_modulus_bound χ (HeckeRayQuotient.character M H hH θ)

end SevenEighths.HeckePrimeScale

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.Principal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalRowCompletion
open CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma rawRow_elementCoeff (u : FreeRow) (n : O) :
    elementCoeff (rawRow u) n = rowTwist (HeckeRowClosure.elementHom
      (fixedSourcePrincipal ∅ (by simp))) rowMaskElement 1 u.val n :=
  (Classical.choose_spec (HeckeRowClosure.exists_row_character_with_conductor
    (fixedSourcePrincipal ∅ (by simp)) rowMaskElement 1 u.val
    rowMaskElement_ne_zero one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))).2 n

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.PrincipalMask
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma calibration_nonzero_supported (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (a : O)
    (ha : (calibrationForSet S hS).residueMonoid a≠0) : Supported (Ideal.span {a}) := by
  have hu := (calibrationForSet S hS).residue.apply_ne_zero_iff.mp ha
  have hc := (CubicEisenstein.isUnit_quotient_span_iff _ _).mp hu
  have havoid := (calibrationForSet_coprime_iff S hS a).mp hc
  rw [supported_span_iff]
  constructor
  · intro hd
    exact havoid (Ideal.span {λ₀}) (hbad (Finset.mem_insert_self _ _))
      (Ideal.mem_span_singleton.mpr hd)
  · intro hd
    exact havoid (Ideal.span {(2:O)}) (hbad (by simp [CanonicalQuadraticSieve.fixedBadPrimes]))
      (Ideal.mem_span_singleton.mpr hd)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.DetectorZeros
namespace OAI

noncomputable section
open scoped Classical Topology
open Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily

variable {ι : Type*} [Fintype ι]

lemma detectorMaximum_mem (χ : ι→Character) (T : ℝ) : detectorMaximum χ T∈detectorRealParts χ T :=
  Finset.max'_mem _ _

lemma detectorMaximum_bounds (χ : ι→Character) (T : ℝ) :
    (51/100:ℝ)≤detectorMaximum χ T ∧ detectorMaximum χ T≤1 := by
  constructor
  · exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  · apply Finset.max'_le
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · norm_num
    · obtain ⟨⟨i,s⟩,hs,rfl⟩ := Finset.mem_image.mp hx
      exact (mem_detectorFamilyZeros χ T i s |>.mp hs).2.1

lemma detector_zero_re_le_maximum (χ : ι→Character) (T : ℝ) (i : ι) {s : ℂ}
    (hs : (51/100:ℝ)≤ s.re) (ht : |s.im|≤T) (hz : LFunction (χ i) s=0)
    (hpole : ¬((χ i).residue=1 ∧ s=1)) : s.re≤detectorMaximum χ T := by
  have hle : s.re≤1 := by
    by_contra hn
    exact LFunction_ne_zero_of_one_lt_re (χ i) (lt_of_not_ge hn) hz
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨(i,s),(mem_detectorFamilyZeros χ T i s).mpr ⟨hs,hle,ht,hz,hpole⟩,rfl⟩)

lemma detectorMaximum_attained (χ : ι→Character) (T : ℝ)
    (hmax : (51/100:ℝ)<detectorMaximum χ T) :
    ∃i s,LFunction (χ i) s=0 ∧ ¬((χ i).residue=1 ∧ s=1) ∧
      |s.im|≤T ∧ s.re=detectorMaximum χ T := by
  have hm := detectorMaximum_mem χ T
  rcases Finset.mem_insert.mp hm with hm|hm
  · exact False.elim ((ne_of_gt hmax) hm)
  · obtain ⟨⟨i,s⟩,hs,heq⟩ := Finset.mem_image.mp hm
    have hz := (mem_detectorFamilyZeros χ T i s).mp hs
    exact ⟨i,s,hz.2.2.2.1,hz.2.2.2.2,hz.2.2.1,heq⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.DetectorBins
namespace OAI

noncomputable section
open scoped Classical Topology
open Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily
variable {ι : Type*} [Fintype ι]

lemma detectorMaximum_eq_nonprincipal (χ : ι→Character) (hχ : ∀i,(χ i).residue≠1) (T : ℝ) :
    detectorMaximum χ T=HeckeDetectorZeros.zeroMaximum χ hχ T := by
  have hz (i : ι) : detectorZeroFinset (χ i) T=HeckeDetectorZeros.zeroFinset (χ i) (hχ i) T := by
    ext s
    simp [hχ i]
  have hr : detectorRealParts χ T=HeckeDetectorZeros.realParts χ hχ T := by
    simp only [detectorRealParts,HeckeDetectorZeros.realParts,detectorFamilyZeros,HeckeDetectorZeros.familyZeros,hz]
  unfold detectorMaximum HeckeDetectorZeros.zeroMaximum
  simp only [hr]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.Conductor
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeRowClosure ProbePhysical
local notation "O" => HeckeFamily.O

theorem rawRow_conductor (u : FreeRow) :
    (rawRow u).modulus.absNorm≤ conductorConstant*(Ideal.span {u.val}:Ideal O).absNorm := by
  have hb := (Classical.choose_spec
    (exists_row_character_with_conductor (fixedSourcePrincipal ∅ (by simp)) rowMaskElement 1 u.val
      rowMaskElement_ne_zero one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))).1
  change (rawRow u).modulus.absNorm≤_ at hb
  simpa [rowConductorBound,conductorConstant,fixedSourcePrincipal,HeckeRayFamily.character,
    Character.ofResidue] using hb

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RayCharacterFamily
namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.ProbeRayCharacterFamily
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.ProbeRayCharacterFamily.instFiniteQuotientOIdeal_solutions
omit [NeZero M] in
theorem fixedTwistSupport_prime : ∀P∈fixedTwistSupport M,Prime P := by
  intro P hP
  exact prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

lemma inverse_twist_base_modulus (θ : RayQuotient.Characters M H) :
    ((fixedSourcePrincipal ∅ (by simp)).product
      (HeckeRayQuotient.character M H hH θ).inverse).modulus=M := by
  change (1:Ideal O)⊓M=M
  simp

theorem large_supported_twists_nonprincipal (u : FreeRow)
    (hs : Supported (Ideal.span {u.val}))
    (hl : (HeckeExceptionalRows.bound (fixedTwistSupport M):ℝ)< rowNorm u)
    (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).residue≠1 := by
  obtain ⟨v,hv⟩ := exists_supported_primary_unit u.val hs
  let r : O := (v:O)*u.val
  have hspan : (Ideal.span {r}:Ideal O)=Ideal.span {u.val} :=
    Ideal.span_singleton_mul_left_unit v.isUnit u.val
  have hr : Supported (Ideal.span {r}) := hspan.symm ▸ hs
  have hx : (1:O)^4*u.val=(v⁻¹:Oˣ).val*λ₀^0*(2:O)^0*r := by simp [r]
  let η := (fixedSourcePrincipal ∅ (by simp)).product
    (HeckeRayQuotient.character M H hH θ).inverse
  let χ := (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).inverse
  have hχ : ∀n,elementCoeff χ n=rowTwist (HeckeRowClosure.elementHom η) rowMaskElement 1 u.val n :=
    HeckePrimeNonprincipal.inverse_twist_elementCoeff _ _ _ _ _ _ (rawRow_elementCoeff u)
  intro hp
  have hprincipal : χ.residue=1 := by
    change (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).residue⁻¹=1
    exact congrArg Inv.inv hp |>.trans inv_one
  have hfixed := HeckeRowNonprincipal.principal_row_fixed_support η χ rowMaskElement 1 u.val
    rowMaskElement_ne_zero (dvd_mul_left _ _) (dvd_mul_right _ _) v⁻¹ 0 0 r hr hv hx hχ hprincipal
    (fun P _=>hspan.symm ▸ u.property.2 P)
  have hη : η.modulus=M := inverse_twist_base_modulus M H hH θ
  rw [hη] at hfixed
  have hn := HeckeExceptionalRows.row_norm_bound (fixedTwistSupport M) (fixedTwistSupport_prime M) hfixed
  rw [hspan] at hn
  exact not_lt_of_ge (show rowNorm u≤(HeckeExceptionalRows.bound (fixedTwistSupport M):ℝ) by unfold rowNorm;exact_mod_cast hn) hl

theorem raw_twisted_conductor (u : FreeRow) (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).modulus.absNorm≤
      conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm := by
  have ht := HeckePrimeScale.twisted_modulus_bound M H hH (rawRow u).inverse θ
  change _≤(rawRow u).modulus.absNorm*M.absNorm at ht
  exact ht.trans (by simpa only [mul_assoc,mul_left_comm,mul_comm] using
    Nat.mul_le_mul_right M.absNorm (rawRow_conductor u))
omit [NeZero M] in
theorem canonical_amplitude_raw (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (u : FreeRow) (W : ℝ→ℂ) (a b D : ℝ)
    (hD : 0<D) (hW : Function.support W⊆Set.Ioo a b)
    (hsmall : ∀P∈S,(P.absNorm:ℝ)≤a*D) (z : ℂ) :
    HeckePrimeRow.canonicalPrimeAmplitude M H u.val W b D z=
      HeckePrimeRay.rayPrimePolynomial M H (rawRow u).inverse W b D (1-z.re) z.im := by
  unfold HeckePrimeRow.canonicalPrimeAmplitude HeckePrimeRay.rayPrimePolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  have hp := (Finset.mem_filter.mp hP).2.1
  have he : -HeckeDyadic.shift (1-z.re) z.im=z-1 := by
    apply Complex.ext <;> simp [HeckeDyadic.shift]
  simp only [HeckePrimeAnnular.annularWeight,he]
  by_cases hw : W ((P.absNorm:ℝ)/D)=0
  · simp [hw]
  have hPS : P∉S := by
    intro hPS
    have hh := (lt_div_iff₀ hD).mp (hW hw).1
    have := hsmall P hPS
    linarith
  rw [idealCoeff_inverse_conj,rawRow_prime_outside S hS hbad u ⟨P,hp⟩ hPS]
  exact mul_assoc _ _ _

omit H hH in
theorem large_supported_twists_eventually (d : ℝ) (hd : 0<d) :
    ∀ᶠZ : ℝ in Filter.atTop,∀u : FreeRow,Z^d≤ rowNorm u →
      Supported (Ideal.span {u.val}) → ∀(H : Subgroup (O ⧸ M)ˣ)
      (hH : RayOrthogonality.globalUnits M≤H) (θ : RayQuotient.Characters M H),
      (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).residue≠1 := by
  filter_upwards [(tendsto_rpow_atTop hd).eventually
    (Filter.eventually_gt_atTop (HeckeExceptionalRows.bound (fixedTwistSupport M):ℝ))]
    with Z hZ u hu hs H hH θ
  exact large_supported_twists_nonprincipal M H hH u hs (hZ.trans_le hu) θ

omit M H hH in
theorem source_maximum_dominates {ι : Type*} [Fintype ι]
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character) (u : FreeRow)
    (ψ : ι→Character) (T : ℝ) :
    detectorMaximum ψ T≤detectorMaximum (sourceDetectorFamily S hS η u ψ) T := by
  rcases lt_or_ge (51/100:ℝ) (detectorMaximum ψ T) with hm|hm
  · obtain ⟨j,s,hz,hpole,ht,heq⟩ := detectorMaximum_attained ψ T hm
    rw [←heq]
    exact detector_zero_re_le_maximum (sourceDetectorFamily S hS η u ψ) T (Sum.inr j)
      (by rw [heq];exact hm.le) ht hz hpole
  · exact hm.trans (detectorMaximum_bounds _ T).1

omit M H hH in
theorem source_nonprincipal_maximum_dominates {ι : Type*} [Fintype ι]
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character) (u : FreeRow)
    (ψ : ι→Character) (hψ : ∀j,(ψ j).residue≠1) (T : ℝ) :
    HeckeDetectorZeros.zeroMaximum ψ hψ T≤detectorMaximum (sourceDetectorFamily S hS η u ψ) T := by
  rw [←detectorMaximum_eq_nonprincipal ψ hψ T]
  exact source_maximum_dominates S hS η u ψ T

end SevenEighths.ProbeRayCharacterFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicGeometry
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.HeckeDetectorDyadicGeometry
open HeckeDyadic

lemma uniform_scale_threshold (dmin A : ℝ) (hd : 0<dmin) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → A≤Z^d := by
  have hh := constant_absorbed_eventually A dmin hd
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hA hZ d hd'
  exact hA.trans (Real.rpow_le_rpow_of_exponent_le hZ hd')

end SevenEighths.HeckeDetectorDyadicGeometry

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RayPhaseBins
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeRayPhaseBins
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbeRayCharacterFamily
open HeckePrimeAmplitudeBins ProbeRaySlots
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance instFiniteQuotientOIdeal_solutions : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_phase_bins (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A) (hAB : A≤B)
    (hWs : Function.support W⊆Ioo A B) (hW : ContDiff ℝ ∞ W)
    (R dmin dmax rmin τ ε e κ cost mesh σmin σmax δ : ℝ)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀(η : Character) (u : FreeRow),Z^δ≤ rowNorm u →
      CanonicalQuadraticSieve.Supported (Ideal.span {u.val}) →
      (conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^d →
    ∀(a : ℝ) (i : ℕ),51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u
        (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse)) (3*(i+1:ℕ)*Z^τ)<a+2*e →
    ∀(r : ℝ) (z : ℂ),rmin≤ r → r≤R → σmin≤1-z.re → 1-z.re≤σmax →
      |z.im|+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^cost →
    let D := (Z^d)^r
    let Q := HeckePrimeRow.canonicalPrimeAmplitude M H u.val W B D z
    let g := amplitude D (a-1/2) mesh Q
    0≤g ∧ g≤a-1/2 ∧ g∈labels (a-1/2) mesh ∧
      ‖Q‖≤D^(g+mesh) ∧ (0<g → (Z^d)^(2*r*g)≤‖Q‖^2) ∧
      ‖∑P∈pool (RayQuotient.identityClass M H) S A B D,
        W ((P.val.absNorm:ℝ)/D)*(P.val.absNorm:ℂ)^(z-1)*
          (-star (CanonicalRowCompletion.idealRowHom u.val P.val))‖≤D^(z.re-1/2+g+mesh) := by
  have hb := HeckePrimeAmplitudeActual.ray_amplitude_bins M H hH W A B hA
    (hWs.trans Ioo_subset_Icc_self) hW R dmin dmax rmin τ ε e κ cost mesh σmin σmax
    hR hdmin hdmax hrmin hτ hε he he' hκ hcost hmesh hbudget hgap
  have hn := large_supported_twists_eventually M δ hδ
  have ht := ProbeRaySlots.power_fixed_exclusions S A (dmin*rmin) hA (mul_pos hdmin hrmin)
    (fun p : {p : ℝ×ℝ // dmin≤p.1 ∧ rmin≤p.2}=>p.val.1*p.val.2)
    (fun p=>mul_le_mul p.property.1 p.property.2 hrmin.le (hdmin.trans_le p.property.1).le)
  filter_upwards [hb,hn,ht,eventually_ge_atTop (1:ℝ)] with Z hb hn ht hZ
  intro d hd hd' hU hT η u hu hs hcond a i ha ha' hbin r z hr hr' hσ hσ' hf hh
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hD : 0<(Z^d)^r := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hZp _) _
  have hsmall : ∀P∈S,(P.absNorm:ℝ)≤A*(Z^d)^r := by
    intro P hP
    rw [←Real.rpow_mul hZp.le]
    exact ht ⟨(d,r),hd,hr⟩ P hP
  have hnp := hn u hu hs H hH
  have hzmax := (source_nonprincipal_maximum_dominates S hS η u
    (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse) hnp _).trans_lt hbin
  have hq (θ : RayQuotient.Characters M H) :
      ((HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).modulus.absNorm:ℝ)≤Z^d :=
    (show ((HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).modulus.absNorm:ℝ)≤
      (conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm:ℝ) by
        exact_mod_cast raw_twisted_conductor M H hH u θ).trans hcond
  have heq := canonical_amplitude_raw M H S hS hbad u W A B ((Z^d)^r) hD hWs hsmall z
  have hbins := hb d hd hd' hU hT (rawRow u).inverse hnp a i ha ha' hzmax
    r (1-z.re) z.im hr hr' hσ hσ' hq hf hh
  rw [←heq] at hbins
  refine ⟨hbins.1,hbins.2.1,hbins.2.2.1,hbins.2.2.2.1,hbins.2.2.2.2,?_⟩
  rw [central_phase_norm M H S u.val W A B ((Z^d)^r) hA hAB hD hWs hsmall z]
  calc
    _ ≤ ((Z^d)^r)^(z.re-1/2)*((Z^d)^r)^(_+mesh) :=
      mul_le_mul_of_nonneg_left hbins.2.2.2.1 (Real.rpow_nonneg hD.le _)
    _ = _ := by rw [←Real.rpow_add hD];congr 1;ring
end SevenEighths.ProbeRayPhaseBins

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RayPoolDisjoint
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical
local notation "Id" => Ideal HeckeFamily.O

lemma annular_power_separation (a b r s : ℝ) (ha : 0<a) (hrs : r<s) :
    ∀ᶠZ : ℝ in atTop,b*Z^r<a*Z^s := by
  have hh := (tendsto_rpow_atTop (show 0<s-r by linarith)).eventually (eventually_gt_atTop (b/a))
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with Z hZ hZ0
  have ht : b<a*Z^(s-r) := by
    have h := (div_lt_iff₀ ha).mp hZ
    nlinarith
  have hp : 0<Z^r := Real.rpow_pos_of_pos hZ0 _
  calc
    b*Z^r < (a*Z^(s-r))*Z^r := mul_lt_mul_of_pos_right ht hp
    _=a*Z^s := by rw [mul_assoc,←Real.rpow_add hZ0];congr 1;congr 1;ring

theorem power_pools_eventually_disjoint {ι : Type*} [Fintype ι]
    (C : Set Id) (S : Finset Id) (a b ell : ι→ℝ)
    (ha : ∀i,0<a i) (hab : ∀i,a i≤b i) (hell : Function.Injective ell) :
    ∀ᶠZ : ℝ in atTop,∀i j, i≠j→Disjoint (pool C S (a i) (b i) (Z^(ell i)))
      (pool C S (a j) (b j) (Z^(ell j))) := by
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  by_cases hij : i=j
  · exact Filter.Eventually.of_forall (fun Z hn=>(hn hij).elim)
  have hne : ell i≠ell j := fun h=>hij (hell h)
  rcases lt_or_gt_of_ne hne with hlt|hgt
  · filter_upwards [annular_power_separation (a j) (b i) (ell i) (ell j) (ha j) hlt,
      eventually_gt_atTop (0:ℝ)] with Z hsep hZ _
    apply Finset.disjoint_left.mpr
    intro P hPi hPj
    have hi := pool_norm_bounds C S (ha i).le (hab i) (Real.rpow_pos_of_pos hZ _) P hPi
    have hj := pool_norm_bounds C S (ha j).le (hab j) (Real.rpow_pos_of_pos hZ _) P hPj
    nlinarith
  · filter_upwards [annular_power_separation (a i) (b j) (ell j) (ell i) (ha i) hgt,
      eventually_gt_atTop (0:ℝ)] with Z hsep hZ _
    apply Finset.disjoint_left.mpr
    intro P hPi hPj
    have hi := pool_norm_bounds C S (ha i).le (hab i) (Real.rpow_pos_of_pos hZ _) P hPi
    have hj := pool_norm_bounds C S (ha j).le (hab j) (Real.rpow_pos_of_pos hZ _) P hPj
    nlinarith

end SevenEighths.ProbeRaySlots
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RayPoolGood
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical CanonicalQuadraticSieve PrincipalSignalComparison
local notation "Id" => Ideal HeckeFamily.O

theorem prime_coprime_of_norm_gt (η : Character) (P : PrimeIdeal)
    (hN : (η.modulus.absNorm:ℝ)<(P.val.absNorm:ℝ)) : IsCoprime P.val η.modulus := by
  apply Ideal.coprime_of_no_prime_ge
  intro J hPJ hηJ hJ
  have hmax := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  have heq := hmax.eq_of_le hJ.ne_top hPJ
  rw [←heq] at hηJ
  have hd : P.val∣η.modulus := Ideal.dvd_iff_le.mpr hηJ
  have hn := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot))
    (map_dvd Ideal.absNorm hd)
  exact (not_le_of_gt hN) (by exact_mod_cast hn)

end SevenEighths.ProbeRaySlots
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CubeFiniteIntegral
namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma cube_buffered_heights (t : HeightSpace) (H B : ℝ) (i : ℕ)
    (ht : (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H) (hB : 0≤B)
    (hbuffer : H+B/2≤(3*i+2:ℕ)*B) :
    |t.1.1|≤(3*i+2:ℕ)*B ∧ |t.2|≤(3*i+2:ℕ)*B ∧
      |t.1.2|+B/2≤(3*i+2:ℕ)*B := by
  constructor
  · linarith [ht.1.1]
  constructor
  · linarith [ht.1.2]
  · linarith [ht.2]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CanonicalCubeBins
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem source_cube_height_eventually (τ : ℝ) (hτ : 0<τ) :
    ∀ᶠ Z : ℝ in atTop,1≤Z ∧ 2<Z^τ := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ))] with Z hZ hpow
  exact ⟨hZ,hpow⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CubeScale
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification
local notation "O" => HeckeFamily.O

theorem cube_height_budget_eventually (n : ℕ) (τ dmin cost : ℝ)
    (hτ : 0<τ) (hc : 0≤ cost) (hgap : 2*τ<dmin*cost) :
    ∀ᶠ Z : ℝ in atTop,∀i : ℕ,i≤n → ∀d : ℝ,dmin≤d →
      (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^cost := by
  have habs := HeckeDyadic.constant_absorbed_eventually
    ((3*(n:ℝ)+5)^2) (dmin*cost-2*τ) (by linarith)
  filter_upwards [habs,eventually_ge_atTop (1:ℝ)] with Z hC hZ
  intro i hi d hd
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hpow : 1≤Z^τ := Real.one_le_rpow hZ hτ.le
  have hi' : (i:ℝ)≤n := by exact_mod_cast hi
  have hx : 3+(3*i+2:ℕ)*Z^τ≤(3*(n:ℝ)+5)*Z^τ := by
    push_cast
    nlinarith
  calc
    _ ≤ ((3*(n:ℝ)+5)*Z^τ)^2 := by
      apply sq_le_sq₀ (by positivity) (by positivity) |>.mpr hx
    _ = (3*(n:ℝ)+5)^2*Z^(2*τ) := by
      rw [mul_pow]
      congr 1
      rw [←Real.rpow_two,←Real.rpow_mul hZp.le]
      congr 1
      ring
    _ ≤ Z^(dmin*cost-2*τ)*Z^(2*τ) :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le _)
    _ = Z^(dmin*cost) := by rw [←Real.rpow_add hZp];congr 1;ring
    _ ≤ (Z^d)^cost := by
      rw [←Real.rpow_mul hZp.le]
      exact Real.rpow_le_rpow_of_exponent_le hZ (mul_le_mul_of_nonneg_right hd hc)

theorem ray_cube_conductor_eventually (M : Ideal O) (ν : ℝ) (hν : 0<ν) :
    ∀ᶠ Z : ℝ in atTop,∀(u : FreeRow) (d : ℝ),rowNorm u≤Z^(d-ν) →
      (conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^d := by
  have hh := HeckeDyadic.constant_absorbed_eventually
    ((conductorConstant*M.absNorm:ℕ):ℝ) ν hν
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with Z hC hZ
  intro u d hu
  calc
    _ = ((conductorConstant*M.absNorm:ℕ):ℝ)*rowNorm u := by simp [rowNorm]
    _ ≤ Z^ν*Z^(d-ν) := mul_le_mul hC hu (by unfold rowNorm;positivity) (Real.rpow_nonneg hZ.le _)
    _ = Z^d := by rw [←Real.rpow_add hZ];congr 1;ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CentralHeightCost
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem cube_height_power_eventually (n : ℕ) (τ p loss : ℝ)
    (hτ : 0<τ) (hp : 0≤p) (hgap : τ*p<loss) :
    ∀ᶠ Z : ℝ in atTop,∀i : ℕ,i≤n → (3+(3*i+2:ℕ)*Z^τ)^p≤Z^loss := by
  have hh := HeckeDyadic.constant_absorbed_eventually ((3*(n:ℝ)+5)^p)
    (loss-τ*p) (by linarith)
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with Z hC hZ
  intro i hi
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hpow : 1≤Z^τ := Real.one_le_rpow hZ hτ.le
  have hi' : (i:ℝ)≤n := by exact_mod_cast hi
  have hx : 3+(3*i+2:ℕ)*Z^τ≤(3*(n:ℝ)+5)*Z^τ := by push_cast;nlinarith
  calc
    _ ≤ ((3*(n:ℝ)+5)*Z^τ)^p := Real.rpow_le_rpow (by positivity) hx hp
    _ = (3*(n:ℝ)+5)^p*Z^(τ*p) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hZp.le _),←Real.rpow_mul hZp.le]
    _ ≤ Z^(loss-τ*p)*Z^(τ*p) := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le _)
    _ = Z^loss := by rw [←Real.rpow_add hZp];congr 1;ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CubePhaseBins
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbeRayCharacterFamily
open HeckePrimeAmplitudeBins ProbeRaySlots
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_phase_bins_on_cube (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (hmax : ∀P∈S,P.IsMaximal)
    (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A) (hAB : A≤B)
    (hWs : Function.support W⊆Ioo A B) (hW : ContDiff ℝ ∞ W)
    (R dmin dmax rmin τ ε e κ cost mesh δ ν : ℝ) (n : ℕ)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hν : 0<ν) (hheight : 2*τ<dmin*cost) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀(η : Character) (u : FreeRow),Z^δ≤ rowNorm u →
      (ProbePhysical.calibrationForSet S hmax).residueMonoid u.val≠0 →
      rowNorm u≤Z^(d-ν) →
    ∀(a : ℝ) (i : ℕ),i≤n → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u
        (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse)) (3*(i+1:ℕ)*Z^τ)<a+2*e →
    ∀(r : ℝ) (t : ProbeMellinBoundary.HeightSpace),rmin≤ r → r≤R →
      ((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
    let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
    let D := (Z^d)^r
    let Q := HeckePrimeRow.canonicalPrimeAmplitude M H u.val W B D z
    let g := amplitude D (a-1/2) mesh Q
    0≤g ∧ g≤a-1/2 ∧ g∈labels (a-1/2) mesh ∧
      ‖Q‖≤D^(g+mesh) ∧ (0<g → (Z^d)^(2*r*g)≤‖Q‖^2) ∧
      ‖∑P∈pool (RayQuotient.identityClass M H) S A B D,
        W ((P.val.absNorm:ℝ)/D)*(P.val.absNorm:ℂ)^(z-1)*
          (-star (CanonicalRowCompletion.idealRowHom u.val P.val))‖≤D^(z.re-1/2+g+mesh) := by
  have hb := ProbeRayPhaseBins.actual_phase_bins M H hH S hS hbad W A B hA hAB hWs hW
    R dmin dmax rmin τ ε e κ cost mesh (33/50) (33/50) δ
    hR hdmin hdmax hrmin hτ hε he he' hκ hcost hmesh hδ hbudget hgap
  filter_upwards [hb,cube_height_budget_eventually n τ dmin cost hτ hcost hheight,
    ray_cube_conductor_eventually M ν hν,eventually_gt_atTop (0:ℝ)] with Z hb hh hc hZ
  intro d hd hd' hU hT η u hu hcal hrow a i hi ha ha' hbin r t hr hr' ht
  have hs := calibration_nonzero_supported S hmax hbad u.val hcal
  have hpow : 0≤Z^τ := Real.rpow_nonneg hZ.le _
  have hbuffer : ((3*i+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*i+2:ℕ)*Z^τ := by
    push_cast
    nlinarith
  have hfreq := (cube_buffered_heights t ((3*i+1:ℕ)*Z^τ) (Z^τ) i ht hpow hbuffer).2.2
  have hb' := hb d hd hd' hU hT η u hu hs (hc u d hrow) a i ha ha' hbin r
    ((17/50:ℂ)+t.1.2*Complex.I) hr hr'
    (by norm_num) (by norm_num) (by simpa using hfreq) (hh i hi d hd)
  exact hb'

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CubePrimeThresholds
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily ProbeRaySlots
local notation "O" => HeckeFamily.O

theorem central_pool_good_eventually (η : Character) (e c b dmin rmin : ℝ)
    (he : 0<e) (hc : 0<c) (hcb : c≤b) (hd : 0<dmin) (hr : 0< rmin) :
    ∀ᶠ Z : ℝ in atTop,∀(C : Set (Ideal O)) (S : Finset (Ideal O)) (d r : ℝ),dmin≤d → rmin≤ r →
      ∀P∈pool C S c b ((Z^d)^r),P.val∉S ∧ IsCoprime P.val η.modulus ∧
        (480:ℝ)≤P.val.absNorm ∧ 198*(P.val.absNorm:ℝ)^(-10*e)≤1/2 := by
  obtain ⟨Q0,hQ0,hsmall⟩ := ProbeEuler.central_correction_threshold e he
  have ht := (tendsto_rpow_atTop (mul_pos hd hr)).const_mul_atTop hc
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually (eventually_ge_atTop Q0),
    ht.eventually (eventually_gt_atTop (η.modulus.absNorm:ℝ))] with Z hZ hQ hη
  intro C S d r hdd hrr P hP
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hD : 0<(Z^d)^r := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hZp _) _
  have hle : c*Z^(dmin*rmin)≤ c*(Z^d)^r := by
    rw [←Real.rpow_mul hZp.le]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ
      (mul_le_mul hdd hrr hr.le (hd.trans_le hdd).le)) hc.le
  have hl := (pool_norm_bounds C S hc.le hcb hD P hP).1
  have hq : Q0≤(P.val.absNorm:ℝ) := hQ.trans (hle.trans (by linarith))
  exact ⟨(mem_pool C S c b _ P).mp hP |>.2.2.2,
    prime_coprime_of_norm_gt η P (hη.trans_le (hle.trans (by linarith))),hQ0.trans hq,hsmall _ hq⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CubePrimeBound
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots ProbeCentralAllSlots HeckePrimeAmplitudeBins
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_cube_prime_bound (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(u : FreeRow),u.val≠1 → Z^δ≤ rowNorm u →
      (calibrationForSet S hmax).residueMonoid u.val≠0 → rowNorm u≤Z^(d-margin) →
      ∀(a : ℝ) (i : ℕ),i≤n → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<a+2*e →
      ∀r : Fin N→ℝ,(∀j,rmin≤ r j) → (∀j,r j≤R) →
      let Y : Fin N→ℝ := fun j=>(Z^d)^(r j)
      let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      (∀j l,j≠l → Disjoint (T j) (T l)) →
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      let x : ℂ := (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I)
      let w : ℂ := (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
      let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
      let Q : Fin N→ℂ := fun j=>HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) z
      let g : Fin N→ℝ := fun j=>amplitude (Y j) (a-1/2) mesh (Q j)
      (∀j,0≤g j ∧ g j≤a-1/2 ∧ g j∈labels (a-1/2) mesh ∧
        ‖Q j‖≤(Y j)^(g j+mesh) ∧ (0<g j → (Z^d)^(2*r j*g j)≤‖Q j‖^2)) ∧
      ‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
          (fun j=>poolOutside M H S N c b Y j (P j).val (P j).property) W Y x w z‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+eps*(N+8))*Z^loss*
          (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh)) := by
  have hb (j : Fin N) := actual_phase_bins_on_cube M H hH S hS.prime hS.bad hmax (W j) c b hc hcb
    (hWs j) (hW j) R dmin dmax rmin τ ε e κ cost mesh δ margin n
    hR hdmin hdmax hrmin hτ hε he he1 hκ hcost hmesh hδ hbudget hgap hmargin hheight
  have hbAll := Filter.eventually_all.mpr hb
  obtain ⟨C,hC,hbound⟩ := ProbeCentralPrimeSum.actual_central_prime_sum N e eps c b A
    he he1 heps hc (hc.trans_le hcb) hA S hS hfirst hmax
  refine ⟨C,hC,?_⟩
  intro η
  have hscale := HeckeDetectorDyadicGeometry.uniform_scale_threshold dmin 2 hdmin
  filter_upwards [hbAll,central_pool_good_eventually η e c b dmin rmin he hc hcb hdmin hrmin,
    cube_height_power_eventually n τ (2+4*eps) loss hτ (by positivity) hloss,
    hscale,source_cube_height_eventually τ hτ] with Z hb hg hheightZ hscaleZ hZ
  intro d hd hd' u hu hulo hcal huhi a i hi ha ha1 hbin r hr hr'
  dsimp only
  intro hdis t ht
  let Y : Fin N→ℝ := fun j=>(Z^d)^(r j)
  let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let g : Fin N→ℝ := fun j=>amplitude (Y j) (a-1/2) mesh
    (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) z)
  have hU : 2≤Z^d := hscaleZ d hd
  have hUp : 0<Z^d := by linarith
  have hY (j : Fin N) : 1≤Y j := Real.one_le_rpow (by linarith) (hrmin.trans_le (hr j)).le
  have hYp (j : Fin N) : 0<Y j := zero_lt_one.trans_le (hY j)
  have hphase (j : Fin N) := hb j d hd hd' hU hZ.2 η u hulo hcal huhi a i hi ha ha1 hbin (r j) t (hr j) (hr' j) ht
  refine ⟨fun j=>⟨(hphase j).1,(hphase j).2.1,(hphase j).2.2.1,(hphase j).2.2.2.1,(hphase j).2.2.2.2.1⟩,?_⟩
  let p : Fin N→ℝ := fun j=>(Y j)^(g j+mesh)
  have hp (j : Fin N) : 1≤p j := Real.one_le_rpow (hY j) (by have := (hphase j).1;dsimp [g];linarith)
  have hph (j : Fin N) : ‖phaseSlot u (T j) (W j) (Y j) z‖≤(Y j)^(-(4/25:ℝ))*p j := by
    have hj := (hphase j).2.2.2.2.2
    have hsum : phaseSlot u (T j) (W j) (Y j) z=
        ∑P∈T j,W j ((P.val.absNorm:ℝ)/Y j)*(P.val.absNorm:ℂ)^(z-1)*
          (-star (CanonicalRowCompletion.idealRowHom u.val P.val)) :=
      Finset.sum_coe_sort (T j) (fun P=>W j ((P.val.absNorm:ℝ)/Y j)*(P.val.absNorm:ℂ)^(z-1)*
        (-star (CanonicalRowCompletion.idealRowHom u.val P.val)))
    have hj' : ‖phaseSlot u (T j) (W j) (Y j) z‖≤(Y j)^(-(4/25:ℝ)+g j+mesh) := by
      rw [hsum]
      convert (preTransparency := .instances) hj using 1
      simp only [Y,g,z]
      congr 1
      norm_num
    apply hj'.trans_eq
    dsimp only [p]
    rw [←Real.rpow_add (hYp j)]
    congr 1
    ring
  have hgood (j : Fin N) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : P∈T j) := hg (RayQuotient.identityClass M H) S d (r j) hd (hr j) P hP
  have hfreq := cube_buffered_heights t ((3*i+1:ℕ)*Z^τ) (Z^τ) i ht
    (Real.rpow_nonneg (zero_le_one.trans hZ.1) _) (by push_cast;have hh : 0≤Z^τ := Real.rpow_nonneg (zero_le_one.trans hZ.1) _;nlinarith)
  have hbound' := hbound u hu η (rayCubeFamily M H hH u) (Z^τ) a i hZ.2 ha ha1 hbin T
    (poolOutside M H S N c b Y) hdis (fun j P hP=>(hgood j P hP).2.1)
    (fun j P hP=>(hgood j P hP).2.2.1) (fun j P hP=>(hgood j P hP).2.2.2)
    W Y hY (fun j=>(hWs j).trans Ioo_subset_Icc_self) hWB
    (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I) z
    (by simp) (by simp) (by simp [z]) (by simpa using hfreq.1) (by simpa using hfreq.2.1) p hp hph
  have hprod : (∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)=∏j,(Y j)^(-(4/25:ℝ)+g j+mesh) := by
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    dsimp only [p]
    rw [←Real.rpow_add (hYp j)]
    congr 1
    ring
  calc
    _ ≤ C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+eps*(N+8))*
        (3+(3*i+2:ℕ)*Z^τ)^(2+4*eps)*((∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)) := by
      exact hbound'.trans_eq (by ring)
    _ ≤ C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+eps*(N+8))*Z^loss*
        ((∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg
        (Finset.prod_nonneg (fun j _=>Real.rpow_nonneg (hYp j).le _))
        (Finset.prod_nonneg (fun j _=>zero_le_one.trans (hp j))))
      exact mul_le_mul_of_nonneg_left (hheightZ i hi) (by unfold rowNorm;positivity)
    _ = _ := by rw [hprod]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CubeFixedPrimes
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots ProbeCentralAllSlots HeckePrimeAmplitudeBins
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_fixed_cube_prime_bound_oai (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (_hdRange : dmin≤dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(u : FreeRow),u.val≠1 → Z^δ≤ rowNorm u →
      (calibrationForSet S hmax).residueMonoid u.val≠0 → rowNorm u≤Z^(d-margin) →
      ∀(a : ℝ) (i : ℕ),i≤n → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<a+2*e →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      let x : ℂ := (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I)
      let w : ℂ := (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
      let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
      let Q : Fin N→ℂ := fun j=>HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) z
      let g : Fin N→ℝ := fun j=>amplitude (Y j) (a-1/2) mesh (Q j)
      (∀j,0≤g j ∧ g j≤a-1/2 ∧ g j∈labels (a-1/2) mesh ∧
        ‖Q j‖≤(Y j)^(g j+mesh) ∧ (0<g j → (Z^d)^(2*(ell j/d)*g j)≤‖Q j‖^2)) ∧
      ‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
          (fun j=>fixedPoolOutside M H S N c b Y j (P j).val (P j).property) W Y x w z‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+eps*(N+8))*Z^loss*
          (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh)) := by
  obtain ⟨C,hC,hbound⟩ := actual_cube_prime_bound M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax W hWs hW hWB
  have hdj := power_pools_eventually_disjoint (RayQuotient.identityClass M H) S
    (fun _ : Fin N=>c) (fun _=>b) ell (fun _=>hc) (fun _=>hcb) hell
  refine ⟨C,hC,?_⟩
  intro η
  filter_upwards [hbound η,hdj,eventually_ge_atTop (1:ℝ)] with Z hbound hdis hZ
  intro d hd hd' u hu hulo hcal huhi a i hi ha ha1 hbin
  dsimp only
  intro t ht
  have hd0 : 0<d := hdmin.trans_le hd
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hr (j : Fin N) : rmin≤ell j/d := by
    apply (le_div_iff₀ hd0).mpr
    exact (by nlinarith [mul_le_mul_of_nonneg_right hd' hrmin.le] : rmin*d≤dmax*rmin).trans (hello j)
  have hr' (j : Fin N) : ell j/d≤R := by
    apply (div_le_iff₀ hd0).mpr
    exact (hellhi j).trans (by nlinarith [mul_le_mul_of_nonneg_right hd hR])
  have heq (j : Fin N) : (Z^d)^(ell j/d)=Z^(ell j) := by
    rw [←Real.rpow_mul hZp.le,mul_div_cancel₀ _ hd0.ne']
  have hb := hbound d hd hd' u hu hulo hcal huhi a i hi ha ha1 hbin (fun j=>ell j/d) hr hr'
  have hfun : (fun j : Fin N => (Z^d)^(ell j/d)) = (fun j => Z^(ell j)) := funext heq
  rw [hfun] at hb
  exact hb hdis t ht

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.ProbeHighRowFamily.actual_fixed_cube_prime_bound_oai := @OAI.SevenEighths.ProbeHighRowFamily.actual_fixed_cube_prime_bound_oai
