-- Prove2me | solution 1 for OAI.SevenEighths.ProbeHighRowFamily.actual_source_batch
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:59:08.998759+00:00
-- url     : https://prove2.me/submissions/25fb666b-acfd-4f39-92af-cabea449d1e1

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027
import Theorems.Thm_OAI_SevenEighths_HeckeDetectorSupportedWitness_actual_supported_witness_family
import Theorems.Thm_OAI_SmoothMobiusCorrection_prime_norm_two_le

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Continuation
namespace OAI

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped Topology
namespace SevenEighths.Continuation

theorem product_identity_on_halfPlane (a b : ℝ) (L M W : ℂ → ℂ)
    (hL : AnalyticOnNhd ℂ L {s : ℂ | a < s.re})
    (hM : AnalyticOnNhd ℂ M {s : ℂ | a < s.re})
    (hW : AnalyticOnNhd ℂ W {s : ℂ | a < s.re})
    (heq : ∀ s : ℂ, max a b < s.re → L s * M s = W s) :
    Set.EqOn (fun s => L s * M s) W {s : ℂ | a < s.re} := by
  let z : ℂ := (max a b + 1 : ℝ)
  have hz : a < z.re := by dsimp [z]; linarith [le_max_left a b]
  have hz' : max a b < z.re := by dsimp [z]; simp
  have hev : (fun s => L s * M s) =ᶠ[𝓝 z] W := by
    filter_upwards [(Complex.isOpen_re_gt (max a b)).mem_nhds hz'] with s hs
    exact heq s hs
  exact (hL.mul hM).eqOn_of_preconnected_of_eventuallyEq hW
    (convex_halfSpace_re_gt a).isPreconnected hz hev

end SevenEighths.Continuation

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.NormFiberCharacters
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology

namespace ShortDraftHeckeBridge

private theorem orderOf_mod3_eq_one {p : ℕ} (h : p % 3 = 1) :
    orderOf (p : ZMod 3) = 1 := by
  have hc : (p : ZMod 3) = 1 :=
    (ZMod.natCast_eq_natCast_iff' p 1 3).2 (by simpa using h)
  simp [hc]

private theorem degree_two : Module.finrank ℚ K = 2 := by
  rw [IsCyclotomicExtension.Rat.finrank 3 K]
  decide

private theorem gal_card_two : Nat.card Gal(K/ℚ) = 2 := by
  rw [IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K]
  exact degree_two

theorem split_count_of_mod_one {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    ((Ideal.span {(p : ℤ)}).primesOver O).ncard = 2 := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hmain := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(p : ℤ)}) O Gal(K/ℚ)
  rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p K hnd,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
    orderOf_mod3_eq_one hmod, gal_card_two] at hmain
  omega

theorem absNorm_split {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1)
    (P : Ideal O) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.absNorm P = p := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hf : P.inertiaDeg ℤ = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P Gal(K/ℚ),
      IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
      orderOf_mod3_eq_one hmod]
  rw [← Ideal.pow_inertiaDeg p P, hf, pow_one]

end ShortDraftHeckeBridge

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.MobiusEulerCorrection
namespace OAI

noncomputable section

namespace SmoothMobiusCorrection

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical

section
open ActualEisensteinCubic
open IdealMobiusDivisorSum hiding O
open UniqueFactorizationMonoid
open CanonicalRowCompletion (primeValueHom primeValueHom_prime)

theorem primeProduct_ne_zero (s : Finset PrimeIdeal) : primeProduct s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _ => P.property.ne_zero)

theorem factors_primeProduct (s : Finset PrimeIdeal) :
    normalizedFactors (primeProduct s) = s.val.map Subtype.val := by
  have h := normalizedFactors_prod_of_prime
    (m := s.val.map (fun P : PrimeIdeal => P.val)) (by
      intro P hP
      obtain ⟨Q,hQ,rfl⟩ := Multiset.mem_map.mp hP
      exact Q.property)
  simpa only [primeProduct, Finset.prod_eq_multiset_prod] using h

theorem primeSet_primeProduct (s : Finset PrimeIdeal) : primeSet (primeProduct s) = s := by
  ext P
  rw [mem_primeSet]
  simp only [primeSupport, factors_primeProduct, Multiset.mem_toFinset,
    Multiset.mem_map, Finset.mem_val]
  constructor
  · rintro ⟨Q,hQ,he⟩
    have : Q=P := Subtype.ext he
    simpa [this] using hQ
  · intro h
    exact ⟨P,h,rfl⟩

theorem primeProduct_injective : Function.Injective primeProduct := by
  intro s t h
  simpa only [primeSet_primeProduct] using congrArg primeSet h

theorem primeProduct_squarefree (s : Finset PrimeIdeal) : Squarefree (primeProduct s) := by
  rw [squarefree_iff_nodup_normalizedFactors (primeProduct_ne_zero s),factors_primeProduct]
  exact s.nodup.map Subtype.val_injective

theorem primeProduct_primeSet (I : Ideal ActualEisensteinCubic.O) (hI : Squarefree I) :
    primeProduct (primeSet I) = I := by
  unfold primeProduct primeSet
  rw [Finset.prod_image]
  · change (∏ P ∈ (primeSupport I).attach, (fun Q : Ideal ActualEisensteinCubic.O => Q) P.val) = I
    exact (Finset.prod_attach (primeSupport I) (fun Q : Ideal ActualEisensteinCubic.O => Q)).trans
      (squarefree_support_product_self hI)
  · intro P hP Q hQ he
    exact Subtype.ext (congrArg (fun R : PrimeIdeal => R.val) he)

theorem mobiusPrimeCoeff_nonsquarefree (w : Ideal ActualEisensteinCubic.O → ℂ) (I : Ideal ActualEisensteinCubic.O)
    (hI : ¬Squarefree I) : mobiusPrimeCoeff w I=0 := by
  simp [mobiusPrimeCoeff,moebius_of_not_squarefree hI]

theorem mobiusPrimeCoeff_primeProduct (w : Ideal ActualEisensteinCubic.O → ℂ) (s : Finset PrimeIdeal) :
    mobiusPrimeCoeff w (primeProduct s) = ∏ P ∈ s, -w P.val := by
  have hm : (moebius (primeProduct s) : ℂ)=(-1:ℂ)^s.card := by
    rw [(primeProduct_squarefree s).moebius_eq,factors_eq_normalizedFactors,
      factors_primeProduct]
    simp
  rw [mobiusPrimeCoeff,hm]
  simp only [primeProduct,map_prod,primeValueHom_prime _ _ (Subtype.property _)]
  rw [Finset.prod_neg]

theorem mobiusPrimeCoeff_tsum (w : Ideal ActualEisensteinCubic.O → ℂ) :
    (∑' I : Ideal ActualEisensteinCubic.O, mobiusPrimeCoeff w I) =
      ∑' s : Finset PrimeIdeal, ∏ P ∈ s, -w P.val := by
  apply tsum_eq_tsum_of_ne_zero_bij (fun s => primeProduct s.val)
  · exact primeProduct_injective.comp Subtype.val_injective
  · intro I hI
    have hs : Squarefree I := by
      by_contra hs
      exact hI (mobiusPrimeCoeff_nonsquarefree w I hs)
    have hp : (∏ P ∈ primeSet I, -w P.val) ≠ 0 := by
      rw [←mobiusPrimeCoeff_primeProduct,primeProduct_primeSet I hs]
      exact hI
    exact ⟨⟨primeSet I,hp⟩,primeProduct_primeSet I hs⟩
  · intro s
    exact mobiusPrimeCoeff_primeProduct w s.val

theorem mobiusPrimeCoeff_euler (w : Ideal ActualEisensteinCubic.O → ℂ)
    (hw : Summable (fun P : PrimeIdeal => ‖w P.val‖)) :
    (∑' I : Ideal ActualEisensteinCubic.O, mobiusPrimeCoeff w I) =
      ∏' P : PrimeIdeal, (1-w P.val) := by
  rw [mobiusPrimeCoeff_tsum]
  have hs : Summable (fun P : PrimeIdeal => ‖-w P.val‖) := by simpa using hw
  simpa only [sub_eq_add_neg] using
    (tprod_one_add (summable_finsetProd_of_summable_norm hs)).symm

end

section
open ActualEisensteinCubic
open Filter

lemma prime_norm_pos (P : PrimeIdeal) : (0 : ℝ) < Ideal.absNorm P.val := by
  have h := prime_norm_two_le P
  exact_mod_cast (by omega : 0 < Ideal.absNorm P.val)

lemma norm_primeNormPower (P : PrimeIdeal) (s : ℂ) :
    ‖primeNormPower P s‖=(Ideal.absNorm P.val : ℝ)^(-s.re) := by
  exact Complex.norm_cpow_eq_rpow_re_of_pos (prime_norm_pos P) (-s)

lemma one_sub_ne_zero {x : ℂ} (hx : ‖x‖<1) : 1-x≠0 := by
  intro h
  have he : x=1 := (sub_eq_zero.mp h).symm
  simp [he] at hx

end

open ActualEisensteinCubic

open scoped BigOperators Classical
open ActualEisensteinCubic
open ShortDraftHeckeBridge hiding O

end SmoothMobiusCorrection

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Theta
namespace OAI

noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology BigOperators
namespace SevenEighths.HeckeTheta
open EisensteinTheta

theorem regularizedCompleted_differentiableAt {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (regularizedCompleted w) s := by
  exact (((differentiableAt_id.sub_const 1).mul
    (((pair w).differentiable_Λ₀ s).sub
      ((differentiableAt_id.inv hs₀).mul_const (pair w).f₀))).add_const (pair w).g₀)

theorem regularizedCompleted_eq {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    regularizedCompleted w s = (s - 1) * completed w s := by
  unfold regularizedCompleted completed WeakFEPair.Λ
  simp only [pair_k, Complex.ofReal_one, show (pair w).ε = 1 from rfl,
    smul_eq_mul, one_div]
  have hsub : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs₁.symm
  field_simp
  ring

theorem regularizedLatticeL_differentiableAt {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (regularizedLatticeL w) s := by
  exact (((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).differentiableAt).mul
      (Complex.differentiable_one_div_Gamma s)).mul
        (regularizedCompleted_differentiableAt w hs₀)

theorem regularizedLatticeL_eq {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    regularizedLatticeL w s = (s - 1) * latticeL w s := by
  unfold regularizedLatticeL latticeL
  rw [regularizedCompleted_eq w hs₀ hs₁]
  ring

end SevenEighths.HeckeTheta

end

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

local instance instInfiniteRingOfIntegers_solutions_rf23f44_1 : Infinite (𝓞 K) := Module.Free.infinite ℤ (𝓞 K)
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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.IdealEuler
namespace OAI

namespace SevenEighths.IdealEuler

open ActualEisensteinCubic UniqueFactorizationMonoid
open CompletedGauss (MulFiber mulFiber_moebius_sum)
open SmoothMobiusCorrection (PrimeIdeal)
open scoped BigOperators Classical

noncomputable section

theorem inverseSeries_eq_inv (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : inverseSeries a s = (series a s)⁻¹ := by
  calc
    _ = (inverseSeries a s * series a s) * (series a s)⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ (series_ne_zero a ha s hs), mul_one]
    _ = _ := by rw [inverseSeries_mul_series a ha s hs, one_mul]

theorem prime_summable_norm (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : Summable (fun P : PrimeIdeal => ‖weighted a s P.val‖) :=
  (weighted_summable_norm a ha s hs).comp_injective Subtype.val_injective

theorem prime_norm_lt_one (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 0 < s.re) (P : PrimeIdeal) : ‖weighted a s P.val‖ < 1 := by
  change ‖a P.val * CubicEisenstein.fullIdealWeight s P.val‖ < 1
  simp only [CubicEisenstein.fullIdealWeight, P.property.ne_zero, ite_false, norm_mul]
  change ‖a P.val‖ * ‖SmoothMobiusCorrection.primeNormPower P s‖ < 1
  rw [SmoothMobiusCorrection.norm_primeNormPower]
  apply (mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _) (ha P.val)).trans_lt
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by have h := SmoothMobiusCorrection.prime_norm_two_le P
        exact_mod_cast (by omega : 1 < Ideal.absNorm P.val)) (by simpa using neg_neg_of_pos hs)

theorem local_factor_ne_zero (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 0 < s.re) (P : PrimeIdeal) : 1 - weighted a s P.val ≠ 0 :=
  SmoothMobiusCorrection.one_sub_ne_zero (prime_norm_lt_one a ha s hs P)

theorem inverseSeries_euler (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    inverseSeries a s = ∏' P : PrimeIdeal, (1 - weighted a s P.val) := by
  have h := SmoothMobiusCorrection.mobiusPrimeCoeff_euler (weighted a s)
    (prime_summable_norm a ha s hs)
  simpa only [SmoothMobiusCorrection.mobiusPrimeCoeff, primeValueHom_eq, inverseSeries] using h

theorem euler_hasProd (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun P : PrimeIdeal => (1 - weighted a s P.val)⁻¹) (series a s) := by
  have hm : Multipliable (fun P : PrimeIdeal => 1 - weighted a s P.val) := by
    simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable
      (show Summable (fun P : PrimeIdeal => ‖-weighted a s P.val‖) by
        simpa only [norm_neg] using prime_summable_norm a ha s hs)
  have heq : (∏' P : PrimeIdeal, (1 - weighted a s P.val)) = (series a s)⁻¹ :=
    (inverseSeries_euler a ha s hs).symm.trans (inverseSeries_eq_inv a ha s hs)
  have hne : (∏' P : PrimeIdeal, (1 - weighted a s P.val)) ≠ 0 := by
    rw [heq]
    exact inv_ne_zero (series_ne_zero a ha s hs)
  simpa only [heq, inv_inv] using hm.hasProd.inv₀ hne

theorem series_euler (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    series a s = ∏' P : PrimeIdeal, (1 - weighted a s P.val)⁻¹ :=
  (euler_hasProd a ha s hs).tprod_eq.symm

theorem deletePrimes_prime (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ) (P : PrimeIdeal) :
    deletePrimes S a P.val = if P ∈ S then 0 else a P.val := by
  have hmem : P.val ∈ S.image Subtype.val ↔ P ∈ S := by
    constructor
    · intro hP
      obtain ⟨Q, hQ, hQP⟩ := Finset.mem_image.mp hP
      exact (Subtype.ext hQP : Q = P) ▸ hQ
    · intro hP
      exact Finset.mem_image.mpr ⟨P, hP, rfl⟩
  change CanonicalRowCompletion.primeValueHom _ P.val = _
  rw [CanonicalRowCompletion.primeValueHom_prime _ _ P.property]
  simp only [hmem]

theorem deletePrimes_norm_le_one (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) : ∀ I, ‖deletePrimes S a I‖ ≤ 1 := by
  apply CanonicalRowCompletion.primeValueHom_norm_le_one
  intro I
  split_ifs
  · simp only [norm_zero, zero_le_one]
  · exact ha I

theorem deletePrimes_apply (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ) (I : Ideal O) :
    deletePrimes S a I = if ∀ P ∈ S, ¬P.val ∣ I then a I else 0 := by
  by_cases ho : ∀ P ∈ S, ¬P.val ∣ I
  · rw [if_pos ho]
    by_cases hI : I = 0
    · subst I
      rw [map_zero, map_zero]
    · change (if I = 0 then 0 else
        ((normalizedFactors I).map (fun J => if J ∈ S.image Subtype.val then 0 else a J)).prod) = a I
      simp only [hI, ite_false]
      have hmap : (normalizedFactors I).map (fun J => if J ∈ S.image Subtype.val then 0 else a J) =
          (normalizedFactors I).map a := by
        apply Multiset.map_congr rfl
        intro J hJ
        have hnot : J ∉ S.image Subtype.val := by
          intro hmem
          obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hmem
          exact ho P hP (dvd_of_mem_normalizedFactors hJ)
        simp only [hnot, ite_false]
      rw [hmap, ← map_multiset_prod, prod_normalizedFactors_eq hI, normalize_eq]
  · simp only [ho, ite_false]
    push Not at ho
    obtain ⟨P, hPS, J, hJ⟩ := ho
    rw [hJ, map_mul, deletePrimes_prime]
    simp only [hPS, ite_true, zero_mul]

theorem deletePrimes_primeSet_apply (M : Ideal O) (hM : M ≠ 0)
    (a : Ideal O →*₀ ℂ) (I : Ideal O) :
    deletePrimes (SmoothMobiusCorrection.primeSet M) a I =
      if IsCoprime I M then a I else 0 := by
  by_cases hI : I = 0
  · subst I
    rw [map_zero, map_zero]
    exact (ite_self _).symm
  have heq : (∀ P ∈ SmoothMobiusCorrection.primeSet M, ¬P.val ∣ I) ↔ IsCoprime I M := by
    rw [← IdealCoprimeSieveOperator.primeSupport_disjoint_iff hI hM]
    constructor
    · intro h
      apply Finset.disjoint_left.mpr
      intro P hPI hPM
      have hp : Prime P := IdealMobiusDivisorSum.support_prime hPM
      exact h ⟨P, hp⟩ (SmoothMobiusCorrection.mem_primeSet M ⟨P, hp⟩ |>.mpr hPM)
        (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hPI))
    · intro h P hPM hPI
      exact Finset.disjoint_left.mp h
        (Multiset.mem_toFinset.mpr ((mem_normalizedFactors_iff hI).mpr ⟨P.property, hPI⟩))
        ((SmoothMobiusCorrection.mem_primeSet M P).mp hPM)
  simpa only [heq] using deletePrimes_apply (SmoothMobiusCorrection.primeSet M) a I

theorem series_deletePrimes (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    series (deletePrimes S a) s =
      series a s * ∏ P ∈ S, (1 - weighted a s P.val) := by
  have hlocal (P : PrimeIdeal) :
      (1 - weighted (deletePrimes S a) s P.val)⁻¹ =
        (1 - weighted a s P.val)⁻¹ * (if P ∈ S then 1 - weighted a s P.val else 1) := by
    change (1 - deletePrimes S a P.val * normWeight s P.val)⁻¹ = _
    rw [deletePrimes_prime]
    by_cases hP : P ∈ S
    · simp only [hP, ite_true, zero_mul, sub_zero, inv_one]
      exact (inv_mul_cancel₀ (local_factor_ne_zero a ha s (by linarith) P)).symm
    · simp only [hP, ite_false, mul_one]
      rfl
  have hfinite : Multipliable (fun P : PrimeIdeal => if P ∈ S then 1 - weighted a s P.val else 1) := by
    apply multipliable_of_hasFiniteMulSupport
    apply S.finite_toSet.subset
    intro P hP
    by_contra hPS
    change P ∉ S at hPS
    exact hP (by simp only [hPS, ite_false])
  rw [series_euler _ (deletePrimes_norm_le_one S a ha) s hs,
    series_euler a ha s hs]
  simp_rw [hlocal]
  rw [(euler_hasProd a ha s hs).multipliable.tprod_mul hfinite]
  congr 1
  rw [tprod_eq_prod (s := S) (fun P hP => by simp only [hP, ite_false])]
  exact Finset.prod_congr rfl (fun P hP => by simp only [hP, ite_true])

theorem series_of_coprime_mask (M : Ideal O) (hM : M ≠ 0)
    (a b : Ideal O →*₀ ℂ) (hb : ∀ I, ‖b I‖ ≤ 1)
    (hmask : ∀ I, a I = if IsCoprime I M then b I else 0)
    (s : ℂ) (hs : 1 < s.re) :
    series a s = series b s *
      ∏ P ∈ SmoothMobiusCorrection.primeSet M, (1 - weighted b s P.val) := by
  have heq : a = deletePrimes (SmoothMobiusCorrection.primeSet M) b := by
    ext I
    rw [deletePrimes_primeSet_apply M hM, hmask]
  rw [heq]
  exact series_deletePrimes _ b hb s hs

end

end SevenEighths.IdealEuler

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighExcludedLocal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma highExclusion_prime (S : Finset Id) (hS : ∀P∈S,Prime P) (P : PrimeIdeal) :
    highExclusion S hS P.val=if P.val∈S then 0 else 1 := by
  change (if ∀Q∈S,¬Q∣P.val then (1:ℂ) else 0)=_
  by_cases hP : P.val∈S
  · rw [if_neg (fun h=>h P.val hP (dvd_refl _)),if_pos hP]
  · have houtside : ∀Q∈S,¬Q∣P.val := by
      intro Q hQ hd
      have hn : (⟨Q,hS Q hQ⟩ : PrimeIdeal)≠P := by
        intro hh
        exact hP ((congrArg Subtype.val hh) ▸ hQ)
      exact (hS Q hQ).not_isUnit ((primeIdeal_coprime ⟨Q,hS Q hQ⟩ P hn).isUnit_of_dvd hd)
    rw [if_pos houtside,if_neg hP]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.EulerFactors
namespace OAI

namespace SevenEighths.EulerFactors

noncomputable section

theorem norm_term_lt_one {N : ℝ} (hN : 1 < N) {a s : ℂ}
    (ha : ‖a‖ ≤ 1) (hs : 0 < s.re) : ‖a * (N : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < N),
    Complex.neg_re]
  calc
    ‖a‖ * N ^ (-s.re) ≤ 1 * N ^ (-s.re) :=
      mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg (by linarith) _)
    _ < 1 := by simpa using Real.rpow_lt_one_of_one_lt_of_neg hN (neg_neg_of_pos hs)

theorem factor_ne_zero {N : ℝ} (hN : 1 < N) {a s : ℂ}
    (ha : ‖a‖ ≤ 1) (hs : 0 < s.re) : factor N a s ≠ 0 := by
  intro h
  have heq : a * (N : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have hlt := norm_term_lt_one hN ha hs
  rw [heq, norm_one] at hlt
  exact (lt_irrefl _ hlt)

theorem differentiable_factor {N : ℝ} (hN : 0 < N) (a : ℂ) :
    Differentiable ℂ (factor N a) := by
  exact (differentiable_const (1 : ℂ)).sub ((differentiable_const a).mul
    (differentiable_id.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hN.ne'))))

theorem deletedProduct_ne_zero {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 1 < N p) (ha : ∀ p ∈ S, ‖a p‖ ≤ 1)
    {s : ℂ} (hs : 0 < s.re) : deletedProduct S N a s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact factor_ne_zero (hN p hp) (ha p hp) hs

theorem differentiable_deletedProduct {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 0 < N p) :
    Differentiable ℂ (deletedProduct S N a) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    change Differentiable ℂ (fun _ : ℂ => (1 : ℂ))
    exact differentiable_const _
  | @insert p S hp ih =>
    have hpN := hN p (Finset.mem_insert_self p S)
    have hSN : ∀ q ∈ S, 0 < N q := fun q hq => hN q (Finset.mem_insert_of_mem hq)
    have heq : deletedProduct (insert p S) N a =
        fun s => factor (N p) (a p) s * deletedProduct S N a s := by
      funext s
      simp only [deletedProduct, Finset.prod_insert hp]
    rw [heq]
    exact (differentiable_factor hpN (a p)).mul (ih hSN)

end

end SevenEighths.EulerFactors

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Reciprocal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeReciprocal
open HeckeFamily HeckeCharacterAnalytic HeckeCoordinates

theorem regularizedL_eq (χ : Character) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    regularizedL χ s = (s - 1) * LFunction χ s := by
  unfold regularizedL LFunction continuedLattice
  rw [HeckeTheta.regularizedLatticeL_eq _ h0 h1]
  ring

theorem regularizedL_differentiableAt (χ : Character) {s : ℂ} (h0 : s ≠ 0) :
    DifferentiableAt ℂ (regularizedL χ) s :=
  (HeckeTheta.regularizedLatticeL_differentiableAt _ h0).div_const 6

end SevenEighths.HeckeReciprocal

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeFiniteDeletion
open HeckeFamily HeckeReciprocal

theorem factors_eq (M : Ideal O) (ψ : Character) (s : ℂ) :
    factors M ψ s = ∏ P ∈ SmoothMobiusCorrection.primeSet M,
      (1 - IdealEuler.weighted (idealCoeff ψ) s P.val) := by
  apply Finset.prod_congr rfl
  intro P _
  simp only [EulerFactors.factor, IdealEuler.weighted, MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk, IdealEuler.normWeight, CubicEisenstein.fullIdealWeight,
    P.property.ne_zero, ite_false, Complex.ofReal_natCast]

theorem factors_differentiable (M : Ideal O) (ψ : Character) :
    Differentiable ℂ (factors M ψ) := by
  apply EulerFactors.differentiable_deletedProduct
  intro P _
  have h := SmoothMobiusCorrection.prime_norm_two_le P
  exact_mod_cast (by omega : 0 < Ideal.absNorm P.val)

theorem factors_ne_zero (M : Ideal O) (ψ : Character) {s : ℂ} (hs : 0 < s.re) :
    factors M ψ s ≠ 0 := by
  apply EulerFactors.deletedProduct_ne_zero _ _ _ _ _ hs
  · intro P _
    have h := SmoothMobiusCorrection.prime_norm_two_le P
    exact_mod_cast (by omega : 1 < Ideal.absNorm P.val)
  · intro P _
    exact idealCoeff_norm_le_one ψ P.val

theorem LFunction_eq_of_mask_right (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = LFunction ψ s * factors χ.modulus ψ s := by
  rw [LFunction_eq_series χ hs, LFunction_eq_series ψ hs, factors_eq]
  exact IdealEuler.series_of_coprime_mask χ.modulus χ.modulus_ne_bot
    _ _ (idealCoeff_norm_le_one ψ) hmask s hs

theorem regularizedL_analytic (χ : Character) :
    AnalyticOnNhd ℂ (regularizedL χ) {s : ℂ | 0 < s.re} := by
  apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
  intro s hs
  exact (regularizedL_differentiableAt χ (by intro h; simp [h] at hs)).differentiableWithinAt

theorem regularizedL_eq_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0 < s.re) :
    regularizedL χ s = regularizedL ψ s * factors χ.modulus ψ s := by
  have hf : AnalyticOnNhd ℂ (factors χ.modulus ψ) {z : ℂ | 0 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
    exact (factors_differentiable _ _).differentiableOn
  apply Eq.symm
  apply Continuation.product_identity_on_halfPlane 0 1
    (regularizedL ψ) (factors χ.modulus ψ) (regularizedL χ)
    (regularizedL_analytic ψ) hf (regularizedL_analytic χ) _ hs
  intro z hz
  have hz' : 1 < z.re := by simpa using hz
  have h0 : z ≠ 0 := by intro h; norm_num [h] at hz'
  have h1 : z ≠ 1 := by intro h; norm_num [h] at hz'
  rw [regularizedL_eq χ h0 h1, regularizedL_eq ψ h0 h1,
    LFunction_eq_of_mask_right χ ψ hmask hz']
  ring

theorem regularizedL_one_ne_zero_iff (χ : Character) :
    regularizedL χ 1 ≠ 0 ↔ χ.residue = 1 := by
  constructor
  · intro h
    by_contra hχ
    rw [regularizedL_at_one,
      HeckeTheta.pair_g₀_eq_zero _ (HeckeCharacterAnalytic.coefficients_sum_eq_zero χ hχ),
      mul_zero, zero_div] at h
    exact h rfl
  · exact regularizedL_ne_zero_at_one χ

theorem principal_iff_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0) :
    χ.residue = 1 ↔ ψ.residue = 1 := by
  rw [← regularizedL_one_ne_zero_iff χ, ← regularizedL_one_ne_zero_iff ψ,
    regularizedL_eq_of_mask χ ψ hmask (by norm_num : 0 < (1 : ℂ).re),
    mul_ne_zero_iff, and_iff_left (factors_ne_zero χ.modulus ψ (by norm_num))]

end SevenEighths.HeckeFiniteDeletion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.ModulusRefinement
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeFamily

attribute [local instance] OAI.SevenEighths.HeckeFamily.instIsPrincipalIdealRingO_solutions
theorem excludePrimes_mask (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (I : Ideal O) :
    idealCoeff (η.excludePrimes S hS) I =
      if IsCoprime I (η.excludePrimes S hS).modulus then idealCoeff η I else 0 :=
  idealCoeff_refineModulus η _ _ _ I

end SevenEighths.HeckeFamily

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.Character
namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeRowClosure CanonicalRowCompletion
open CanonicalQuadraticSieve ProbePhysical
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem rowCharacter_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (u : FreeRow) (I : Ideal O) :
    idealCoeff (rowCharacter S hS u) I=highExclusion S hS I*idealRowHom u.val I := by
  have he : idealCoeff (rowCharacter S hS u)=sourceRowCoeff S hS u := by
    apply hom_eq_of_primes
    intro P
    change idealCoeff ((rawRow u).excludePrimes S hS) P.val=
      highExclusion S hS P.val*idealRowHom u.val P.val
    rw [excludedTarget_prime,highExclusion_prime]
    by_cases hP : P.val∈S
    · simp only [if_pos hP,zero_mul]
    · simp only [if_neg hP,one_mul]
      exact rawRow_prime_outside S hS hbad u P hP
  exact congrArg (fun F : Ideal O→*₀ℂ => F I) he

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.UnitSexticWitness
namespace OAI

namespace SevenEighths.UnitSexticWitness

open ActualEisensteinCubic CanonicalRowCompletion CanonicalUnitEuler
open ConcreteTraceCRT
open scoped Classical
noncomputable section
local notation "lambda" => ConcretePrimeRowBridge.goodLambda

lemma idealRowHom_unit_eq_of_norm_mod_seven (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (hodd : ringChar (O ⧸ P) ≠ 2)
    (hmod : Ideal.absNorm P % 36 = 7) (u : Oˣ) :
    idealRowHom u.val P = eisEmbedding u.val := by
  rw [idealRowHom_prime _ P hg, actualSextic_unit_euler P hg hodd]
  have hcard : Nat.card (O ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hcard]
  have hm : (Ideal.absNorm P - 1) / 6 ≡ 1 [MOD 6] := by
    dsimp [Nat.ModEq]
    omega
  have he := pow_eq_pow_of_modEq hm (unit_pow_six u)
  simpa only [pow_one] using congrArg eisEmbedding he

lemma prime_norm_good {p : ℕ} (_hp : p.Prime) (hp3 : 3 < p)
    (P : Ideal O) (hP : Ideal.absNorm P = p) : lambda ∉ P := by
  intro hl
  have hd := Ideal.absNorm_dvd_absNorm_of_le
    ((Ideal.span_singleton_le_iff_mem P).mpr hl)
  have hlambda : Ideal.absNorm (Ideal.span {lambda}) = 3 := CubicEisenstein.absNorm_span_lambda
  rw [hP, hlambda] at hd
  have := Nat.le_of_dvd (by decide : 0 < 3) hd
  omega

lemma prime_norm_ringChar {p : ℕ} (hp : p.Prime)
    (P : Ideal O) [P.IsMaximal] (hP : Ideal.absNorm P = p) :
    ringChar (O ⧸ P) = p := by
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let : Fact p.Prime := ⟨hp⟩
  have hcard : Fintype.card (O ⧸ P) = p := by
    rw [← Nat.card_eq_fintype_card]
    exact hP
  let : CharP (O ⧸ P) p := charP_of_card_eq_prime hcard
  exact ringChar.eq (O ⧸ P) p

lemma exists_primeIdeal_norm {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    ∃ P : Ideal O, P.IsMaximal ∧ Ideal.absNorm P = p := by
  have hc := ShortDraftHeckeBridge.split_count_of_mod_one hp hmod
  have hne : ((Ideal.span {(p : ℤ)}).primesOver O).Nonempty := by
    exact Set.nonempty_of_ncard_ne_zero (by rw [hc]; decide)
  obtain ⟨P, hP⟩ := hne
  let : P.IsPrime := hP.1
  let : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
  have hn := ShortDraftHeckeBridge.absNorm_split hp hmod P
  have hP0 : P ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hn
    exact hp.ne_zero hn.symm
  exact ⟨P, hP.1.isMaximal hP0, hn⟩

theorem exists_prime_unit_embedding (S : Finset (Ideal O)) (B : ℕ) :
    ∃ P : Ideal O, P.IsMaximal ∧ P ∉ S ∧ B < Ideal.absNorm P ∧
      Ideal.absNorm P % 36 = 7 ∧ lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2 ∧
      ∀ u : Oˣ, idealRowHom u.val P = eisEmbedding u.val := by
  obtain ⟨p, hpB, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq
    (max (max B 3) (S.sup Ideal.absNorm)) (q := 36) (a := 7) (by decide) (by decide)
  have hp36 : p % 36 = 7 := by simpa only [Nat.ModEq, Nat.reduceMod] using hmod
  have hp3 : 3 < p := lt_of_le_of_lt ((le_max_right B 3).trans (le_max_left _ _)) hpB
  have hpmod : p % 3 = 1 := by omega
  obtain ⟨P, hmax, hn⟩ := exists_primeIdeal_norm hp hpmod
  let : P.IsMaximal := hmax
  have hg : lambda ∉ P := prime_norm_good hp hp3 P hn
  have hodd : ringChar (O ⧸ P) ≠ 2 := by
    rw [prime_norm_ringChar hp P hn]
    omega
  refine ⟨P, hmax, ?_, ?_, hn ▸ hp36, hg, hodd, ?_⟩
  · intro hPS
    have hle := Finset.le_sup (f := Ideal.absNorm) hPS
    rw [hn] at hle
    have := le_max_right (max B 3) (S.sup Ideal.absNorm)
    omega
  · rw [hn]
    exact lt_of_le_of_lt ((le_max_left B 3).trans (le_max_left _ _)) hpB
  · exact idealRowHom_unit_eq_of_norm_mod_seven P hg hodd (hn ▸ hp36)

theorem exists_unit_witness (u : Oˣ) (hu : u ≠ 1)
    (S : Finset (Ideal O)) (B : ℕ) :
    ∃ P : Ideal O, P.IsMaximal ∧ P ∉ S ∧ B < Ideal.absNorm P ∧
      lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2 ∧
      idealRowHom u.val P ≠ 0 ∧ idealRowHom u.val P ≠ 1 := by
  obtain ⟨P, hp, hs, hb, hm, hg, ho, he⟩ := exists_prime_unit_embedding S B
  refine ⟨P, hp, hs, hb, hg, ho, ?_, ?_⟩
  · rw [he u]
    intro hz
    exact Units.ne_zero u (eisEmbedding_injective (by simpa using hz))
  · rw [he u]
    intro hh
    apply hu
    apply Units.ext
    exact eisEmbedding_injective (by simpa using hh)

end
end SevenEighths.UnitSexticWitness

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

lemma rowCharacter_principal_iff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow) :
    (rowCharacter S hS u).residue=1 ↔ (rawRow u).residue=1 :=
  HeckeFiniteDeletion.principal_iff_of_mask _ _ (excludePrimes_mask (rawRow u) S hS)

lemma supported_coprime_row_fixed (r : O) (hr : Supported (Ideal.span {r})) :
    IsCoprime (Ideal.span {r})
      ((fixedSourcePrincipal ∅ (by simp)).modulus*Ideal.span {rowMaskElement}*
        Ideal.span {(72:O)}) := by
  have hl : IsCoprime λ₀ r :=
    PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr
      ((supported_span_iff r).mp hr).1
  have hn : IsCoprime (-2:O) r := negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using ((supported_span_iff r).mp hr).2)
  have h2 : IsCoprime (2:O) r := hn.of_isCoprime_of_dvd_left ⟨-1,by ring⟩
  have h9 : IsCoprime (9:O) r := ShortDraftCRT.nine_coprime_of_not_lambda_dvd r
    ((supported_span_iff r).mp hr).1
  have h72 : IsCoprime (72:O) r := by
    convert (preTransparency := .instances) (h2.pow_left (m:=3)).mul_left h9 using 1; norm_num
  have hm := (h2.mul_left hl).symm
  have hmod : (fixedSourcePrincipal ∅ (by simp)).modulus=(1:Ideal O) := by
    simp [fixedSourcePrincipal,HeckeRayFamily.character,Character.ofResidue]
  rw [hmod,one_mul]
  exact ((Ideal.isCoprime_span_singleton_iff _ _).mpr hm).mul_right
    ((Ideal.isCoprime_span_singleton_iff _ _).mpr h72.symm)

theorem rawRow_principal_supported_isUnit (u : FreeRow)
    (hu : Supported (Ideal.span {u.val})) (hp : (rawRow u).residue=1) : IsUnit u.val := by
  obtain ⟨v,hv⟩ := exists_supported_primary_unit u.val hu
  let r : O := (v:O)*u.val
  have hspan : (Ideal.span {r}:Ideal O)=Ideal.span {u.val} :=
    Ideal.span_singleton_mul_left_unit v.isUnit u.val
  have hr : Supported (Ideal.span {r}) := hspan.symm ▸ hu
  have hx : (1:O)^4*u.val=(v⁻¹:Oˣ).val*λ₀^0*(2:O)^0*r := by
    simp [r]
  have hempty : normalizedFactors (Ideal.span {r})=0 := by
    apply Multiset.eq_zero_iff_forall_notMem.mpr
    intro P hP
    have hcop : IsCoprime
        ((fixedSourcePrincipal ∅ (by simp)).modulus*Ideal.span {rowMaskElement}*Ideal.span {(72:O)}) P :=
      (supported_coprime_row_fixed r hr).symm.of_isCoprime_of_dvd_right (dvd_of_mem_normalizedFactors hP)
    have hd := HeckeRowNonprincipal.principal_row_multiplicity
      (fixedSourcePrincipal ∅ (by simp)) (rawRow u) rowMaskElement 1 u.val
      (dvd_mul_left _ _) (dvd_mul_right _ _) v⁻¹ 0 0 r hr hv hx (rawRow_elementCoeff u) hp P hP hcop
    have hlt : (normalizedFactors (Ideal.span {r})).count P<6 := by
      rw [hspan]
      exact u.property.2 P
    exact Nat.not_dvd_of_pos_of_lt (Multiset.count_pos.mpr hP) hlt hd
  have hone : (Ideal.span {u.val}:Ideal O)=1 := by
    rw [←hspan,←Ideal.prod_normalizedFactors_eq_self hr.1,hempty,Multiset.prod_zero]
  exact Ideal.span_singleton_eq_top.mp (by simpa only [Ideal.one_eq_top] using hone)

lemma idealCoeff_principal_eq_one (χ : Character) (hχ : χ.residue=1)
    (I : Ideal O) (hI : idealCoeff χ I≠0) : idealCoeff χ I=1 := by
  change IdealCharacter.value χ.modulus χ.residue I=1
  change IdealCharacter.value χ.modulus χ.residue I≠0 at hI
  unfold IdealCharacter.value at *
  split_ifs at * with hzero
  · exact False.elim (hI rfl)
  · have hu := MulChar.apply_ne_zero_iff.mp hI
    rw [hχ,MulChar.one_apply hu]

theorem rowCharacter_unit_nonprincipal (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (u : FreeRow)
    (v : Oˣ) (hu : u.val=(v:O)) (hv : v≠1) :
    (rowCharacter S hS u).residue≠1 := by
  obtain ⟨P,hmax,hPS,hN,hg,hodd,hval0,hval1⟩ := UnitSexticWitness.exists_unit_witness v hv S 0
  let : P.IsMaximal := hmax
  have hP0 : P≠0 := by
    intro he
    simp [he] at hN
  let Q : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := ⟨P,Ideal.prime_of_isPrime hP0 hmax.isPrime⟩
  have he : idealCoeff (rowCharacter S hS u) P=idealRowHom (v:O) P := by
    rw [rowCharacter_coeff S hS hbad,highExclusion_prime S hS Q,if_neg hPS,one_mul,hu]
  intro hp
  have hv0 : idealCoeff (rowCharacter S hS u) P≠0 := he ▸ hval0
  exact hval1 (he.symm.trans (idealCoeff_principal_eq_one _ hp P hv0))

theorem rowCharacter_principal_supported_eq_one (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (u : FreeRow)
    (hu : Supported (Ideal.span {u.val})) (hp : (rowCharacter S hS u).residue=1) : u.val=1 := by
  obtain ⟨v,hv⟩ := rawRow_principal_supported_isUnit u hu ((rowCharacter_principal_iff S hS u).mp hp)
  by_contra hn
  have hv1 : v≠1 := by
    intro he
    subst v
    exact hn hv.symm
  exact rowCharacter_unit_nonprincipal S hS hbad u v hv.symm hv1 hp

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

theorem calibrated_row_nonprincipal (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hmax : ∀P∈S,P.IsMaximal) (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (u : FreeRow) (hu : u.val≠1)
    (hcal : (calibrationForSet S hmax).residueMonoid u.val≠0) :
    (rowCharacter S hS u).residue≠1 := fun hp=>hu
      (rowCharacter_principal_supported_eq_one S hS hbad u
        (calibration_nonzero_supported S hmax hbad u.val hcal) hp)

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

theorem rowCharacter_conductor (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow) :
    (rowCharacter S hS u).modulus.absNorm≤
      conductorConstant*(Ideal.span {u.val}:Ideal O).absNorm*(∏P∈S,P).absNorm := by
  change ((rawRow u).modulus*(∏P∈S,P)).absNorm≤_
  rw [map_mul]
  exact Nat.mul_le_mul_right _ (rawRow_conductor u)

theorem targetRow_conductor (η : Character) (u : FreeRow) :
    (targetRow η u).modulus.absNorm≤η.modulus.absNorm*conductorConstant*(Ideal.span {u.val}:Ideal O).absNorm := by
  let : Finite (O ⧸ η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Finite (O ⧸ (rawRow u).modulus) := Ring.HasFiniteQuotients.finiteQuotient (rawRow u).modulus_ne_bot
  change (η.modulus⊓(rawRow u).modulus).absNorm≤_
  calc
    _ ≤ η.modulus.absNorm*(rawRow u).modulus.absNorm :=
      FiniteConductor.absNorm_inf_le_mul _ _
    _ ≤ _ := by simpa only [mul_assoc] using Nat.mul_le_mul_left η.modulus.absNorm (rawRow_conductor u)

theorem targetRow_excluded_conductor (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) :
    ((targetRow η u).excludePrimes S hS).modulus.absNorm≤
      η.modulus.absNorm*conductorConstant*(Ideal.span {u.val}:Ideal O).absNorm*(∏P∈S,P).absNorm := by
  change ((targetRow η u).modulus*(∏P∈S,P)).absNorm≤_
  rw [map_mul]
  exact Nat.mul_le_mul_right _ (targetRow_conductor η u)

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

end SevenEighths.ProbeRayCharacterFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.DetectorBatch
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch HeckeDetectorSupportedWitness ProbePhysical
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.ProbeHighRowFamily.instFiniteQuotientOIdeal_solutions_2
lemma physical_slot_widths {N : ℕ} (ell : Fin N→ℝ) (d dmin mesh : ℝ)
    (hdmin : 0<dmin) (hd : dmin≤d) (hdtop : d≤37/42)
    (hell : ∀j,0<ell j) (hsmall : ∀j,ell j≤dmin*mesh)
    (hsum : ∑j,ell j=1/6) :
    (∀j,0<ell j/d) ∧ (∀j,ell j/d≤ mesh) ∧ 7/37≤∑j,ell j/d := by
  have hd0 : 0<d := hdmin.trans_le hd
  have hm : 0≤ mesh := by
    by_contra hn
    have hm : mesh<0 := lt_of_not_ge hn
    have hn : (∑j,ell j)≤0 := Finset.sum_nonpos fun j _=>
      (hsmall j).trans (mul_nonpos_of_nonneg_of_nonpos hdmin.le hm.le)
    rw [hsum] at hn
    norm_num at hn
  refine ⟨fun j=>div_pos (hell j) hd0,fun j=>?_,?_⟩
  · apply (div_le_iff₀ hd0).mpr
    exact (hsmall j).trans (by nlinarith)
  · rw [←Finset.sum_div,hsum]
    apply (le_div_iff₀ hd0).mpr
    nlinarith

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.TargetPrincipal
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter UniqueFactorizationMonoid
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma targetPrincipalSupport_prime (η : Character) : ∀P∈targetPrincipalSupport η,Prime P := by
  intro P hP
  exact prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

lemma inverse_target_elementCoeff (η : Character) (u : FreeRow) (n : O) :
    elementCoeff (targetRow η u).inverse n=
      rowTwist (HeckeRowClosure.elementHom ((fixedSourcePrincipal ∅ (by simp)).product η.inverse))
        rowMaskElement 1 u.val n := by
  rw [elementCoeff_inverse]
  unfold targetRow
  rw [elementCoeff_product,elementCoeff_inverse,mul_inv_rev,inv_inv,rawRow_elementCoeff]
  change (elementCoeff (fixedSourcePrincipal ∅ (by simp)) n *
    idealRowHom (rowMaskElement^6*1^4*u.val) (Ideal.span {n})) * (elementCoeff η n)⁻¹=
    elementCoeff ((fixedSourcePrincipal ∅ (by simp)).product η.inverse) n *
      idealRowHom (rowMaskElement^6*1^4*u.val) (Ideal.span {n})
  rw [elementCoeff_product,elementCoeff_inverse]
  ring

theorem principal_target_row_norm_bound (η : Character) (u : FreeRow)
    (hs : Supported (Ideal.span {u.val})) (hp : (targetRow η u).residue=1) :
    rowNorm u≤(HeckeExceptionalRows.bound (targetPrincipalSupport η):ℝ) := by
  obtain ⟨v,hv⟩ := exists_supported_primary_unit u.val hs
  let r : O := (v:O)*u.val
  have hspan : (Ideal.span {r}:Ideal O)=Ideal.span {u.val} :=
    Ideal.span_singleton_mul_left_unit v.isUnit u.val
  have hr : Supported (Ideal.span {r}) := hspan.symm ▸ hs
  have hx : (1:O)^4*u.val=(v⁻¹:Oˣ).val*λ₀^0*(2:O)^0*r := by simp [r]
  let η0 := (fixedSourcePrincipal ∅ (by simp)).product η.inverse
  have hmod : η0.modulus=η.modulus := by
    change (1:Ideal O)⊓η.modulus=η.modulus
    simp
  have hinv : (targetRow η u).inverse.residue=1 := by
    change (targetRow η u).residue⁻¹=1
    rw [hp,inv_one]
  have hfixed := HeckeRowNonprincipal.principal_row_fixed_support η0 (targetRow η u).inverse
    rowMaskElement 1 u.val rowMaskElement_ne_zero (dvd_mul_left _ _) (dvd_mul_right _ _)
    v⁻¹ 0 0 r hr hv hx (inverse_target_elementCoeff η u) hinv (fun P _=>hspan.symm ▸ u.property.2 P)
  rw [hmod] at hfixed
  have hn := HeckeExceptionalRows.row_norm_bound (targetPrincipalSupport η) (targetPrincipalSupport_prime η) hfixed
  rw [hspan] at hn
  unfold rowNorm
  exact_mod_cast hn

theorem excluded_target_nonprincipal_eventually (η : Character) (d : ℝ) (hd : 0<d) :
    ∀ᶠ Z : ℝ in atTop,∀u : FreeRow,Z^d≤ rowNorm u →
      Supported (Ideal.span {u.val}) → ∀S : Finset (Ideal O),∀hS : ∀P∈S,Prime P,
      ((targetRow η u).excludePrimes S hS).residue≠1 := by
  filter_upwards [(tendsto_rpow_atTop hd).eventually
    (eventually_gt_atTop (HeckeExceptionalRows.bound (targetPrincipalSupport η):ℝ))]
    with Z hZ u hu hs S hS
  intro hp
  have hp' := (HeckeFiniteDeletion.principal_iff_of_mask _ _ (excludePrimes_mask (targetRow η u) S hS)).mp hp
  exact not_lt_of_ge (principal_target_row_norm_bound η u hs hp') (hZ.trans_le hu)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.DetectorReady
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem source_ray_conductor (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (j : Sum Bool (RayQuotient.Characters M H)) :
    (sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j).modulus.absNorm≤
      sourceConductorConstant M S η*(Ideal.span {u.val}:Ideal O).absNorm := by
  cases j with
  | inl b =>
    cases b with
    | false =>
      apply (targetRow_excluded_conductor S hS η u).trans
      unfold sourceConductorConstant
      ring_nf
      omega
    | true =>
      apply (rowCharacter_conductor S hS u).trans
      unfold sourceConductorConstant
      ring_nf
      omega
  | inr θ =>
    apply (ProbeRayCharacterFamily.raw_twisted_conductor M H hH u θ).trans
    unfold sourceConductorConstant
    ring_nf
    omega

theorem source_ray_nonprincipal_eventually (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (d : ℝ) (hd : 0<d) :
    ∀ᶠ Z : ℝ in atTop,∀U : ℝ,∀u∈rowBand (Z^d) U,
      (calibrationForSet S hmax).residueMonoid u.val≠0 →
      ∀j,(sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue≠1 := by
  filter_upwards [excluded_target_nonprincipal_eventually η d hd,
    ProbeRayCharacterFamily.large_supported_twists_eventually M d hd] with Z htarget hray
  intro U u hu hc j
  have hs := calibration_nonzero_supported S hmax hS.bad u.val hc
  have hnorm := (mem_rowBand.mp hu).2.1
  cases j with
  | inl b =>
    cases b with
    | false => exact htarget u hnorm hs S hS.prime
    | true => exact calibrated_row_nonprincipal S hS.prime hmax hS.bad u (mem_rowBand.mp hu).1 hc
  | inr θ => exact hray u hnorm hs H hH θ

theorem source_ray_conductor_eventually (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (ν : ℝ) (hν : 0<ν) :
    ∀ᶠ Z : ℝ in atTop,∀(u : FreeRow) (d : ℝ),rowNorm u≤Z^(d-ν) →
      ∀j,((sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j).modulus.absNorm:ℝ)≤Z^d := by
  have hh := HeckeDyadic.constant_absorbed_eventually (sourceConductorConstant M S η:ℝ) ν hν
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with Z hC hZ
  intro u d hu j
  have hq : ((sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j).modulus.absNorm:ℝ)≤
      (sourceConductorConstant M S η:ℝ)*rowNorm u := by
    unfold rowNorm
    exact_mod_cast source_ray_conductor M H hH S hS η u j
  apply hq.trans
  calc
    _ ≤ Z^ν*Z^(d-ν) := mul_le_mul hC hu (by unfold rowNorm;positivity) (Real.rpow_nonneg hZ.le _)
    _ = Z^d := by rw [←Real.rpow_add hZ];congr 1;ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.CubeSupportedWitness
namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
open HeckeDetectorSupportedWitness
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
variable (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal) (η : Character)

theorem supported_witnesses_from_source_cube (dmin dmax τ ε e κ heightCost margin : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*heightCost)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤heightCost)
    (hmargin : 0< margin)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*heightCost≤ε/2) :
    ∀ᶠ Z : ℝ in atTop,∀ d : ℝ,dmin≤d → d≤dmax →
      ∀ (U : ℝ) (rows : Finset FreeRow),rows⊆rowBand (Z^(1/100:ℝ)) U →
      (∀u∈rows,(calibrationForSet S hmax).residueMonoid u.val≠0) →
      (∀u∈rows,rowNorm u≤Z^(d-margin)) →
      let χ := fun u : rows => sourceDetectorFamily S hS.prime η u.val (rayCubeFamily M H hH u.val)
      ∀(a : ℝ) (i : ℕ),i≤I → 51/100<a → a≤1 →
        (∀u : rows,detectorMaximum (χ u) (3*(i+1 : ℕ)*(Z^τ))<a+2*e) →
        (∀u : rows,a≤detectorMaximum (χ u) ((3*i : ℕ)*Z^τ)) →
        ∀ tstar : ℝ,1≤tstar → tstar≤3/2 →
          Nonempty (∀u : rows,SupportedWitness (χ u) (Z^d) a ε tstar (Z^τ)
            ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z0,hdet⟩ := actual_supported_witness_family dmin dmax τ ε e κ heightCost I
    hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hheightCost hbudget
  filter_upwards [eventually_ge_atTop Z0,
    source_ray_nonprincipal_eventually M H hH S hS hmax η (1/100) (by norm_num),
    source_ray_conductor_eventually M H hH S hS.prime η margin hmargin] with Z hZ hnp hcond
  intro d hd hd' U rows hrows hcal hrow
  dsimp only
  intro a i hi ha ha' hnext hcurrent tstar ht ht'
  let χ := fun u : rows => sourceDetectorFamily S hS.prime η u.val (rayCubeFamily M H hH u.val)
  have hχ : ∀u j,(χ u j).residue≠1 := fun u=>hnp U u.val (hrows u.property) (hcal u.val u.property)
  have heq (u : rows) := detectorMaximum_eq_nonprincipal (χ u) (hχ u)
  exact hdet Z hZ d hd hd' χ hχ a i hi ha ha'
    (fun u=>by rw [←heq u];exact hnext u)
    (fun u=>by rw [←heq u];exact hcurrent u)
    (fun u=>hcond u.val d (hrow u.val u.property)) tstar ht ht'

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.SourceBatch
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch ProbePhysical
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.ProbeHighRowFamily.instFiniteQuotientOIdeal
theorem actual_source_batch_oai (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κ heightCost margin mesh binWidth : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hdtop : dmax≤37/42) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*heightCost)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤heightCost)
    (hmargin : 0< margin) (hm : 0≤ mesh) (hb : 0<binWidth)
    (hbudget : 12*e*((22:ℝ)+2)+8*κ+2*heightCost≤ε/2) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → d≤dmax →
    ∀(U : ℝ) (rows : Finset FreeRow),rows.Nonempty → rows⊆rowBand (Z^(1/100:ℝ)) U →
      (∀u∈rows,(calibrationForSet S hmax).residueMonoid u.val≠0) →
      (∀u∈rows,rowNorm u≤Z^(d-margin)) →
    ∀(a : ℝ) (i : ℕ),i≤I → 51/100<a → a≤1 →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*i:ℕ)*Z^τ)) →
    ∀tstar : ℝ,1≤tstar → tstar≤3/2 →
    ∀(N : ℕ) (ell : Fin N→ℝ),(∀j,0<ell j) → (∀j,ell j≤dmin*mesh) → (∑j,ell j)=1/6 →
    ∀(W : Fin N→ℝ→ℂ) (upper : Fin N→ℝ) (z : Fin N→ℂ),
    ∃B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
        (Z^d) a ε tstar (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
      B.rows=rows ∧ B.data=sourceMomentData M H hH S hS.prime η ∧
      B.reverse=sourceMomentReverse M H ∧ B.slots=Finset.univ ∧
      B.widths=(fun j=>ell j/d) ∧ B.profile=W ∧ B.upper=upper ∧ B.external=z ∧
      B.mesh=mesh ∧ B.binWidth=binWidth ∧
      (∀u∈rows,∀j,B.family u j=sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) := by
  have hw := supported_witnesses_from_source_cube M H hH S hS hmax η
    dmin dmax τ ε e κ heightCost margin I hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hheightCost hmargin hbudget
  filter_upwards [hw,eventually_ge_atTop (1:ℝ)] with Z hw hZ
  intro d hd hd' U rows hne hrows hcal hrow a i hi ha ha' hnext hcurrent tstar ht ht' N ell hell hsmall hsum W upper z
  obtain ⟨w⟩ := hw d hd hd' U rows hrows hcal hrow a i hi ha ha'
    (fun u=>hnext u.val u.property) (fun u=>hcurrent u.val u.property) tstar ht ht'
  obtain ⟨u0,h0⟩ := hne
  have hnorm (u : FreeRow) (hu : u∈rows) : rowNorm u≤Z^d :=
    (hrow u hu).trans (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
  obtain ⟨hwp,hwm,hsp⟩ := physical_slot_widths ell d dmin mesh hdmin hd (hd'.trans hdtop) hell hsmall hsum
  let B := retainedSourceBatch M H hH S hS η rows u0 h0 (Z^d) a ε tstar (Z^τ)
    ((Z^d)^(τ/(2*dmax))) i (fun u hu=>w ⟨u,hu⟩) hnorm
    Finset.univ W upper (fun j=>ell j/d) z mesh binWidth hm hb (fun j _=>hwp j) (fun j _=>hwm j) hsp
  refine ⟨B,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  intro u hu j
  dsimp [B,retainedSourceBatch]
  rw [retainedProjection_of_mem rows u0 u hu]
end SevenEighths.ProbeHighRowFamily

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.ProbeHighRowFamily.actual_source_batch_oai := @OAI.SevenEighths.ProbeHighRowFamily.actual_source_batch_oai
