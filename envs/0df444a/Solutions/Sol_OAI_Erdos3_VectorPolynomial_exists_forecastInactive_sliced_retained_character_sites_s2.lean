-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_retained_character_sites_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:49:09.158606+00:00
-- url     : https://prove2.me/submissions/5b0e96ad-1126-4f62-a26d-b5020fac659d

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B178
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B196
import Definitions.Def_OAIE3v2B197
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedInactiveResidueJetPMF_norm_le_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_forecastInactive_sliced_fixed_zero_axis_site_small_or_dense_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_forecastInactive_sliced_fixed_residue_identity_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FiniteFourierSmoothing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteImageCharacteristic_norm_le_one {X H : Type*} [Fintype X]
    [AddCommGroup H] [Fintype H] (p : FiniteProbabilityWeights X) (Y : X → H) (χ : AddChar H ℂ) :
    ‖finiteImageCharacteristic p Y χ‖ ≤ 1 := by
  exact (p.norm_complexMean_le_mean_norm _).trans_eq (by
    simp only [AddChar.norm_apply, p.mean_const])

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CharacterCoordinateScale
namespace OAI

section

namespace Erdos3

theorem torsionLatticeCharacter_card_le (I : Type*) [Fintype I] (a : ℕ) [NeZero a] :
    Fintype.card (TorsionLatticeCharacter I a) ≤ a ^ Fintype.card I := by
  classical
  let _ : Fintype (rootsOfUnity a ℂ) := Fintype.ofFinite _
  have h := Fintype.card_le_of_injective torsionCharacterCoordinates
    (torsionCharacterCoordinates_injective (I := I) (a := a))
  have hc : Fintype.card (rootsOfUnity a ℂ) = a := by
    rw [← Nat.card_eq_fintype_card, Complex.card_rootsOfUnity]
  rw [Fintype.card_fun, hc] at h
  exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductPMFMap
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem dependentProductPMF_apply {D : Type*} [Fintype D] {X : D → Type*}
    [∀ d, Countable (X d)] [∀ d, MeasurableSpace (X d)] [∀ d, MeasurableSingletonClass (X d)]
    (p : ∀ d, PMF (X d)) (x : ∀ d, X d) : dependentProductPMF p x = ∏ d, p d (x d) := by
  simp only [dependentProductPMF, Measure.toPMF_apply, Measure.pi_singleton]
  exact Finset.prod_congr rfl (fun d _ => (p d).toMeasure_apply_singleton (x d) (measurableSet_singleton _))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialResidues
namespace OAI

section

namespace Erdos3

theorem integerPolynomial_eval_residue {X : Type*} (p : MvPolynomial X ℤ)
    (m : ℕ) (x : X → ℤ) :
    ((MvPolynomial.eval x p : ℤ) : ZMod m) =
      MvPolynomial.eval₂ (Int.castRingHom (ZMod m)) (integerResidueMap X m x) p := by
  have heq : integerResidueMap X m x = (fun i => (x i : ZMod m)) := rfl
  rw [heq]
  simpa only [MvPolynomial.eval₂_id, RingHom.comp_id, Int.coe_castRingHom] using
    MvPolynomial.hom_eval₂ p (RingHom.id ℤ) (Int.castRingHom (ZMod m)) x

theorem integerPolynomial_eval_congr {X : Type*} (p : MvPolynomial X ℤ)
    (m : ℕ) {x y : X → ℤ} (hxy : integerResidueMap X m x = integerResidueMap X m y) :
    ((MvPolynomial.eval x p : ℤ) : ZMod m) = ((MvPolynomial.eval y p : ℤ) : ZMod m) := by
  rw [integerPolynomial_eval_residue, integerPolynomial_eval_residue, hxy]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformProductAccuracy
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_finset_prod_sub_prod_le {ι : Type*} (S : Finset ι) (f g : ι → ℂ)
    {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hf : ∀ i ∈ S, ‖f i‖ ≤ B) (hg : ∀ i ∈ S, ‖g i‖ ≤ B)
    (hdiff : ∀ i ∈ S, ‖f i - g i‖ ≤ δ) :
    ‖(∏ i ∈ S, f i) - ∏ i ∈ S, g i‖ ≤ S.card * δ * B ^ S.card := by
  classical
  revert hf hg hdiff
  induction S using Finset.induction_on with
  | empty => intro _ _ _; simp
  | @insert a S ha ih =>
    intro hf hg hdiff
    have hrec := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      (fun i hi => hdiff i (Finset.mem_insert_of_mem hi))
    have hprod : ‖∏ i ∈ S, g i‖ ≤ B ^ S.card := by
      rw [norm_prod]
      calc
        _ ≤ ∏ _i ∈ S, B := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          (fun i hi => hg i (Finset.mem_insert_of_mem hi))
        _ = _ := by simp
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    calc
      _ = ‖f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i) +
          (f a - g a) * ∏ i ∈ S, g i‖ := by congr 1; ring
      _ ≤ ‖f a‖ * ‖(∏ i ∈ S, f i) - ∏ i ∈ S, g i‖ +
          ‖f a - g a‖ * ‖∏ i ∈ S, g i‖ := by
        simpa only [norm_mul] using norm_add_le
          (f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i)) ((f a - g a) * ∏ i ∈ S, g i)
      _ ≤ B * (S.card * δ * B ^ S.card) + δ * B ^ S.card :=
        add_le_add (mul_le_mul (hf a (Finset.mem_insert_self _ _)) hrec
          (norm_nonneg _) (zero_le_one.trans hB))
          (mul_le_mul (hdiff a (Finset.mem_insert_self _ _)) hprod (norm_nonneg _) hδ)
      _ = (S.card : ℝ) * δ * B ^ (S.card + 1) + δ * B ^ S.card := by rw [pow_succ]; ring
      _ ≤ (S.card : ℝ) * δ * B ^ (S.card + 1) + δ * B ^ (S.card + 1) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (Nat.le_succ _)) hδ)
      _ = _ := by push_cast; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem uniformProductAccuracy_spec (N : ℕ) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) :
    0 < uniformProductAccuracy N C δ ∧ uniformProductAccuracy N C δ ≤ 1 ∧
      (N : ℝ) * uniformProductAccuracy N C δ * (C + 2) ^ N ≤ δ := by
  have hD : 0 < ((N : ℝ) + 1) * (C + 2) ^ N := by positivity
  have he : 0 < uniformProductAccuracy N C δ := lt_min zero_lt_one (div_pos hδ hD)
  refine ⟨he, min_le_left _ _, ?_⟩
  have hbound : uniformProductAccuracy N C δ * (((N : ℝ) + 1) * (C + 2) ^ N) ≤ δ :=
    (le_div_iff₀ hD).mp (min_le_right _ _)
  have hp : 0 ≤ uniformProductAccuracy N C δ * (C + 2) ^ N := by positivity
  nlinarith

theorem norm_prod_sub_prod_le_uniform_accuracy {A : Type*} [Fintype A]
    (N : ℕ) (hcard : Fintype.card A ≤ N) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ)
    (f g : A → ℂ) (hg : ∀ a, ‖g a‖ ≤ C)
    (herr : ∀ a, ‖f a - g a‖ ≤ uniformProductAccuracy N C δ) :
    ‖(∏ a, f a) - ∏ a, g a‖ ≤ δ := by
  obtain ⟨he0, he1, heδ⟩ := uniformProductAccuracy_spec N hC hδ
  have hB : 1 ≤ C + 2 := by linarith
  have hf (a : A) : ‖f a‖ ≤ C + 2 := by
    have hn : ‖f a‖ ≤ ‖f a - g a‖ + ‖g a‖ := by
      simpa only [sub_add_cancel] using norm_add_le (f a - g a) (g a)
    linarith [herr a, hg a]
  have hprod := norm_finset_prod_sub_prod_le Finset.univ f g hB he0.le
    (fun a _ => hf a) (fun a _ => (hg a).trans (by linarith)) (fun a _ => herr a)
  have hc : (Fintype.card A : ℝ) ≤ N := by exact_mod_cast hcard
  calc
    _ ≤ (Fintype.card A : ℝ) * uniformProductAccuracy N C δ * (C + 2) ^ Fintype.card A := by
      simpa only [Finset.card_univ] using hprod
    _ ≤ (N : ℝ) * uniformProductAccuracy N C δ * (C + 2) ^ N :=
      mul_le_mul (mul_le_mul_of_nonneg_right hc he0.le)
        (pow_le_pow_right₀ hB hcard) (pow_nonneg (by linarith) _) (by positivity)
    _ ≤ δ := heδ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FiniteCharacterOrderTail
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {I H : Type*} [Fintype I]
  [AddCommGroup H] [Fintype H]

theorem finiteCharacter_exactOrder_card_le
    (π : (I → ℤ) →+ H) (hπ : Function.Surjective π) (q : ℕ) (hq : 0 < q) :
    (Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ = q)).card ≤ q ^ Fintype.card I := by
  let : NeZero q := ⟨hq.ne'⟩
  let f : {χ : AddChar H ℂ // orderOf χ = q} → TorsionLatticeCharacter I q :=
    fun χ => ⟨characterPullback π χ.val, by
      simpa only [map_pow, map_one, χ.property] using
        congrArg (characterPullback π) (pow_orderOf_eq_one χ.val)⟩
  have hf : Function.Injective f := by
    intro χ ψ h
    apply Subtype.ext
    exact AddChar.compAddMonoidHom_injective_left π hπ (congrArg Subtype.val h)
  have hc := (Fintype.card_le_of_injective f hf).trans (torsionLatticeCharacter_card_le I q)
  simpa only [Fintype.card_subtype] using hc

theorem finiteCharacter_boundedOrder_card_le
    (π : (I → ℤ) →+ H) (hπ : Function.Surjective π) (T : ℕ) :
    (Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ ≤ T)).card ≤
      T ^ (Fintype.card I + 1) := by
  let S := Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ ≤ T)
  have hmap : (S : Set (AddChar H ℂ)).MapsTo orderOf (Finset.Icc 1 T) := by
    intro χ hχ
    exact Finset.mem_Icc.mpr ⟨(isOfFinOrder_of_finite χ).orderOf_pos,
      (Finset.mem_filter.mp hχ).2⟩
  change S.card ≤ _
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 T, T ^ Fintype.card I := by
      apply Finset.sum_le_sum
      intro q hq
      have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
      have hc := finiteCharacter_exactOrder_card_le π hπ q hq0
      have hsub : S.filter (fun χ => orderOf χ = q) ⊆
          Finset.univ.filter (fun χ : AddChar H ℂ => orderOf χ = q) := by
        intro χ hχ
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hχ).2⟩
      exact (Finset.card_le_card hsub).trans
        (hc.trans (Nat.pow_le_pow_left (Finset.mem_Icc.mp hq).2 _))
    _ = T ^ (Fintype.card I + 1) := by
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, pow_succ]
      simp only [Nat.add_sub_cancel]
      exact Nat.mul_comm _ _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FiniteUnchargedPrimeDensity
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem finiteCharacter_order_dvd_of_annihilation {H : Type*} [AddCommGroup H]
    (N : ℕ) (hN : ∀ x : H, N • x = 0) (χ : AddChar H ℂ) : orderOf χ ∣ N := by
  apply orderOf_dvd_of_pow_eq_one
  ext x
  rw [AddChar.pow_apply, ← AddChar.map_nsmul_eq_pow, hN x]
  exact χ.map_zero_eq_one

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalForecastGridTail
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]

omit [Fintype J] [DecidableEq J] in
theorem integerResidueTuple_surjective (N : ℕ) :
    Function.Surjective (integerResidueTuple (J := J) N) := by
  intro y
  choose x hx using fun j => ZMod.intCast_surjective (y j)
  exact ⟨x, funext hx⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalForecastCoefficientPeriod
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem exists_character_order_reduction {J : Type*} [Fintype J]
    (N : ℕ) [NeZero N] (χ : AddChar (J → ZMod N) ℂ) :
    ∃ (hq : orderOf χ ∣ N) (ψ : AddChar (J → ZMod (orderOf χ)) ℂ),
      characterPullback (zmodPiReduction hq) ψ = χ := by
  have hann (x : J → ZMod N) : N • x = 0 := by
    ext j
    simp only [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
  have hq := finiteCharacter_order_dvd_of_annihilation N hann χ
  obtain ⟨ψ, hψ, _⟩ := exists_zmodPiReduction_character hq χ (pow_orderOf_eq_one χ)
  exact ⟨hq, ψ, hψ⟩

theorem character_integerTuple_congr_order {J : Type*} [Fintype J]
    (N : ℕ) [NeZero N] (χ : AddChar (J → ZMod N) ℂ) (x y : J → ℤ)
    (hxy : ∀ j, (x j : ZMod (orderOf χ)) = (y j : ZMod (orderOf χ))) :
    χ (fun j => (x j : ZMod N)) = χ (fun j => (y j : ZMod N)) := by
  obtain ⟨hq, ψ, hψ⟩ := exists_character_order_reduction N χ
  rw [← hψ]
  change ψ (fun j => ZMod.castHom hq (ZMod (orderOf χ)) (x j : ZMod N)) =
    ψ (fun j => ZMod.castHom hq (ZMod (orderOf χ)) (y j : ZMod N))
  simp only [map_intCast]
  congr 1
  exact funext hxy

theorem integerLongPolynomial_characteristic_inactive_congr
    {A I J : Type*} [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
    (poly : J → MvPolynomial (A ⊕ I) ℤ) (N : ℕ) [NeZero N]
    (p : FiniteProbabilityWeights (A → ZMod N))
    (χ : AddChar (J → ZMod N) ℂ) (v w : I → ℤ)
    (hvw : ∀ i, (v i : ZMod (orderOf χ)) = (w i : ZMod (orderOf χ))) :
    finiteImageCharacteristic p
      (fun t j => (integerLongPolynomialOutput poly v N t j : ZMod N)) χ =
    finiteImageCharacteristic p
      (fun t j => (integerLongPolynomialOutput poly w N t j : ZMod N)) χ := by
  unfold finiteImageCharacteristic
  congr 1
  funext t
  apply character_integerTuple_congr_order
  intro j
  apply integerPolynomial_eval_congr
  funext a
  cases a with
  | inl a => rfl
  | inr i => exact hvw i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RationalForecastResidueMass
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {A I J : Type*} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

local instance characterOrderNeZero (N : ℕ) [NeZero N]
    (χ : AddChar (J → ZMod N) ℂ) : NeZero (orderOf χ) :=
  ⟨(isOfFinOrder_of_finite χ).orderOf_pos.ne'⟩

omit [Fintype I] [DecidableEq I] in

theorem integerLongPolynomial_characteristic_residue_representative
    (poly : J → MvPolynomial (A ⊕ I) ℤ) (N : ℕ) [NeZero N]
    (p : FiniteProbabilityWeights (A → ZMod N))
    (χ : AddChar (J → ZMod N) ℂ) (v : I → ℤ) :
    finiteImageCharacteristic p
      (fun t j => (integerLongPolynomialOutput poly v N t j : ZMod N)) χ =
    finiteImageCharacteristic p
      (fun t j => (integerLongPolynomialOutput poly
        (fun i => (((v i : ZMod (orderOf χ)).val : ℕ) : ℤ)) N t j : ZMod N)) χ := by
  apply integerLongPolynomial_characteristic_inactive_congr
  intro i
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalScalarSourceEnvelope
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem paddedResidueDensityCap_mono (I : Type*) [Fintype I] {M N : ℕ} (hMN : M ≤ N) :
    paddedResidueDensityCap I M ≤ paddedResidueDensityCap I N := by
  unfold paddedResidueDensityCap scalarCubeResidueDensityCap
  gcongr

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem scalarCubePrimitiveEnvelope_mono (I : Type*) [Fintype I] (A : ℝ≥0)
    {B B' T T' : ℝ≥0} {M N : ℕ} (hB : B ≤ B') (hT : T ≤ T') (hM : M ≤ N) :
    scalarCubePrimitiveEnvelope I A B T M ≤ scalarCubePrimitiveEnvelope I A B' T' N := by
  have hB' : (B : ℝ) ≤ B' := hB
  have hT' : (T : ℝ) ≤ T' := hT
  have hM' : (M : ℝ) ≤ N := Nat.cast_le.mpr hM
  have hc := paddedResidueDensityCap_mono I hM
  dsimp only [scalarCubePrimitiveEnvelope]
  linarith only [hB', hT', hM', hc]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InactiveAxisScale
namespace OAI

section

namespace Erdos3

theorem inactiveSideLength_lower_power {h K q : ℕ} (hh : 0 < h) (hq : 0 < q)
    (hlarge : 2 * q ≤ K) : K < q * 2 ^ h * inactiveSideLength h K q ^ h := by
  have hpos := inactiveSideLength_pos (K := K) hh hq
  have hnext : K / q < (inactiveSideLength h K q + 1) ^ h := by
    simpa [inactiveSideLength, hlarge] using Nat.lt_pow_nthRoot_add_one hh.ne' (K / q)
  have hdiv : K < q * (K / q + 1) := by
    have hm := Nat.mod_lt K hq
    have he := Nat.mod_add_div K q
    nlinarith
  calc
    K < q * (K / q + 1) := hdiv
    _ ≤ q * (inactiveSideLength h K q + 1) ^ h :=
      Nat.mul_le_mul_left q (Nat.succ_le_of_lt hnext)
    _ ≤ q * (2 * inactiveSideLength h K q) ^ h := by gcongr; omega
    _ = _ := by rw [mul_pow]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SiteTwistCommonModulus
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {A S : Type*} [Fintype A] [Fintype S]
variable {I : A → Type*} [∀ a, Fintype (I a)]

theorem finite_site_product_expansion (c : ∀ a, I a → ℂ)
    (f : ∀ a, I a → S → ℂ) :
    (∏ a, ∑ k, c a k * ∏ s, f a k s) =
      ∑ k : ∀ a, I a, (∏ a, c a (k a)) * ∏ s, ∏ a, f a (k a) s := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.prod_mul_distrib, Finset.prod_comm]

theorem finite_site_product_coefficient_norm (c : ∀ a, I a → ℂ) :
    (∑ k : ∀ a, I a, ‖∏ a, c a (k a)‖) = ∏ a, ∑ k, ‖c a k‖ := by
  simp only [norm_prod, Fintype.prod_sum]

theorem finite_site_product_coefficient_norm_le (c : ∀ a, I a → ℂ)
    (C : A → ℝ) (hc : ∀ a, (∑ k, ‖c a k‖) ≤ C a) :
    (∑ k : ∀ a, I a, ‖∏ a, c a (k a)‖) ≤ ∏ a, C a := by
  rw [finite_site_product_coefficient_norm]
  exact Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (fun a _ => hc a)

theorem finite_site_product_approximation (c : ∀ a, I a → ℂ)
    (f : ∀ a, I a → S → ℂ) (g : A → ℂ)
    (N : ℕ) (hcard : Fintype.card A ≤ N) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ)
    (hg : ∀ a, ‖g a‖ ≤ C)
    (he : ∀ a, ‖g a - ∑ k, c a k * ∏ s, f a k s‖ ≤ uniformProductAccuracy N C δ) :
    ‖(∏ a, g a) -
      ∑ k : ∀ a, I a, (∏ a, c a (k a)) * ∏ s, ∏ a, f a (k a) s‖ ≤ δ := by
  rw [← finite_site_product_expansion]
  have h := norm_prod_sub_prod_le_uniform_accuracy N hcard hC hδ
    (fun a => ∑ k, c a k * ∏ s, f a k s) g hg
    (fun a => by simpa only [norm_sub_rev] using he a)
  simpa only [norm_sub_rev] using h

end Erdos3

end

section

namespace Erdos3.ScalarSiteExpansion

open scoped NNReal

universe u v

variable {S : Type u} {e : ScalarSiteExpansion.{u,v} S}

theorem Bounds.mono {T D C H T' D' C' H' : ℝ} {L L' : ℝ≥0}
    (h : e.Bounds T D C L H) (hT : T ≤ T') (hD : D ≤ D') (hC : C ≤ C')
    (hL : L ≤ L') (hH : H ≤ H') : e.Bounds T' D' C' L' H' :=
  ⟨h.card_le.trans hT, h.period_pos, fun i => (h.period_le i).trans hD,
    h.coefficient_le.trans hC, h.factor_bound, fun i s r => (h.lipschitz i s r).weaken hL,
    fun i s r x hx => h.support i s r x (hH.trans hx)⟩

end Erdos3.ScalarSiteExpansion

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

attribute [local instance] ScalarSiteExpansion.termFinite

universe u v w

variable {A : Type u} {S : Type v} [Fintype A] [Fintype S]
variable (e : A → ScalarSiteExpansion.{v,w} S)

variable {T D C H : A → ℝ} {L : ℝ≥0}
variable (h : ∀ a, (e a).Bounds (T a) (D a) (C a) L (H a))

include h in
omit [Fintype S] in
theorem siteFamily_coefficient_le : (∑ k, ‖siteFamilyCoefficient e k‖) ≤ ∏ a, C a :=
  finite_site_product_coefficient_norm_le (fun a => (e a).coefficient) C
    (fun a => (h a).coefficient_le)

theorem siteFamily_approximation (y : S → A → ℤ) (x : S → A → ℝ) (g : A → ℂ)
    (N : ℕ) (hcard : Fintype.card A ≤ N) {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ)
    (hg : ∀ a, ‖g a‖ ≤ B)
    (he : ∀ a, ‖g a - (e a).eval (fun s => y s a) (fun s => x s a)‖ ≤
      uniformProductAccuracy N B δ) :
    ‖(∏ a, g a) - siteFamilyEval e y x‖ ≤ δ := by
  exact finite_site_product_approximation (fun a => (e a).coefficient)
    (fun a k s => (e a).factor k s (y s a : ZMod ((e a).period k)) (x s a))
    g N hcard hB hδ hg he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedPlateauSiteApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {A : Type*} [Fintype A] {I : A → Type*} [∀ a, Fintype (I a)]

theorem sigma_sum_coefficient_norm_le (w : A → ℂ) (c : ∀ a, I a → ℂ)
    {C B : ℝ} (hB : 0 ≤ B) (hw : (∑ a, ‖w a‖) ≤ C)
    (hc : ∀ a, (∑ i, ‖c a i‖) ≤ B) :
    (∑ p : Σ a, I a, ‖w p.1 * c p.1 p.2‖) ≤ C * B := by
  rw [Fintype.sum_sigma]
  simp only [norm_mul, ← Finset.mul_sum]
  calc
    _ ≤ ∑ a, ‖w a‖ * B :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hc a) (norm_nonneg _))
    _ = (∑ a, ‖w a‖) * B := (Finset.sum_mul _ _ _).symm
    _ ≤ C * B := mul_le_mul_of_nonneg_right hw hB

theorem sigma_sum_approximation_error (w g : A → ℂ) (c v : ∀ a, I a → ℂ)
    {C ε : ℝ} (hε : 0 ≤ ε) (hw : (∑ a, ‖w a‖) ≤ C)
    (he : ∀ a, ‖g a - ∑ i, c a i * v a i‖ ≤ ε) :
    ‖(∑ a, w a * g a) -
      ∑ p : Σ a, I a, (w p.1 * c p.1 p.2) * v p.1 p.2‖ ≤ C * ε := by
  rw [Fintype.sum_sigma]
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a, ‖w a * g a - w a * ∑ i, c a i * v a i‖ := norm_sum_le _ _
    _ ≤ ∑ a, ‖w a‖ * ε := by
      apply Finset.sum_le_sum
      intro a _
      rw [← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_left (he a) (norm_nonneg _)
    _ = (∑ a, ‖w a‖) * ε := (Finset.sum_mul _ _ _).symm
    _ ≤ C * ε := mul_le_mul_of_nonneg_right hw hε

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastContinuousRetainedExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite

universe u v w uR

variable {R : Type uR} {A : Type u} {S : Type v}
variable [Fintype R] [Fintype A] [Fintype S]
variable (e : R → A → ScalarSiteExpansion.{v,w} S)

theorem forecastSiteMixture_expansion (c : R → ℂ)
    (y : S → A → ℤ) (x : S → A → ℝ) :
    (∑ r, c r * siteFamilyEval (e r) y x) =
      ∑ t : Σ r, ∀ a, (e r a).Term,
        forecastSiteMixtureCoefficient e c t * ∏ s,
          siteFamilyFactor (e t.1) t.2 s
            (fun a => (y s a : ZMod ((e t.1 a).period (t.2 a)))) (x s) := by
  simp only [Fintype.sum_sigma, forecastSiteMixtureCoefficient, siteFamilyEval,
    Finset.mul_sum, mul_assoc]

omit [Fintype S] in
theorem forecastSiteMixture_coefficient_mass
    {T D C H : A → ℝ} {L : ℝ≥0}
    (he : ∀ r a, (e r a).Bounds (T a) (D a) (C a) L (H a))
    (hC : ∀ a, 0 ≤ C a) (c : R → ℂ) {M : ℝ}
    (hc : (∑ r, ‖c r‖) ≤ M) :
    (∑ t : Σ r, ∀ a, (e r a).Term, ‖forecastSiteMixtureCoefficient e c t‖) ≤
      M * ∏ a, C a := by
  exact sigma_sum_coefficient_norm_le c (fun r => siteFamilyCoefficient (e r))
    (Finset.prod_nonneg (fun a _ => hC a)) hc
    (fun r => siteFamily_coefficient_le (e r) (he r))

theorem forecastResidueWeight_mass (w : R → ℝ) (a : R → ℂ)
    (hw : ∀ r, 0 ≤ w r) (hmass : ∑ r, w r ≤ 1) (ha : ∀ r, ‖a r‖ ≤ 1) :
    (∑ r, ‖(w r : ℂ) * a r‖) ≤ 1 := by
  apply le_trans (Finset.sum_le_sum (fun r _ => ?_)) hmass
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw r)]
  exact mul_le_of_le_one_right (hw r) (ha r)

omit [Fintype S] in
theorem forecastSiteMixture_weighted_mass
    {T D C H : A → ℝ} {L : ℝ≥0}
    (he : ∀ r a, (e r a).Bounds (T a) (D a) (C a) L (H a))
    (hC : ∀ a, 0 ≤ C a) (w : R → ℝ) (a : R → ℂ)
    (hw : ∀ r, 0 ≤ w r) (hmass : ∑ r, w r ≤ 1) (ha : ∀ r, ‖a r‖ ≤ 1) :
    (∑ t : Σ r, ∀ a, (e r a).Term,
      ‖forecastSiteMixtureCoefficient e (fun r => (w r : ℂ) * a r) t‖) ≤ ∏ a, C a := by
  simpa only [one_mul] using forecastSiteMixture_coefficient_mass e he hC
    (fun r => (w r : ℂ) * a r) (forecastResidueWeight_mass w a hw hmass ha)

theorem forecastSiteMixture_error (c μ : R → ℂ)
    (y : S → A → ℤ) (x : S → A → ℝ) {M δ : ℝ}
    (hδ : 0 ≤ δ) (hc : (∑ r, ‖c r‖) ≤ M)
    (he : ∀ r, ‖μ r - siteFamilyEval (e r) y x‖ ≤ δ) :
    ‖(∑ r, c r * μ r) - (∑ r, c r * siteFamilyEval (e r) y x)‖ ≤ M * δ := by
  rw [forecastSiteMixture_expansion]
  exact sigma_sum_approximation_error c μ (fun r => siteFamilyCoefficient (e r))
    (fun r k => ∏ s, siteFamilyFactor (e r) k s
      (fun a => (y s a : ZMod ((e r a).period (k a)))) (x s)) hδ hc he

theorem forecastSiteMixture_weighted_error (w : R → ℝ) (a μ : R → ℂ)
    (hw : ∀ r, 0 ≤ w r) (hmass : ∑ r, w r ≤ 1) (ha : ∀ r, ‖a r‖ ≤ 1)
    (y : S → A → ℤ) (x : S → A → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (he : ∀ r, ‖μ r - siteFamilyEval (e r) y x‖ ≤ δ) :
    ‖(∑ r, (w r : ℂ) * a r * μ r) -
      (∑ r, (w r : ℂ) * a r * siteFamilyEval (e r) y x)‖ ≤ δ := by
  simpa only [one_mul] using forecastSiteMixture_error e
    (fun r => (w r : ℂ) * a r) μ y x hδ (forecastResidueWeight_mass w a hw hmass ha) he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSlicedGridGeometryBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "side" => inactiveSideLength degree height denom

theorem allocatedPrincipalSides_inactive
    (hsmall : height ≤ S.value ^ degree) (b : B ⟨j,Sum.inr i⟩) (v : Fin degree) :
    allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ = side := by
  rw [layerIntegerPrincipalSlots_card]
  change integerAxisSideLength degree height S.value
    (principalProfileSize (R j) (Fintype.card (B ⟨j,Sum.inr i⟩))) = _
  simp only [integerAxisSideLength, Nat.not_lt.mpr hsmall, ite_false]

theorem allocatedSlicedGrid_cases
    (H : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j,Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ ≤
      (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (Q T : ℕ) (hQT : (Q : ℝ) / δ ≤ T) :
    height ≤ allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T ∨
      ((∀ b v, Q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩) ∧
        ((S.value ^ degree < height ∧ ∀ b v, δ * S.value ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)) ∨
         (height ≤ S.value ^ degree ∧ 2 * denom ≤ height ∧
           ∀ b v, δ * side ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)))) := by
  let K := allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T
  by_cases hK : height ≤ K
  · exact Or.inl hK
  have hlarge : 2 * denom ≤ height := by
    have : 2 * denom ≤ K := by dsimp [K, allocatedSlicedGridHeightCutoff]; omega
    omega
  have hside_bound {L h : ℕ} (hd : δ * L ≤ (h : ℝ)) (hh : h < Q) : L ≤ T := by
    have hl : (L : ℝ) ≤ (Q : ℝ) / δ := by
      apply (le_div_iff₀ hδ).mpr
      have hh' : (h : ℝ) ≤ Q := Nat.cast_le.mpr hh.le
      simpa only [mul_comm] using hd.trans hh'
    exact_mod_cast hl.trans hQT
  have hsize : ∀ b v, Q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩ := by
    intro b v
    by_contra hh
    have hL := hside_bound (hdense b v) (Nat.lt_of_not_ge hh)
    apply hK
    by_cases ha : S.value ^ degree < height
    · rw [allocatedPrincipalSides_active B U basis S j i ha b v] at hL
      have hb := hgrid.trans (Nat.pow_le_pow_left hL (layerTailDegree m + 1))
      exact hb.trans (by dsimp [K, allocatedSlicedGridHeightCutoff]; omega)
    · rw [allocatedPrincipalSides_inactive B U basis S j i (Nat.le_of_not_gt ha) b v] at hL
      have hb := (inactiveSideLength_lower_power (Nat.zero_lt_succ j.val) (inactiveDenominator_pos _) hlarge).le
      have hc := hb.trans (Nat.mul_le_mul_left (denom * 2 ^ degree) (Nat.pow_le_pow_left hL degree))
      exact hc.trans (by dsimp [K, allocatedSlicedGridHeightCutoff]; omega)
  refine Or.inr ⟨hsize, ?_⟩
  by_cases ha : S.value ^ degree < height
  · refine Or.inl ⟨ha, ?_⟩
    intro b v
    simpa only [allocatedPrincipalSides_active B U basis S j i ha b v] using hdense b v
  · refine Or.inr ⟨Nat.le_of_not_gt ha, hlarge, ?_⟩
    intro b v
    simpa only [allocatedPrincipalSides_inactive B U basis S j i (Nat.le_of_not_gt ha) b v] using hdense b v

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedFixedAxisCap
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

variable (hsize : ∀ b v, q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "torus" => blockTorusFactor (Fintype.card Empty) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

include hq hsize in

theorem forecastInactive_sliced_fixed_zero_axis_norm_le
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * side ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope Empty A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (hB : uniformSpectrumBlockCount j.val 1 degree ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (c0 z : ℤ) :
    let V := (torus : ℝ) * cost / δ ^ degree
    ‖(((height : ℝ) *
      (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i Finset.univ
        (fun _ => c0) (fun _ => z)).toReal : ℝ) : ℂ)‖ ≤
      uniformSpectrumAbsoluteCap j.val 1 degree P V V := by
  intro V
  have hsize' : ∀ b v, (Fintype.card Empty + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩ := by
    simpa using hsize
  have hrows (t : Finset Empty) (_ : t ∈ (Finset.univ : Finset (Finset Empty))) : t.card ≤ degree := by
    have ht : t = ∅ := Subsingleton.elim _ _
    simp only [ht, Finset.card_empty]
    omega
  have hB' : uniformSpectrumBlockCount j.val (Finset.univ : Finset (Finset Empty)).card
      (degree * (Finset.univ : Finset (Finset Empty)).card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩) := by
    simpa using hB
  have hc := allocatedSupportedSlicedInactiveResidueJetPMF_norm_le_s2
    B U basis hR hσ S q hq r H step c hH hsubset hcell j i hsize' hsmall hlarge
    hδ hlength hstep A hA P hP hsP hstride Finset.univ hrows hB' (fun _ => c0) (fun _ => z)
  simpa only [Finset.card_univ, Fintype.card_finset, Fintype.card_empty, pow_zero,
    pow_one, mul_one, V] using hc

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (lower : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (lower t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => j.val + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in

theorem allocatedInactiveGrid_height_le_of_small_original_side
    (hsmall : height ≤ S.value ^ degree) (Hchild : ℕ)
    (b0 : B ⟨j, Sum.inr i⟩) (v0 : Fin degree)
    (hshort : allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b0,v0⟩ < Hchild) :
    height ≤ denom * 2 ^ degree * Hchild ^ degree + 2 * denom := by
  by_cases hlarge : 2 * denom ≤ height
  · have hside : inactiveSideLength degree height denom ≤ Hchild := by
      rw [allocatedPrincipalSides_inactive B U basis S j i hsmall b0 v0] at hshort
      exact hshort.le
    have hb := (inactiveSideLength_lower_power (Nat.zero_lt_succ j.val)
      (inactiveDenominator_pos _) hlarge).le
    exact (hb.trans (Nat.mul_le_mul_left (denom * 2 ^ degree)
      (Nat.pow_le_pow_left hside degree))).trans (Nat.le_add_right _ _)
  · omega

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "torus" => blockTorusFactor (Fintype.card Empty) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

include hq in
theorem forecastInactive_sliced_fixed_zero_axis_norm_le_small_or_dense
    (δ P : ℝ) (Hchild : ℕ)
    (hδ : 0 < δ)
    (hreg : (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ ≤
        (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)))
    (hsmall : height ≤ S.value ^ degree)
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (hB : uniformSpectrumBlockCount j.val 1 degree ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (c0 z : ℤ) :
    let V := (torus : ℝ) * cost / δ ^ degree
    let cutoff := max (allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i (Nat.ceil ((q : ℝ) / δ)))
      (denom * 2 ^ degree * Hchild ^ degree + 2 * denom)
    ‖(((height : ℝ) *
      (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i Finset.univ
        (fun _ => c0) (fun _ => z)).toReal : ℝ) : ℂ)‖ ≤
      max (cutoff : ℝ) (uniformSpectrumAbsoluteCap j.val 1 degree P V V) := by
  intro V cutoff
  have htrivial :
      ‖(((height : ℝ) *
        (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i Finset.univ
          (fun _ => c0) (fun _ => z)).toReal : ℝ) : ℂ)‖ ≤ height := by
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg)]
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) ((ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one _ _)).trans_eq ENNReal.toReal_one)
  rcases hreg with ⟨b0, v0, hshort⟩ | ⟨hdense, hstep⟩
  · have hk : height ≤ cutoff :=
      (allocatedInactiveGrid_height_le_of_small_original_side B U basis S j i
        hsmall Hchild b0 v0 hshort).trans (le_max_right _ _)
    exact (htrivial.trans (Nat.cast_le.mpr hk)).trans (le_max_left _ _)
  · rcases allocatedSlicedGrid_cases B U basis S j i H hgrid hδ hdense
        q (Nat.ceil ((q : ℝ) / δ)) (Nat.le_ceil _) with hbounded | ⟨hsize, hcases⟩
    · have hk : height ≤ cutoff := hbounded.trans (le_max_left _ _)
      exact (htrivial.trans (Nat.cast_le.mpr hk)).trans (le_max_left _ _)
    · rcases hcases with ⟨hactive, _⟩ | ⟨_, hlarge, hlength⟩
      · exact False.elim ((Nat.not_lt.mpr hsmall) hactive)
      · exact (forecastInactive_sliced_fixed_zero_axis_norm_le
          B U basis hR hσ S q hq r H step c hH hsubset hcell j i hsize hsmall hlarge
          hδ hlength hstep A hA P hP hsP hstride hB c0 z).trans (le_max_right _ _)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedFixedProduct
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable {A : Type*} [Fintype A]

include hq in
theorem exists_forecastInactive_sliced_fixed_product_site
    (selected : A → Σ j : Fin m, Fin (n j))
    (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ ≤
        (H ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩)))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (c0 : A → ℤ)
    (hc0 : ∀ a, allocatedLayerIntegerPMFs B U basis hR hσ S (selected a).1 (selected a).2
      (principalCoefficientChoice (G := G) (layerSamplerDegree I n)
        ⟨(selected a).1, Sum.inr (selected a).2⟩ none) (c0 a) ≠ 0)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty L 1 0 q ≤ P)
    (hstride : ∀ a b v, ((step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0)
    (hCactual : 0 ≤ Cactual) (hδout : 0 < δout) (hQ : 0 ≤ Q) :
    let degree := fun a => (selected a).1.val + 1
    let height := fun a => basisAxisScale (basis (selected a).1) (selected a).2
    let denom := fun a => inactiveDenominator (principalProfileSize (R (selected a).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
    let torus := fun a => blockTorusFactor (Fintype.card Empty) (degree a)
      (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
    let V := fun a => (torus a : ℝ) * ((denom a : ℝ) * 2 ^ degree a) / δ ^ degree a
    let cap := fun a => uniformSpectrumAbsoluteCap (selected a).1.val 1 (degree a) P (V a) (V a)
    let cutoff := fun a => max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
      (selected a).1 (selected a).2 (Nat.ceil ((q : ℝ) / δ)))
      (denom a * 2 ^ degree a * Hchild ^ degree a + 2 * denom a)
    let R0 := fun a => (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (degree a)) : ℝ) *
      R (selected a).1
    let ε := uniformProductAccuracy (Fintype.card A) Cactual δout / 2
    let ζ := fun a => uniformBlockRetainedBias (selected a).1.val 1 (degree a) P (V a) (V a) ε
    let freq := fun a => Real.toNNReal (uniformScaledRetainedFrequencyBound (selected a).1.val 1 P (V a) (ζ a))
    (∀ a, max (cutoff a : ℝ) (cap a) ≤ Cactual) →
    (∀ a, R0 a + 1 / 4 ≤ Real.exp Q) →
    (∀ a, (ε / (cap a + 1))⁻¹ ≤ Real.exp Q) →
    (∀ a, (CircleFourier.characterLipConstant * freq a + 4 : ℝ≥0) ≤ Real.exp Q) →
    (∀ a, (cutoff a : ℝ) ≤ Real.exp Q) →
    (∀ a, (2 * (cutoff a : ℝ≥0) ^ 2 * (cutoff a : ℝ≥0) : ℝ≥0) ≤ Real.exp Q) →
    ε⁻¹ ≤ Real.exp Q →
    (∀ a, max ((uniformSpectrumSizeConstant (selected a).1.val 1 (degree a) P (V a) (V a) /
      ε ^ max (majorArcSpectrumExponent (selected a).1.val 1)
        (majorArcLengthExponent (selected a).1.val * degree a)) * Real.exp (4 * Q + 8))
      (Real.exp (4 * Q + 8)) ≤ Nt) →
    (∀ a, max (uniformScaledRetainedDenominatorBound (selected a).1.val 1 (degree a) P
      (V a) (V a) (ζ a)) 1 ≤ Vt) →
    (∀ a, max (cap a * Real.exp (4 * Q + 8 + Q)) (Real.exp (4 * Q + 8 + Q)) ≤ Ct) →
    (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4 : ℝ≥0) ≤ Lt →
    (∀ a, R0 a + 1 / 4 ≤ Ht) →
    ∃ e : A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ a, (e a).Bounds Nt Vt Ct Lt Ht) ∧
      ∀ z : A → ℤ,
        ‖(((∏ a, (height a : ℝ)) *
          (dependentProductPMF (fun a => allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r
            H step c hH hsubset hcell (selected a).1 (selected a).2 (Finset.univ : Finset (Finset Empty))
            (fun _ => c0 a)) (fun a _ => z a)).toReal : ℝ) : ℂ) -
          siteFamilyEval e (fun _ => z) (fun _ a => (z a : ℝ) / height a)‖ ≤ δout := by
  intro degree height denom torus V cap cutoff R0 ε ζ freq
    hactual hRQ hεQ hLQ hKQ hKLQ hεinvQ hNt hVt hCt hLt hHt
  obtain ⟨hτ, hτ1, _⟩ := uniformProductAccuracy_spec (Fintype.card A) hCactual hδout
  have hε : 0 < ε := half_pos hτ
  have hε1 : ε ≤ 1 := by dsimp only [ε]; linarith
  have heach (a : A) := exists_forecastInactive_sliced_fixed_zero_axis_site_small_or_dense_s2
    B U basis hR hσ S q hq r H step c hH hsubset hcell (selected a).1 (selected a).2 Hchild
    (c0 a) (hc0 a) (hgrid a) (hsmall a) hδ (hreg a) L hL P hP hsP (hstride a)
    (hB a) hε hε1 (hσ1 a) hQ (hRQ a) (hεQ a) (hLQ a) (hKQ a) (hKLQ a) hεinvQ
  choose e he herr using heach
  refine ⟨e, fun a => (he a).mono (hNt a) (hVt a) (hCt a) hLt (hHt a), ?_⟩
  intro z
  let g (a : A) : ℂ := (((height a : ℝ) *
    (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell
      (selected a).1 (selected a).2 (Finset.univ : Finset (Finset Empty))
      (fun _ => c0 a) (fun _ => z a)).toReal : ℝ) : ℂ)
  have hg (a : A) : ‖g a‖ ≤ Cactual :=
    (forecastInactive_sliced_fixed_zero_axis_norm_le_small_or_dense B U basis hR hσ S q hq r
      H step c hH hsubset hcell (selected a).1 (selected a).2 δ P Hchild hδ (hreg a)
      (hsmall a) (hgrid a) L hL hP hsP (hstride a) (hB a) (c0 a) (z a)).trans (hactual a)
  have herr' (a : A) :
      ‖g a - (e a).eval (fun _ => z a) (fun _ => (z a : ℝ) / height a)‖ ≤
      uniformProductAccuracy (Fintype.card A) Cactual δout := by
    simpa only [ScalarSiteExpansion.integerEval, ε, mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)]
      using herr a (z a)
  have hp' := siteFamily_approximation e (fun _ => z)
    (fun _ a => (z a : ℝ) / height a) g (Fintype.card A) le_rfl hCactual hδout hg herr'
  have hj : (((∏ a, (height a : ℝ)) *
      (dependentProductPMF (fun a => allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r
        H step c hH hsubset hcell (selected a).1 (selected a).2 (Finset.univ : Finset (Finset Empty))
        (fun _ => c0 a)) (fun a _ => z a)).toReal : ℝ) : ℂ) = ∏ a, g a := by
    rw [dependentProductPMF_apply, ENNReal.toReal_prod, ← Finset.prod_mul_distrib,
      Complex.ofReal_prod]
  rw [hj]
  exact hp'

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedOriginalSampleResidueMixtureForecast
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem forecastInactive_positiveResidue_mass_sum
    {Ω R : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype R] [DecidableEq R]
    (p : FiniteProbabilityWeights Ω) (residue : Ω → R) :
    (∑ r : {r : R // 0 < p.mass (Finset.univ.filter (fun x => residue x = r))},
      p.mass (Finset.univ.filter (fun x => residue x = r.val))) = 1 := by
  have hsum : (∑ r : R, p.mass (Finset.univ.filter (fun x => residue x = r))) =
      ∑ r : {r : R // 0 < p.mass (Finset.univ.filter (fun x => residue x = r))},
        p.mass (Finset.univ.filter (fun x => residue x = r.val)) := by
    apply Finset.sum_congr_set
      {r : R | 0 < p.mass (Finset.univ.filter (fun x => residue x = r))}
    · intro r hr
      rfl
    · intro r hr
      exact le_antisymm (le_of_not_gt hr) (p.mass_nonneg _)
  rw [← hsum]
  simpa only [FiniteProbabilityWeights.fiberLaw_weight_eq_mass] using
    (p.fiberLaw residue).total

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ForecastInactiveAffineIntervalFixedResidueSite
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (q : ℕ) [NeZero q]
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]
attribute [local instance] ScalarSiteExpansion.termFinite

theorem exists_forecastInactive_sliced_fixed_residue_site
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (coefficient : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q) → ℂ)
    (hcoefficient : ∀ r, ‖coefficient r‖ ≤ 1)
    (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ ≤
        (H ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩)))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (coefficients : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hcoefficients : ∀ a d, coefficients a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty L 1 0 q ≤ P)
    (hstride : ∀ a b v, ((step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0)
    (hCactual : 0 ≤ Cactual) (hCtNonneg : 0 ≤ Ct) (hδout : 0 < δout) (hQ : 0 ≤ Q) :
    let degree := fun a => (selected a).1.val + 1
    let height := fun a => basisAxisScale (basis (selected a).1) (selected a).2
    let denom := fun a => inactiveDenominator (principalProfileSize (R (selected a).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
    let torus := fun a => blockTorusFactor (Fintype.card Empty) (degree a)
      (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
    let V := fun a => (torus a : ℝ) * ((denom a : ℝ) * 2 ^ degree a) / δ ^ degree a
    let cap := fun a => uniformSpectrumAbsoluteCap (selected a).1.val 1 (degree a) P (V a) (V a)
    let cutoff := fun a => max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
      (selected a).1 (selected a).2 (Nat.ceil ((q : ℝ) / δ)))
      (denom a * 2 ^ degree a * Hchild ^ degree a + 2 * denom a)
    let R0 := fun a => (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (degree a)) : ℝ) *
      R (selected a).1
    let ε := uniformProductAccuracy (Fintype.card A) Cactual δout / 2
    let ζ := fun a => uniformBlockRetainedBias (selected a).1.val 1 (degree a) P (V a) (V a) ε
    let freq := fun a => Real.toNNReal (uniformScaledRetainedFrequencyBound (selected a).1.val 1 P (V a) (ζ a))
    (∀ a, max (cutoff a : ℝ) (cap a) ≤ Cactual) →
    (∀ a, R0 a + 1 / 4 ≤ Real.exp Q) →
    (∀ a, (ε / (cap a + 1))⁻¹ ≤ Real.exp Q) →
    (∀ a, (CircleFourier.characterLipConstant * freq a + 4 : ℝ≥0) ≤ Real.exp Q) →
    (∀ a, (cutoff a : ℝ) ≤ Real.exp Q) →
    (∀ a, (2 * (cutoff a : ℝ≥0) ^ 2 * (cutoff a : ℝ≥0) : ℝ≥0) ≤ Real.exp Q) →
    ε⁻¹ ≤ Real.exp Q →
    (∀ a, max ((uniformSpectrumSizeConstant (selected a).1.val 1 (degree a) P (V a) (V a) /
      ε ^ max (majorArcSpectrumExponent (selected a).1.val 1)
        (majorArcLengthExponent (selected a).1.val * degree a)) * Real.exp (4 * Q + 8))
      (Real.exp (4 * Q + 8)) ≤ Nt) →
    (∀ a, max (uniformScaledRetainedDenominatorBound (selected a).1.val 1 (degree a) P
      (V a) (V a) (ζ a)) 1 ≤ Vt) →
    (∀ a, max (cap a * Real.exp (4 * Q + 8 + Q)) (Real.exp (4 * Q + 8 + Q)) ≤ Ct) →
    (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4 : ℝ≥0) ≤ Lt →
    (∀ a, R0 a + 1 / 4 ≤ Ht) →
    let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH
    let Pos := {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q //
      0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))}
    let map := containedProgressionTupleMap B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hsubset
    let w := fun r : Pos => (p.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r.val)) : ℂ) *
      coefficient (progressionPrincipalResidue B (layerSamplerDegree I n) step c q r.val)
    ∃ e : Pos → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ r a, (e r a).Bounds Nt Vt Ct Lt Ht) ∧
      (∑ t : Σ r : Pos, ∀ a, (e r a).Term, ‖forecastSiteMixtureCoefficient e w t‖) ≤ Ct ^ Fintype.card A ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ),
        ‖((∏ a, (height a : ℝ)) : ℂ) *
          (p.fiberLaw map).complexMean (fun y => coefficient (principalResidueLabel q y) *
            (if forecastInactiveFixedOutput B U basis S selected coefficients x y = (fun a _ => z a)
              then 1 else 0)) -
          (∑ r : Pos, w r * siteFamilyEval (e r) (fun _ => z)
            (fun _ a => (z a : ℝ) / height a))‖ ≤ δout := by
  intro degree height denom torus V cap cutoff R0 ε ζ freq
    hactual hRQ hεQ hLQ hKQ hKLQ hεinvQ hNt hVt hCt hLt hHt p Pos map w
  let c0 (a : A) := coefficients a (constantCoefficientSlot _ _)
  have hc0 (a : A) : allocatedLayerIntegerPMFs B U basis hR hσ S (selected a).1 (selected a).2
      (principalCoefficientChoice (G := G) (layerSamplerDegree I n)
        ⟨(selected a).1, Sum.inr (selected a).2⟩ none) (c0 a) ≠ 0 := hcoefficients a _
  have heach (r : Pos) := exists_forecastInactive_sliced_fixed_product_site
    B U basis hR hσ S q (NeZero.pos q) r.val H step c hH hsubset r.property selected
    δ P Hchild hδ hreg hsmall hgrid c0 hc0 hσ1 L hL hP hsP hstride hB
    Cactual δout Q Nt Vt Ct Ht Lt hCactual hδout hQ
    hactual hRQ hεQ hLQ hKQ hKLQ hεinvQ hNt hVt hCt hLt hHt
  choose e he herr using heach
  let mass (r : Pos) := p.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r.val))
  let co (r : Pos) := coefficient (progressionPrincipalResidue B (layerSamplerDegree I n) step c q r.val)
  have hmass : (∑ r : Pos, mass r) ≤ 1 :=
    (forecastInactive_positiveResidue_mass_sum p (principalResidueLabel q)).le
  have hm (r : Pos) : 0 ≤ mass r := p.mass_nonneg _
  refine ⟨e, he, ?_, ?_⟩
  · have hbound := forecastSiteMixture_weighted_mass e he (fun _ => hCtNonneg) mass co hm hmass
      (fun r => hcoefficient _)
    simpa only [Finset.prod_const, Finset.card_univ] using hbound
  · intro x z
    let μ (r : Pos) : ℂ := (((∏ a, (height a : ℝ)) *
      (dependentProductPMF (fun a => allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r.val
        H step c hH hsubset r.property (selected a).1 (selected a).2
        (Finset.univ : Finset (Finset Empty)) (fun _ => c0 a)) (fun a _ => z a)).toReal : ℝ) : ℂ)
    have herr' := forecastSiteMixture_weighted_error e mass co μ hm hmass
      (fun r => hcoefficient _) (fun _ => z) (fun _ a => (z a : ℝ) / height a)
      hδout.le (fun r => herr r z)
    rw [forecastInactive_sliced_fixed_residue_identity_s2 B U basis S hR hσ selected hselected q
      H step c hH hsubset coefficient hsmall coefficients hcoefficients x z, Finset.mul_sum]
    have heq : (∑ r : Pos, ((∏ a, (height a : ℝ)) : ℂ) *
        ((mass r : ℂ) * co r *
          ((dependentProductPMF (fun a => allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r.val
            H step c hH hsubset r.property (selected a).1 (selected a).2
            (Finset.univ : Finset (Finset Empty)) (fun _ => c0 a)) (fun a _ => z a)).toReal : ℂ))) =
        ∑ r : Pos, (mass r : ℂ) * co r * μ r := by
      apply Finset.sum_congr rfl
      intro r _
      dsimp only [μ]
      push_cast
      ring
    rw [heq]
    exact herr'

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ForecastInactiveCharacterSite
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {A J K H : Type*} [Fintype A] [DecidableEq A]
  [Fintype J] [DecidableEq J]

theorem forecastInactiveCharacterCoefficient_norm_le
    (poly : J → MvPolynomial (A ⊕ (K × H)) ℤ) (N : ℕ) [NeZero N]
    (p : FiniteProbabilityWeights (A → ZMod N)) (χ : AddChar (J → ZMod N) ℂ)
    (r : K → H → ZMod (orderOf χ)) :
    ‖forecastInactiveCharacterCoefficient poly N p χ r‖ ≤ 1 :=
  finiteImageCharacteristic_norm_le_one p _ χ

theorem forecastInactiveCharacterCoefficient_eq
    (poly : J → MvPolynomial (A ⊕ (K × H)) ℤ) (N : ℕ) [NeZero N]
    (p : FiniteProbabilityWeights (A → ZMod N)) (χ : AddChar (J → ZMod N) ℂ)
    (v : K → H → ℤ) :
    finiteImageCharacteristic p
      (fun t j => (integerLongPolynomialOutput poly (fun k => v k.1 k.2) N t j : ZMod N)) χ =
      forecastInactiveCharacterCoefficient poly N p χ
        (fun k h => (v k h : ZMod (orderOf χ))) :=
  integerLongPolynomial_characteristic_residue_representative poly N p χ
    (fun k => v k.1 k.2)

section Principal

variable {D α : Type*} {B : D → Type*} {h : D → ℕ}
  {L : PrincipalTupleIndex B h → ℕ}

theorem forecastInactive_principal_characteristic_residue
    (poly : J → MvPolynomial (A ⊕ (PrincipalTupleIndex B h × Option α)) ℤ)
    (N : ℕ) [NeZero N] (p : FiniteProbabilityWeights (A → ZMod N))
    (χ : AddChar (J → ZMod N) ℂ) (y : PrincipalIntegerTuples B h α L) :
    finiteImageCharacteristic p
      (fun t j => (integerLongPolynomialOutput poly
        (fun k => (y k.1 k.2 : ℤ)) N t j : ZMod N)) χ =
      forecastInactiveCharacterCoefficient poly N p χ (principalResidueLabel (orderOf χ) y) :=
  forecastInactiveCharacterCoefficient_eq poly N p χ (fun k h => (y k h : ℤ))

end Principal

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedCappedContinuousSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]
attribute [local instance] ScalarSiteExpansion.termFinite

variable {Vact Out : Type*} [Fintype Vact] [DecidableEq Vact] [Fintype Out] [DecidableEq Out]

attribute [local instance] OAI.Erdos3.VectorPolynomial.instNeZeroNatOrderOfAddCharForallZModComplex_1
theorem exists_forecastInactive_sliced_retained_character_sites_s2_oai
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (poly : Out → MvPolynomial (Vact ⊕ (PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty)) ℤ)
    (N : ℕ) [NeZero N] (pRat : FiniteProbabilityWeights (Vact → ZMod N))
    (T : ℕ) (_hT : 0 < T)
    (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ ≤
        (H ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩)))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (coefficients : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hcoefficients : ∀ a d, coefficients a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ P)
    (hstride : ∀ a b v, ((step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ * T : ℕ) : ℝ) ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0)
    (hCactual : 0 ≤ Cactual) (hCtNonneg : 0 ≤ Ct) (hδout : 0 < δout) (hQ : 0 ≤ Q)
    (hnumerics : ∀ q : ℕ, 0 < q → q ≤ T →
      forecastInactiveSlicedSiteNumerics (G := G) B (R := R) selected q Hchild
        δ P Cactual δout Q Nt Vt Ct Ht Lt) :
    let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH
    let map := containedProgressionTupleMap B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hsubset
    let law := p.fiberLaw map
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    let height := fun a => basisAxisScale (basis (selected a).1) (selected a).2
    let weight := fun (χ : Ch) (r : Pos χ) =>
      (p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
        forecastInactiveCharacterCoefficient poly N pRat χ.val
          (progressionPrincipalResidue B (layerSamplerDegree I n) step c (orderOf χ.val) r.val)
    ∃ e : ∀ χ : Ch, Pos χ → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ χ r a, (e χ r a).Bounds Nt Vt Ct Lt Ht) ∧
      (∑ χ : Ch, ∑ t : Σ r : Pos χ, ∀ a, (e χ r a).Term,
        ‖forecastSiteMixtureCoefficient (e χ) (weight χ) t‖) ≤
        (T : ℝ) ^ (Fintype.card Out + 1) * Ct ^ Fintype.card A ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ) (outPoint : Out → ZMod N),
        ‖(∑ χ : Ch, ((∏ a, (height a : ℝ)) : ℂ) *
          law.complexMean (fun y => finiteImageCharacteristic pRat
            (fun t j => (integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j : ZMod N)) χ.val *
            (if forecastInactiveFixedOutput B U basis S selected coefficients x y = (fun a _ => z a)
              then (1 : ℂ) else 0)) * star (χ.val outPoint)) -
          (∑ χ : Ch, (∑ r : Pos χ, weight χ r *
            siteFamilyEval (e χ r) (fun _ => z) (fun _ a => (z a : ℝ) / height a)) *
              star (χ.val outPoint))‖ ≤ (T : ℝ) ^ (Fintype.card Out + 1) * δout := by
  intro p map law Ch Pos height weight
  have horder (χ : Ch) : orderOf χ.val ≤ T := (Finset.mem_filter.mp χ.property).2
  have hn (χ : Ch) := hnumerics (orderOf χ.val) (isOfFinOrder_of_finite χ.val).orderOf_pos (horder χ)
  have hstride' (χ : Ch) (a : A) b v :
      ((step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ * orderOf χ.val : ℕ) : ℝ) ≤ P :=
    (Nat.cast_le.mpr (Nat.mul_le_mul_left _ (horder χ))).trans (hstride a b v)
  have heach (χ : Ch) := exists_forecastInactive_sliced_fixed_residue_site
    B U basis hR hσ S (orderOf χ.val) H step c hH hsubset selected hselected
    (forecastInactiveCharacterCoefficient poly N pRat χ.val)
    (forecastInactiveCharacterCoefficient_norm_le poly N pRat χ.val)
    δ P Hchild hδ hreg hsmall hgrid coefficients hcoefficients hσ1 L hL hP
    ((scalarCubePrimitiveEnvelope_mono Empty L (le_refl (1 : ℝ≥0))
      (le_refl (0 : ℝ≥0)) (horder χ)).trans hsP)
    (hstride' χ) hB Cactual δout Q Nt Vt Ct Ht Lt hCactual hCtNonneg hδout hQ
    ((hn χ).1) ((hn χ).2.1) ((hn χ).2.2.1) ((hn χ).2.2.2.1) ((hn χ).2.2.2.2.1) ((hn χ).2.2.2.2.2.1) ((hn χ).2.2.2.2.2.2.1) ((hn χ).2.2.2.2.2.2.2.1) ((hn χ).2.2.2.2.2.2.2.2.1) ((hn χ).2.2.2.2.2.2.2.2.2.1) ((hn χ).2.2.2.2.2.2.2.2.2.2.1) ((hn χ).2.2.2.2.2.2.2.2.2.2.2)
  choose e he hmass herr using heach
  have hcard : (Fintype.card Ch : ℝ) ≤ (T : ℝ) ^ (Fintype.card Out + 1) := by
    have hb := finiteCharacter_boundedOrder_card_le (integerResidueTuple (J := Out) N)
      (integerResidueTuple_surjective N) T
    have hnat : Fintype.card Ch ≤ T ^ (Fintype.card Out + 1) := by
      simpa only [Fintype.card_coe] using hb
    exact_mod_cast hnat
  refine ⟨e, he, ?_, ?_⟩
  · calc
      _ ≤ ∑ _χ : Ch, Ct ^ Fintype.card A := Finset.sum_le_sum (fun χ _ => hmass χ)
      _ = (Fintype.card Ch : ℝ) * Ct ^ Fintype.card A := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (pow_nonneg hCtNonneg _)
  · intro x z outPoint
    rw [← Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _χ : Ch, δout := by
        apply Finset.sum_le_sum
        intro χ _
        rw [← sub_mul, norm_mul, norm_star, AddChar.norm_apply, mul_one]
        simp_rw [forecastInactive_principal_characteristic_residue]
        exact herr χ x z
      _ = (Fintype.card Ch : ℝ) * δout := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hδout.le

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} : type_of% @OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_retained_character_sites_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} := @OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_retained_character_sites_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7}
