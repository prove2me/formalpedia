-- Prove2me | solution 1 for OAI.Erdos970.WeightedTorusJets.source_biquadratic_arithmetic_of_field_ne_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:51:04.465824+00:00
-- url     : https://prove2.me/submissions/d3f57b4c-a141-4769-8dbb-bf0d5b171b96

import Mathlib
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.Basic
import Definitions.Def_OAIQ247J001
import Definitions.Def_OAIQ247J002
import Definitions.Def_OAIQ247J005
import Theorems.Thm_OAI_Erdos970_WeightedTorusJets_characterField_changeLevel_discr_natAbs_jb247

section
-- module Solutions.OAIQ247_JB.Compat
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `Int.sq_emod_four`: an integer square is `0` or `1` mod 4, according to parity. -/
theorem _root_.Int.sq_emod_four (x : ℤ) : x ^ 2 % 4 = x % 2 := by
  have h : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  rcases h with h | h | h | h <;>
    simp [pow_two, Int.mul_emod, h] <;> omega

/-- Mathlib d13f23b's `Int.squarefree_iff_prime_sq_not_dvd`. -/
theorem _root_.Int.squarefree_iff_prime_sq_not_dvd {n : ℤ} :
    Squarefree n ↔ ∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ^ 2 ∣ n) := by
  rw [← Int.squarefree_natAbs, Nat.squarefree_iff_prime_squarefree]
  refine forall_congr' fun p => imp_congr_right fun hp => not_congr ?_
  rw [pow_two, ← Nat.cast_mul, Int.natCast_dvd]

theorem _root_.Int.isFundamentalDiscr_iff_squarefree {D : ℤ} :
    Int.IsFundamentalDiscr D ↔
      (D % 4 = 1 ∧ Squarefree D) ∨ ∃ d : ℤ, D = 4 * d ∧ Squarefree d ∧ (d % 4 = 2 ∨ d % 4 = 3) :=
  Iff.rfl

theorem _root_.Int.isFundamentalDiscr_four_mul {d : ℤ} :
    Int.IsFundamentalDiscr (4 * d) ↔ Squarefree d ∧ (d % 4 = 2 ∨ d % 4 = 3) := by
  constructor
  · rintro (⟨h, _⟩ | ⟨e, he, hs, h⟩)
    · omega
    · have : e = d := by omega
      subst this; exact ⟨hs, h⟩
  · rintro ⟨hs, h⟩
    exact Or.inr ⟨d, rfl, hs, h⟩

end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_BiquadraticBasis
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
open scoped Pointwise
namespace WeightedTorusJets

theorem biquadratic_monomials_integral {E : Type*} [CommRing E] [Algebra ℤ E]
    (a b : E) (d e : ℤ) (ha : a ^ 2 = d) (hb : b ^ 2 = e) :
    IsIntegral ℤ (1 : E) ∧ IsIntegral ℤ a ∧ IsIntegral ℤ b ∧ IsIntegral ℤ (a * b) := by
  have hai : IsIntegral ℤ a := IsIntegral.of_pow (by decide : 0 < 2)
    (ha ▸ isIntegral_intCast d)
  have hbi : IsIntegral ℤ b := IsIntegral.of_pow (by decide : 0 < 2)
    (hb ▸ isIntegral_intCast e)
  exact ⟨isIntegral_one, hai, hbi, hai.mul hbi⟩



open Module

variable {K : Type*} [Field K] [Algebra ℚ K]

lemma biquadraticSignEquiv_basis (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e)
    (s t : Bool) (i : Fin 4) :
    biquadraticSignEquiv v a b d e hv ha hb s t (v i) =
      ![1, if s then -a else a, if t then -b else b,
        (if s then -a else a) * (if t then -b else b)] i :=
  biquadraticLinearMap_basis v _ _ i

lemma biquadratic_algEquiv_ext (v : Basis (Fin 4) ℚ K) (a b : K)
    (hv : ∀ i, v i = ![1, a, b, a * b] i) (f g : K ≃ₐ[ℚ] K)
    (ha : f a = g a) (hb : f b = g b) : f = g := by
  apply AlgEquiv.toLinearMap_injective
  apply v.ext
  intro i
  change f (v i) = g (v i)
  rw [hv i]
  fin_cases i <;> simp_all

lemma quadratic_algEquiv_dichotomy (a : K) (d : ℚ)
    (ha : a * a = algebraMap ℚ K d) (f : K ≃ₐ[ℚ] K) :
    f a = a ∨ f a = -a := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  simpa only [pow_two, ← map_mul, ha] using f.commutes d

lemma biquadratic_automorphism_eq_sign (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e)
    (f : K ≃ₐ[ℚ] K) :
    ∃ s t : Bool, f = biquadraticSignEquiv v a b d e hv ha hb s t := by
  have hs (s t : Bool) (i : Fin 4) := biquadraticSignEquiv_basis v a b d e hv ha hb s t i
  simp_rw [hv] at hs
  rcases quadratic_algEquiv_dichotomy a d ha f with hfa | hfa <;>
    rcases quadratic_algEquiv_dichotomy b e hb f with hfb | hfb
  · refine ⟨false, false, biquadratic_algEquiv_ext v a b hv f _ ?_ ?_⟩
    · exact hfa.trans (hs false false 1).symm
    · exact hfb.trans (hs false false 2).symm
  · refine ⟨false, true, biquadratic_algEquiv_ext v a b hv f _ ?_ ?_⟩
    · exact hfa.trans (hs false true 1).symm
    · exact hfb.trans (hs false true 2).symm
  · refine ⟨true, false, biquadratic_algEquiv_ext v a b hv f _ ?_ ?_⟩
    · exact hfa.trans (hs true false 1).symm
    · exact hfb.trans (hs true false 2).symm
  · refine ⟨true, true, biquadratic_algEquiv_ext v a b hv f _ ?_ ?_⟩
    · exact hfa.trans (hs true true 1).symm
    · exact hfb.trans (hs true true 2).symm

lemma biquadraticSignEquiv_injective (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e) :
    Function.Injective (fun st : Bool × Bool =>
      biquadraticSignEquiv v a b d e hv ha hb st.1 st.2) := by
  let : CharZero K := algebraRat.charZero K
  have ha0 : a ≠ 0 := by simpa [hv] using v.ne_zero 1
  have hb0 : b ≠ 0 := by simpa [hv] using v.ne_zero 2
  have hana : a ≠ -a := fun h => ha0 (CharZero.eq_neg_self_iff.mp h)
  have hbna : b ≠ -b := fun h => hb0 (CharZero.eq_neg_self_iff.mp h)
  have hs (s t : Bool) (i : Fin 4) := biquadraticSignEquiv_basis v a b d e hv ha hb s t i
  simp_rw [hv] at hs
  intro st st' h
  have hA := congrArg (fun f : K ≃ₐ[ℚ] K => f a) h
  have hB := congrArg (fun f : K ≃ₐ[ℚ] K => f b) h
  have hsA (s t : Bool) : biquadraticSignEquiv v a b d e hv ha hb s t a =
      if s then -a else a := hs s t 1
  have hsB (s t : Bool) : biquadraticSignEquiv v a b d e hv ha hb s t b =
      if t then -b else b := hs s t 2
  simp only [hsA] at hA
  simp only [hsB] at hB
  clear hs hsA hsB h
  rcases st with ⟨s, t⟩
  rcases st' with ⟨s', t'⟩
  cases s <;> cases s' <;> cases t <;> cases t' <;> simp_all

lemma biquadratic_card_automorphisms (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e) :
    Nat.card (K ≃ₐ[ℚ] K) = 4 := by
  let f := fun st : Bool × Bool => biquadraticSignEquiv v a b d e hv ha hb st.1 st.2
  have hf : Function.Bijective f := by
    refine ⟨biquadraticSignEquiv_injective v a b d e hv ha hb, ?_⟩
    intro g
    obtain ⟨s, t, h⟩ := biquadratic_automorphism_eq_sign v a b d e hv ha hb g
    exact ⟨⟨s, t⟩, h.symm⟩
  simpa using (Nat.card_congr (Equiv.ofBijective f hf)).symm

lemma biquadratic_isGalois (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e) :
    IsGalois ℚ K := by
  let : FiniteDimensional ℚ K := Module.Finite.of_basis v
  apply IsGalois.of_card_aut_eq_finrank
  rw [biquadratic_card_automorphisms v a b d e hv ha hb, Module.finrank_eq_card_basis v]
  rfl

lemma biquadraticSignEquiv_mul (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e)
    (s t s' t' : Bool) :
    biquadraticSignEquiv v a b d e hv ha hb s t *
        biquadraticSignEquiv v a b d e hv ha hb s' t' =
      biquadraticSignEquiv v a b d e hv ha hb (s.xor s') (t.xor t') := by
  have hs (s t : Bool) (i : Fin 4) := biquadraticSignEquiv_basis v a b d e hv ha hb s t i
  simp_rw [hv] at hs
  have hsA (s t : Bool) : biquadraticSignEquiv v a b d e hv ha hb s t a =
      if s then -a else a := hs s t 1
  have hsB (s t : Bool) : biquadraticSignEquiv v a b d e hv ha hb s t b =
      if t then -b else b := hs s t 2
  apply biquadratic_algEquiv_ext v a b hv
  · cases s <;> cases s' <;> simp [AlgEquiv.mul_apply, hsA]
  · cases t <;> cases t' <;> simp [AlgEquiv.mul_apply, hsB]

lemma biquadratic_automorphisms_commute (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e)
    (f g : K ≃ₐ[ℚ] K) : Commute f g := by
  obtain ⟨s, t, rfl⟩ := biquadratic_automorphism_eq_sign v a b d e hv ha hb f
  obtain ⟨s', t', rfl⟩ := biquadratic_automorphism_eq_sign v a b d e hv ha hb g
  change _ = _
  simp only [biquadraticSignEquiv_mul, Bool.xor_comm]

lemma biquadraticSignEquiv_identity (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e) :
    biquadraticSignEquiv v a b d e hv ha hb false false = 1 := by
  have hs (i : Fin 4) := biquadraticSignEquiv_basis v a b d e hv ha hb false false i
  simp_rw [hv] at hs
  apply biquadratic_algEquiv_ext v a b hv
  · exact hs 1
  · exact hs 2

lemma biquadratic_four_automorphisms (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e)
    (f : K ≃ₐ[ℚ] K) :
    let σ := biquadraticSignEquiv v a b d e hv ha hb true false
    let τ := biquadraticSignEquiv v a b d e hv ha hb false true
    f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ := by
  dsimp
  obtain ⟨s, t, rfl⟩ := biquadratic_automorphism_eq_sign v a b d e hv ha hb f
  cases s <;> cases t <;>
    simp [biquadraticSignEquiv_mul, biquadraticSignEquiv_identity]

end WeightedTorusJets
namespace WeightedTorusJets

lemma sqrtPair_isGalois {L : Type*} [Field L] [CharZero L]
    (a b : L) (d e : ℚ) (ha : a ^ 2 = algebraMap ℚ L d)
    (hb : b ^ 2 = algebraMap ℚ L e) (hd : ¬ IsSquare d) (he : ¬ IsSquare e)
    (hne : IntermediateField.adjoin ℚ {a} ≠ IntermediateField.adjoin ℚ {b}) :
    IsGalois ℚ (IntermediateField.adjoin ℚ ({a, b} : Set L)) := by
  let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
  let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let v := sqrtPairBasis a b d e ha hb hd he hne
  have hv (i : Fin 4) : v i = ![1, a', b', a' * b'] i := by
    apply Subtype.ext
    change (sqrtPairBasis a b d e ha hb hd he hne i : L) = _
    rw [coe_sqrtPairBasis_apply]
    fin_cases i <;> rfl
  have ha' : a' * a' = algebraMap ℚ B d := by
    apply Subtype.ext
    simpa [a', pow_two] using ha
  have hb' : b' * b' = algebraMap ℚ B e := by
    apply Subtype.ext
    simpa [b', pow_two] using hb
  exact biquadratic_isGalois v a' b' d e hv ha' hb'

lemma sqrtPair_four_automorphisms {L : Type*} [Field L] [CharZero L]
    (a b : L) (d e : ℚ) (ha : a ^ 2 = algebraMap ℚ L d)
    (hb : b ^ 2 = algebraMap ℚ L e) (hd : ¬ IsSquare d) (he : ¬ IsSquare e)
    (hne : IntermediateField.adjoin ℚ {a} ≠ IntermediateField.adjoin ℚ {b}) :
    let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
    let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    ∃ σ τ : B ≃ₐ[ℚ] B,
      σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
      Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
      (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
      (∀ f g : B ≃ₐ[ℚ] B, Commute f g) := by
  dsimp
  let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
  let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let v := sqrtPairBasis a b d e ha hb hd he hne
  have hv (i : Fin 4) : v i = ![1, a', b', a' * b'] i := by
    apply Subtype.ext
    change (sqrtPairBasis a b d e ha hb hd he hne i : L) = _
    rw [coe_sqrtPairBasis_apply]
    fin_cases i <;> rfl
  have ha' : a' * a' = algebraMap ℚ B d := by
    apply Subtype.ext
    simpa [a', pow_two] using ha
  have hb' : b' * b' = algebraMap ℚ B e := by
    apply Subtype.ext
    simpa [b', pow_two] using hb
  let σ := biquadraticSignEquiv v a' b' d e hv ha' hb' true false
  let τ := biquadraticSignEquiv v a' b' d e hv ha' hb' false true
  have hs (s t : Bool) (i : Fin 4) :=
    biquadraticSignEquiv_basis v a' b' d e hv ha' hb' s t i
  simp_rw [hv] at hs
  refine ⟨σ, τ, hs true false 1, hs true false 2, hs false true 1,
    hs false true 2, biquadratic_card_automorphisms v a' b' d e hv ha' hb', ?_, ?_⟩
  · exact biquadratic_four_automorphisms v a' b' d e hv ha' hb'
  · exact biquadratic_automorphisms_commute v a' b' d e hv ha' hb'

end WeightedTorusJets

open scoped NumberField

namespace WeightedTorusJets

theorem ringOfIntegers_map_dvd_iff
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    (f : K →ₐ[ℚ] L) (a b : 𝓞 K) :
    NumberField.RingOfIntegers.mapRingHom f.toRingHom a ∣
      NumberField.RingOfIntegers.mapRingHom f.toRingHom b ↔ a ∣ b := by
  let F := NumberField.RingOfIntegers.mapRingHom f.toRingHom
  have hF : Function.Injective F := by
    intro x y h
    apply NumberField.RingOfIntegers.ext
    apply f.injective
    exact congrArg (fun z : 𝓞 L ↦ (z : L)) h
  refine ⟨fun h ↦ ?_, fun h ↦ map_dvd F h⟩
  change F a ∣ F b at h
  by_cases ha : a = 0
  · subst a
    rw [map_zero, zero_dvd_iff] at h
    have hb : b = 0 := hF (h.trans (map_zero F).symm)
    simp [hb]
  · have haK : (a : K) ≠ 0 := fun h ↦ ha (NumberField.RingOfIntegers.ext h)
    have haL : f (a : K) ≠ 0 := fun h ↦ haK (f.injective (h.trans (map_zero f).symm))
    obtain ⟨c, hc⟩ := h
    have hquot : f ((b : K) / (a : K)) = (c : L) := by
      rw [map_div₀, div_eq_iff haL]
      simpa [F, map_mul, mul_comm] using congrArg (fun z : 𝓞 L ↦ (z : L)) hc
    have hint : IsIntegral ℤ ((b : K) / (a : K)) := by
      apply (isIntegral_algHom_iff (f.restrictScalars ℤ) f.injective).mp
      change IsIntegral ℤ (f ((b : K) / (a : K)))
      rw [hquot]
      exact c.2
    refine ⟨⟨(b : K) / (a : K), hint⟩, ?_⟩
    apply NumberField.RingOfIntegers.ext
    change (b : K) = (a : K) * ((b : K) / (a : K))
    rw [mul_comm, div_mul_cancel₀ _ haK]

theorem frobenius_congruence_descends
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    (f : K →ₐ[ℚ] L) (σ : K ≃ₐ[ℚ] K) (τ : L ≃ₐ[ℚ] L)
    (hcomm : ∀ x : K, f (σ x) = τ (f x)) (p : ℕ)
    (hfrob : ∀ y : 𝓞 L, (p : 𝓞 L) ∣ y ^ p - τ • y) (x : 𝓞 K) :
    (p : 𝓞 K) ∣ x ^ p - σ • x := by
  let F := NumberField.RingOfIntegers.mapRingHom f.toRingHom
  have hmap : F (σ • x) = τ • F x := by
    apply NumberField.RingOfIntegers.ext
    exact hcomm (x : K)
  apply (ringOfIntegers_map_dvd_iff f (p : 𝓞 K) (x ^ p - σ • x)).mp
  change F (p : 𝓞 K) ∣ F (x ^ p - σ • x)
  simpa only [map_natCast, map_sub, map_pow, hmap] using hfrob (F x)

end WeightedTorusJets

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_IntegerCharacter
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem oai_compat_exists_sq_mul_squarefree_int (z : ℤ) :
    ∃ t u : ℤ, t ^ 2 * u = z ∧ Squarefree u := by
  obtain ⟨a, b, hab, ha⟩ := Nat.sq_mul_squarefree z.natAbs
  rcases Int.natAbs_eq z with hz | hz
  · refine ⟨b, a, ?_, Int.squarefree_natCast.mpr ha⟩
    rw [hz, ← hab]
    push_cast
    ring
  · refine ⟨b, -a, ?_, Int.squarefree_natAbs.mp (by simpa using ha)⟩
    rw [hz, ← hab]
    push_cast
    ring

theorem oai_compat_adjoin_simple_mul_algebraMap {F E : Type*} [Field F] [Field E] [Algebra F E]
    (x : E) (r : F) (hr : r ≠ 0) :
    IntermediateField.adjoin F {x * algebraMap F E r} = IntermediateField.adjoin F {x} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact mul_mem (IntermediateField.mem_adjoin_simple_self F x)
      (IntermediateField.algebraMap_mem _ r)
  · rw [IntermediateField.adjoin_simple_le_iff]
    convert mul_mem (IntermediateField.mem_adjoin_simple_self F (x * algebraMap F E r))
      (IntermediateField.algebraMap_mem _ r⁻¹) using 1
    rw [mul_assoc, ← map_mul, mul_inv_cancel₀ hr, map_one, mul_one]

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
namespace WeightedTorusJets

open AddChar MulChar

theorem primitive_gaussSum_mul_inv {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] [IsDomain R]
    {χ : DirichletCharacter R q} (hχ : χ.IsPrimitive)
    {e : AddChar (ZMod q) R} (he : e.IsPrimitive) :
    gaussSum χ e * gaussSum χ⁻¹ e⁻¹ = q := by
  classical
  calc
    gaussSum χ e * gaussSum χ⁻¹ e⁻¹ =
        ∑ a : ZMod q, gaussSum χ (e.mulShift a) * e (-a) := by
      simp_rw [gaussSum_mulShift_of_isPrimitive e hχ]
      change gaussSum χ e * (∑ a : ZMod q, χ⁻¹ a * e (-a)) = _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ b : ZMod q, χ b * ∑ a : ZMod q, e (a * (b - 1)) := by
      simp only [gaussSum, mulShift_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      funext b
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_assoc, ← e.map_add_eq_mul]
      congr 2
      ring
    _ = q := by
      simp_rw [sum_mulShift _ he]
      simp [sub_eq_zero]

theorem primitive_quadratic_gaussSum_sq {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] [IsDomain R]
    {χ : DirichletCharacter R q} (hχ : χ.IsPrimitive) (hquad : χ.IsQuadratic)
    {e : AddChar (ZMod q) R} (he : e.IsPrimitive) :
    gaussSum χ e ^ 2 = χ (-1) * q := by
  rw [pow_two, ← primitive_gaussSum_mul_inv hχ he, hquad.inv, mul_rotate']
  congr 1
  rw [mul_comm, ← gaussSum_mulShift χ e (-1 : (ZMod q)ˣ), e.inv_mulShift]
  rfl

theorem primitive_gaussSum_ne_zero {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {χ : DirichletCharacter R q} (hχ : χ.IsPrimitive)
    {e : AddChar (ZMod q) R} (he : e.IsPrimitive) : gaussSum χ e ≠ 0 := by
  intro h
  have hq := primitive_gaussSum_mul_inv hχ he
  rw [h, zero_mul] at hq
  exact (Nat.cast_ne_zero.mpr (NeZero.ne q)) hq.symm

theorem primitive_quadratic_gaussSum_integer_square {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] [IsDomain R]
    {χ : DirichletCharacter R q} (hχ : χ.IsPrimitive) (hquad : χ.IsQuadratic)
    {e : AddChar (ZMod q) R} (he : e.IsPrimitive) :
    ∃ D : ℤ, D.natAbs = q ∧ gaussSum χ e ^ 2 = (D : R) := by
  have hnonzero : χ (-1) ≠ 0 := (isUnit_neg_one.map χ).ne_zero
  rcases hquad (-1) with h | h | h
  · exact (hnonzero h).elim
  · exact ⟨q, by simp, by simp [primitive_quadratic_gaussSum_sq hχ hquad he, h]⟩
  · exact ⟨-q, by simp, by simp [primitive_quadratic_gaussSum_sq hχ hquad he, h]⟩

end WeightedTorusJets

namespace WeightedTorusJets

theorem factorsThrough_ringHomComp_iff {q d : ℕ} [NeZero q]
    {R S : Type*} [CommRing R] [CommRing S] (χ : DirichletCharacter R q)
    (f : R →+* S) (hf : Function.Injective f) :
    DirichletCharacter.FactorsThrough (χ.ringHomComp f) d ↔ χ.FactorsThrough d := by
  by_cases hd : d ∣ q
  · rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd,
      DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
    change (∀ a, a ∈ (ZMod.unitsMap hd).ker → _ = 1) ↔
      (∀ a, a ∈ (ZMod.unitsMap hd).ker → _ = 1)
    simp only [← Units.val_inj, MulChar.coe_toUnitHom, Units.val_one,
      MulChar.ringHomComp_apply, ← f.map_one, hf.eq_iff]
  · exact iff_of_false (fun h ↦ hd h.dvd) (fun h ↦ hd h.dvd)

theorem conductor_ringHomComp {q : ℕ} [NeZero q]
    {R S : Type*} [CommRing R] [CommRing S] (χ : DirichletCharacter R q)
    (f : R →+* S) (hf : Function.Injective f) :
    DirichletCharacter.conductor (χ.ringHomComp f) = χ.conductor := by
  unfold DirichletCharacter.conductor
  congr 1
  ext d
  exact factorsThrough_ringHomComp_iff χ f hf

theorem integerCharacter_ringHomComp {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) :
    (integerCharacter χ hquad).ringHomComp (Int.castRingHom ℂ) = χ := by
  ext a
  exact integerCharacter_cast χ hquad a

theorem integerCharacter_isPrimitive {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) (hprim : χ.IsPrimitive) :
    (integerCharacter χ hquad).IsPrimitive := by
  change DirichletCharacter.conductor (integerCharacter χ hquad) = q
  rw [← conductor_ringHomComp (integerCharacter χ hquad) (Int.castRingHom ℂ)
    (Int.cast_injective (α := ℂ)), integerCharacter_ringHomComp]
  exact hprim

theorem integerCharacter_isQuadratic {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) : (integerCharacter χ hquad).IsQuadratic := by
  apply MulChar.isQuadratic_iff_sq_eq_one.mpr
  apply MulChar.injective_ringHomComp (f := Int.castRingHom ℂ) (Int.cast_injective (α := ℂ))
  dsimp only
  rw [← MulChar.ringHomComp_pow, integerCharacter_ringHomComp,
    MulChar.ringHomComp_one, hquad.sq_eq_one]



open NumberField IsCyclotomicExtension.Rat

theorem cyclotomic_gaussSum_action {n : ℕ} [NeZero n] {K : Type*}
    [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    (χ : DirichletCharacter K n) (hχ : χ.IsQuadratic)
    (e : AddChar (ZMod n) K) (σ : Gal(K/ℚ)) :
    σ (gaussSum χ e) = χ (galEquivZMod n K σ) * gaussSum χ e := by
  have hroot (x : ZMod n) : e x ^ n = 1 := by
    rw [← e.map_nsmul_eq_pow, nsmul_eq_mul]
    simp
  have he (x : ZMod n) : σ (e x) = e ((galEquivZMod n K σ) * x) := by
    rw [galEquivZMod_apply_of_pow_eq n K σ (hroot x), ← e.map_nsmul_eq_pow,
      nsmul_eq_mul, ZMod.natCast_zmod_val]
  calc
    σ (gaussSum χ e) = gaussSum χ (e.mulShift (galEquivZMod n K σ)) := by
      simp only [gaussSum, map_sum, map_mul, AddChar.mulShift_apply]
      apply Finset.sum_congr rfl
      intro x _
      rw [he]
      congr 1
      rcases hχ x with h | h | h <;> simp [h]
    _ = χ (galEquivZMod n K σ) * gaussSum χ e := by
      rw [gaussSum_mulShift_eq, hχ.inv]

end WeightedTorusJets

namespace WeightedTorusJets

open NumberField IsCyclotomicExtension.Rat

variable (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] [IsAbelianGalois ℚ K]
    (R : Type*) [CommRing R] [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]

theorem characterField_finrank (χ : DirichletCharacter R n) (hχ : χ.IsQuadratic)
    (hne : χ ≠ 1) : Module.finrank ℚ (characterField n K R χ) = 2 := by
  rw [← card_intermediateFieldEquivSubgroupChar n K R, characterField,
    OrderIso.apply_symm_apply, Nat.card_zpowers]
  exact orderOf_eq_prime hχ.sq_eq_one hne

theorem mem_characterField_fixingSubgroup (χ : DirichletCharacter R n)
    (hχ : χ.IsQuadratic) (σ : Gal(K/ℚ)) :
    σ ∈ (characterField n K R χ).fixingSubgroup ↔ χ (galEquivZMod n K σ) = 1 := by
  change σ ∈ (IntermediateField.fixedField
    ((subgroupGalEquivSubgroupChar n K R).symm
      (OrderDual.toDual (Subgroup.zpowers χ)))).fixingSubgroup ↔ _
  rw [IntermediateField.fixingSubgroup_fixedField, mem_subgroupGalEquivSubgroupChar_symm_iff]
  constructor
  · intro h
    exact h χ (Subgroup.mem_zpowers χ)
  · intro h ψ hψ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hψ
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · simp only [zpow_natCast, MulChar.pow_apply_coe, h, one_pow]
    · simp only [zpow_neg, zpow_natCast, ← inv_pow, hχ.inv, MulChar.pow_apply_coe, h, one_pow]

theorem characterField_changeLevel [IsDomain R] {m : ℕ} [NeZero m]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {m} ℚ L]
    [IsAbelianGalois ℚ L] [Algebra K L] [IsScalarTower ℚ K L]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod m)ˣ)]
    (hdiv : n ∣ m) (χ : DirichletCharacter R n) (hχ : χ.IsQuadratic) :
    characterField m L R (DirichletCharacter.changeLevel hdiv χ) =
      (characterField n K R χ).map (IsScalarTower.toAlgHom ℚ K L) := by
  have hχ' : (DirichletCharacter.changeLevel hdiv χ).IsQuadratic := by
    rw [MulChar.isQuadratic_iff_sq_eq_one, ← map_pow, hχ.sq_eq_one, map_one]
  apply (IsGalois.intermediateFieldEquivSubgroup (F := ℚ) (E := L)).injective
  change (characterField m L R (DirichletCharacter.changeLevel hdiv χ)).fixingSubgroup =
    ((characterField n K R χ).map (IsScalarTower.toAlgHom ℚ K L)).fixingSubgroup
  ext σ
  have hm : σ ∈ ((characterField n K R χ).map
      (IsScalarTower.toAlgHom ℚ K L)).fixingSubgroup ↔
      σ.restrictNormal K ∈ (characterField n K R χ).fixingSubgroup := by
    simp only [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      apply (algebraMap K L).injective
      rw [AlgEquiv.restrictNormal_commutes]
      exact h _ ⟨x, hx, rfl⟩
    · intro h y hy
      obtain ⟨x, hx, rfl⟩ := hy
      change σ (algebraMap K L x) = algebraMap K L x
      rw [← AlgEquiv.restrictNormal_commutes, h x hx]
  rw [hm, mem_characterField_fixingSubgroup n K R χ hχ,
    mem_characterField_fixingSubgroup m L R _ hχ']
  rw [galEquivZMod_restrictNormal_apply m L K hdiv σ]
  simp [DirichletCharacter.changeLevel_def]

end WeightedTorusJets

namespace WeightedTorusJets

open NumberField IsCyclotomicExtension.Rat

theorem mem_adjoin_fixingSubgroup_iff {F K : Type*} [Field F] [Field K] [Algebra F K]
    (g : K) (σ : Gal(K/F)) :
    σ ∈ (IntermediateField.adjoin F {g}).fixingSubgroup ↔ σ g = g := by
  rw [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le,
    IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff,
    Subgroup.forall_mem_zpowers]
  simpa only [MulAction.mem_fixedBy, AlgEquiv.smul_def] using
    (MulAction.mem_fixedBy_zpowers_iff_mem_fixedBy (g := σ) (a := g))

theorem gaussSum_adjoin_eq_characterField {n : ℕ} [NeZero n] {K : Type*}
    [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] [IsAbelianGalois ℚ K]
    (χ : DirichletCharacter ℤ n) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    (e : AddChar (ZMod n) K) (he : e.IsPrimitive) :
    IntermediateField.adjoin ℚ {gaussSum (χ.ringHomComp (Int.castRingHom K)) e} =
      characterField n K ℂ (χ.ringHomComp (Int.castRingHom ℂ)) := by
  have hprimK : DirichletCharacter.IsPrimitive (χ.ringHomComp (Int.castRingHom K)) := by
    rw [DirichletCharacter.isPrimitive_def, conductor_ringHomComp χ (Int.castRingHom K)
      (Int.cast_injective (α := K))]
    exact hprim
  have hg := primitive_gaussSum_ne_zero hprimK he
  apply IsGalois.intermediateFieldEquivSubgroup.injective
  change (IntermediateField.adjoin ℚ {_}).fixingSubgroup =
    (characterField n K ℂ (χ.ringHomComp (Int.castRingHom ℂ))).fixingSubgroup
  ext σ
  rw [mem_adjoin_fixingSubgroup_iff, mem_characterField_fixingSubgroup _ _ _ _
    (hχ.comp (Int.castRingHom ℂ)), cyclotomic_gaussSum_action _
    (hχ.comp (Int.castRingHom K)), mul_eq_right₀ hg]
  change ((χ (galEquivZMod n K σ) : K) = 1) ↔
    ((χ (galEquivZMod n K σ) : ℂ) = 1)
  norm_cast

end WeightedTorusJets

namespace WeightedTorusJets

theorem exists_squarefree_generator {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    {D : ℤ} (hD : D ≠ 0) {g : K} (hg : g ^ 2 = (D : K)) :
    ∃ (d c : ℤ) (a : K), Squarefree d ∧ d.natAbs ≤ D.natAbs ∧ c ≠ 0 ∧
      D = c ^ 2 * d ∧ a ^ 2 = (d : K) ∧ IsIntegral ℤ a ∧ g = (c : K) * a ∧
      IntermediateField.adjoin ℚ {a} = IntermediateField.adjoin ℚ {g} := by
  obtain ⟨c, d, hcd, hd⟩ := oai_compat_exists_sq_mul_squarefree_int D
  have hc : c ≠ 0 := by
    intro h
    apply hD
    rw [← hcd, h]
    simp
  have hcK : (c : K) ≠ 0 := Int.cast_ne_zero.mpr hc
  have had : (g / (c : K)) ^ 2 = (d : K) := by
    rw [div_pow, hg, ← hcd]
    push_cast
    exact mul_div_cancel_left₀ _ (pow_ne_zero 2 hcK)
  refine ⟨d, c, g / (c : K), hd, ?_, hc, hcd.symm, had, ?_, ?_, ?_⟩
  · apply Nat.le_of_dvd (Int.natAbs_pos.mpr hD)
    exact Int.natAbs_dvd_natAbs.mpr ⟨c ^ 2, by rw [← hcd, mul_comm]⟩
  · apply IsIntegral.of_pow (by decide : 0 < 2)
    rw [had]
    exact isIntegral_algebraMap
  · exact (mul_div_cancel₀ g hcK).symm
  · simpa only [div_eq_mul_inv, map_inv₀, map_intCast] using
      oai_compat_adjoin_simple_mul_algebraMap (F := ℚ) g ((c : ℚ)⁻¹)
        (inv_ne_zero (Int.cast_ne_zero.mpr hc))



open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat

theorem not_isSquare_of_quadratic_adjoin {K : Type*} [Field K] [Algebra ℚ K]
    {d : ℤ} {a : K} (ha : a ^ 2 = (d : K))
    (hdim : Module.finrank ℚ (IntermediateField.adjoin ℚ {a}) = 2) :
    ¬ IsSquare (d : ℚ) := by
  rintro ⟨r, hr⟩
  have hs : a ^ 2 = (algebraMap ℚ K r) ^ 2 := by
    calc
      a ^ 2 = (d : K) := ha
      _ = algebraMap ℚ K (d : ℚ) := by simp
      _ = (algebraMap ℚ K r) ^ 2 := by rw [hr, map_mul, pow_two]
  have hmem : a ∈ (⊥ : IntermediateField ℚ K) := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with h | h
    · rw [h]
      exact IntermediateField.algebraMap_mem _ _
    · rw [h]
      exact (⊥ : IntermediateField ℚ K).neg_mem (IntermediateField.algebraMap_mem _ _)
  rw [IntermediateField.adjoin_simple_eq_bot_iff.mpr hmem,
    IntermediateField.finrank_bot] at hdim
  norm_num at hdim

theorem exists_squarefree_characterField_generator {n : ℕ} [NeZero n] {K : Type*}
    [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] [IsAbelianGalois ℚ K]
    (χ : DirichletCharacter ℂ n) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    (hne : χ ≠ 1) :
    ∃ (d : ℤ) (a : K), Squarefree d ∧ d.natAbs ≤ n ∧ d.natAbs ∣ n ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : K) ∧
      IsIntegral ℤ a ∧ IntermediateField.adjoin ℚ {a} = characterField n K ℂ χ ∧
      ∀ σ : Gal(K/ℚ), σ a = (integerCharacter χ hχ (galEquivZMod n K σ) : K) * a := by
  let χI := integerCharacter χ hχ
  let χK := χI.ringHomComp (Int.castRingHom K)
  have hI := integerCharacter_isQuadratic χ hχ
  have hpI := integerCharacter_isPrimitive χ hχ hprim
  have hK : χK.IsQuadratic := hI.comp (Int.castRingHom K)
  have hpK : DirichletCharacter.IsPrimitive χK := by
    rw [DirichletCharacter.isPrimitive_def, conductor_ringHomComp χI (Int.castRingHom K)
      (Int.cast_injective (α := K))]
    exact hpI
  let e := AddChar.zmodChar n (zeta_spec n ℚ K).pow_eq_one
  have he : e.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root n (zeta_spec n ℚ K)
  obtain ⟨D, hDabs, hgD⟩ := primitive_quadratic_gaussSum_integer_square hpK hK he
  have hD : D ≠ 0 := by
    intro h
    have := hDabs
    rw [h, Int.natAbs_zero] at this
    exact (NeZero.ne n) this.symm
  obtain ⟨d, c, a, hd, hbound, hc, hdc, ha, hint, hga, hadj⟩ :=
    exists_squarefree_generator hD hgD
  have hadjχ : IntermediateField.adjoin ℚ {a} = characterField n K ℂ χ := by
    rw [hadj, gaussSum_adjoin_eq_characterField χI hI hpI e he]
    congr 1
    exact integerCharacter_ringHomComp χ hχ
  have hdiv : d.natAbs ∣ n := by
    rw [← hDabs]
    exact Int.natAbs_dvd_natAbs.mpr ⟨c ^ 2, by rw [hdc, mul_comm]⟩
  have hnsq : ¬ IsSquare (d : ℚ) := by
    apply not_isSquare_of_quadratic_adjoin ha
    rw [hadjχ]
    exact characterField_finrank n K ℂ χ hχ hne
  refine ⟨d, a, hd, hDabs ▸ hbound, hdiv, hnsq, ha, hint, hadjχ, ?_⟩
  intro σ
  have hact := cyclotomic_gaussSum_action χK hK e σ
  rw [hga, map_mul, map_intCast] at hact
  apply mul_left_cancel₀ (Int.cast_ne_zero.mpr hc : (c : K) ≠ 0)
  change (c : K) * σ a = (χI (galEquivZMod n K σ) : K) * ((c : K) * a) at hact
  simpa only [χI, mul_left_comm] using hact

end WeightedTorusJets

namespace WeightedTorusJets

open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat

theorem galEquivZMod_arithFrob (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] {p : ℕ} (hp : p.Prime) (hpn : p.Coprime n)
    (P : Ideal (𝓞 K)) (hP : P.under ℤ = Ideal.span {(p : ℤ)})
    (σ : Gal(K/ℚ)) (hσ : IsArithFrobAt ℤ σ P) :
    galEquivZMod n K σ = ZMod.unitOfCoprime p hpn := by
  have hn : (n : 𝓞 K) ∉ P := by
    intro hn
    have hn' : (n : ℤ) ∈ P.under ℤ := by simpa [Ideal.under, Ideal.mem_comap] using hn
    rw [hP, Ideal.mem_span_singleton] at hn'
    exact hp.not_dvd_one (hpn ▸ Nat.dvd_gcd (dvd_refl p) (Int.natCast_dvd_natCast.mp hn'))
  have hc : Nat.card (ℤ ⧸ P.under ℤ) = p := by
    rw [hP, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  let ζ := (zeta_spec n ℚ K).toInteger
  have hζ : IsPrimitiveRoot ζ n := (zeta_spec n ℚ K).toInteger_isPrimitiveRoot
  have he : ζ ^ (galEquivZMod n K σ).val.val = ζ ^ p := by
    rw [← galEquivZMod_smul_of_pow_eq n K σ hζ.pow_eq_one]
    simpa only [hc, MulSemiringAction.toAlgHom_apply] using hσ.apply_of_pow_eq_one hζ.pow_eq_one hn
  have hmod := (hζ.isOfFinOrder (NeZero.ne n)).pow_inj_mod.mp he
  rw [← hζ.eq_orderOf] at hmod
  apply Units.ext
  rw [ZMod.coe_unitOfCoprime, ← ZMod.natCast_zmod_val (galEquivZMod n K σ).val]
  exact (ZMod.natCast_eq_natCast_iff' _ _ n).mpr hmod

theorem arithFrob_map_character_eigenvector (n m : ℕ) [NeZero n] [NeZero m]
    (K L : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    [Field L] [NumberField L] [IsCyclotomicExtension {m} ℚ L]
    [Algebra K L] [IsScalarTower ℚ K L] (hdiv : n ∣ m)
    (χ : DirichletCharacter ℤ n) (a : K)
    (ha : ∀ τ : Gal(K/ℚ), τ a = (χ (galEquivZMod n K τ) : K) * a)
    {p : ℕ} (hp : p.Prime) (hpm : p.Coprime m)
    (P : Ideal (𝓞 L)) (hP : P.under ℤ = Ideal.span {(p : ℤ)})
    (σ : Gal(L/ℚ)) (hσ : IsArithFrobAt ℤ σ P) :
    σ (algebraMap K L a) = (χ p : L) * algebraMap K L a := by
  let : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
  rw [← AlgEquiv.restrictNormal_commutes, ha, map_mul, map_intCast]
  congr 2
  rw [galEquivZMod_restrictNormal_apply m L K hdiv σ,
    galEquivZMod_arithFrob m L hp hpm P hP σ hσ]
  simp [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.cast_natCast hdiv]

end WeightedTorusJets

namespace WeightedTorusJets

open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat

theorem exists_squarefree_generator_frobenius_sign (n m : ℕ) [NeZero n] [NeZero m]
    (K L : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    [IsAbelianGalois ℚ K] [Field L] [NumberField L] [IsCyclotomicExtension {m} ℚ L]
    [Algebra K L] [IsScalarTower ℚ K L] (hdiv : n ∣ m)
    (χ : DirichletCharacter ℂ n) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) (hne : χ ≠ 1) :
    ∃ (d : ℤ) (a : K), Squarefree d ∧ d.natAbs ≤ n ∧ d.natAbs ∣ n ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : K) ∧
      IsIntegral ℤ a ∧ IntermediateField.adjoin ℚ {a} = characterField n K ℂ χ ∧
      ∀ (p : ℕ), p.Prime → p.Coprime m →
        ∀ (P : Ideal (𝓞 L)), P.under ℤ = Ideal.span {(p : ℤ)} →
          ∀ (σ : Gal(L/ℚ)), IsArithFrobAt ℤ σ P → χ p = -1 →
            σ (algebraMap K L a) = -algebraMap K L a := by
  obtain ⟨d, a, hd, hbound, hddiv, hdns, ha, hint, hadj, hact⟩ :=
    exists_squarefree_characterField_generator (K := K) χ hχ hprim hne
  refine ⟨d, a, hd, hbound, hddiv, hdns, ha, hint, hadj, ?_⟩
  intro p hp hpm P hP σ hσ hχp
  have hi : integerCharacter χ hχ (p : ZMod n) = -1 := by
    apply Int.cast_injective (α := ℂ)
    simpa only [Int.cast_neg, Int.cast_one] using
      (integerCharacter_cast χ hχ (p : ZMod n)).trans hχp
  have he := arithFrob_map_character_eigenvector n m K L hdiv
    (integerCharacter χ hχ) a hact hp hpm P hP σ hσ
  simpa only [hi, Int.cast_neg, Int.cast_one, neg_one_mul] using he

end WeightedTorusJets

namespace WeightedTorusJets

open NumberField IsCyclotomicExtension

theorem cyclotomicDivisorField_isCyclotomicExtension (n m : ℕ) [NeZero n] [NeZero m]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {m} ℚ L] (hdiv : n ∣ m) :
    IsCyclotomicExtension {n} ℚ (cyclotomicDivisorField n m L) := by
  have hζ : IsPrimitiveRoot (zeta m ℚ L ^ (m / n)) n :=
    IsPrimitiveRoot.pow (NeZero.pos m) (zeta_spec m ℚ L) (Nat.div_mul_cancel hdiv).symm
  exact hζ.intermediateField_adjoin_isCyclotomicExtension ℚ

end WeightedTorusJets

namespace WeightedTorusJets

theorem primitive_eighth_root_difference_sq {K : Type*} [Field K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 8) : (ζ - ζ ^ 3) ^ 2 = 2 := by
  have h4 : ζ ^ 4 = -1 := by
    apply IsPrimitiveRoot.eq_neg_one_of_two_right
    simpa using hζ.pow_of_dvd (by decide : (4 : ℕ) ≠ 0) (by decide : (4 : ℕ) ∣ 8)
  linear_combination (ζ ^ 2 - 2) * h4

end WeightedTorusJets

open scoped Pointwise

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_SqrtPairFrobeniusDirections
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
open scoped Pointwise
open scoped NumberField
namespace WeightedTorusJets

open scoped NumberField

lemma sqrtPair_frobenius_directions {L : Type*} [Field L] [NumberField L]
    (a b : L) (d e : ℚ) (ha : a ^ 2 = algebraMap ℚ L d)
    (hb : b ^ 2 = algebraMap ℚ L e) (hd : ¬ IsSquare d) (he : ¬ IsSquare e)
    (hne : IntermediateField.adjoin ℚ {a} ≠ IntermediateField.adjoin ℚ {b}) :
    let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
    let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    ∃ σ τ : B ≃ₐ[ℚ] B,
      σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
      Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
      (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
      (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
      ∀ (p : ℕ) (φ : L ≃ₐ[ℚ] L), φ a = -a →
        (∀ y : 𝓞 L, (p : 𝓞 L) ∣ y ^ p - φ • y) →
          ((∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - σ • x) ∨
            (∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - (σ * τ) • x)) := by
  dsimp
  let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
  let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  obtain ⟨σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm⟩ :=
    sqrtPair_four_automorphisms a b d e ha hb hd he hne
  have ha0 : a ≠ 0 := by
    intro h
    have hmap : algebraMap ℚ L d = 0 := by simpa [h] using ha.symm
    have hd0 : d = 0 := (algebraMap ℚ L).injective (hmap.trans (map_zero _).symm)
    exact hd (hd0 ▸ IsSquare.zero)
  have ha'0 : a' ≠ 0 := fun h => ha0 (congrArg (fun x : B => (x : L)) h)
  have ha'neg : a' ≠ -a' := fun h => ha'0 (CharZero.eq_neg_self_iff.mp h)
  refine ⟨σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, ?_⟩
  intro p φ hφ hfrob
  let : IsGalois ℚ B := sqrtPair_isGalois a b d e ha hb hd he hne
  let ψ := φ.restrictNormal B
  have hψcomm (x : B) : B.val (ψ x) = φ (B.val x) :=
    AlgEquiv.restrictNormal_commutes φ B x
  have hψa : ψ a' = -a' := by
    apply Subtype.ext
    exact (hψcomm a').trans hφ
  have hψfrob : ∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - ψ • x :=
    frobenius_congruence_descends B.val ψ φ hψcomm p hfrob
  rcases hall ψ with hψ | hψ | hψ | hψ
  · rw [hψ, AlgEquiv.one_apply] at hψa
    exact (ha'neg hψa).elim
  · exact Or.inl (hψ ▸ hψfrob)
  · rw [hψ, hτa] at hψa
    exact (ha'neg hψa).elim
  · exact Or.inr (hψ ▸ hψfrob)

end WeightedTorusJets

open scoped NumberField

namespace WeightedTorusJets

theorem mem_map_of_forall_mem_primesOver
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] (P : Ideal R) [hP : P.IsMaximal]
    (hunr : Algebra.IsUnramifiedIn S P) {x : S}
    (hx : ∀ (Q : Ideal S) (_ : Q.IsPrime), Q.LiesOver P → x ∈ Q) :
    x ∈ P.map (algebraMap R S) := by
  apply Ideal.mem_of_localization_maximal
  intro Q hQ
  by_cases hle : P.map (algebraMap R S) ≤ Q
  · have hover : Q.LiesOver P := ⟨hP.eq_of_le (Ideal.IsPrime.ne_top' (I := Q.under R))
      (Ideal.map_le_iff_le_comap.mp hle)⟩
    have : Algebra.IsUnramifiedAt R Q := hunr Q inferInstance hover
    let := Localization.AtPrime.algebraOfLiesOver P Q
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      ((Algebra.isUnramifiedAt_iff_map_eq R P Q).mp inferInstance).2]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime Q) Q x).mpr (hx Q inferInstance hover)
  · rw [IsLocalization.AtPrime.map_eq_top_of_not_le _ hle]
    simp

theorem arithFrobAt_eq_of_under_eq
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [CommGroup G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Finite G] [Algebra.IsInvariant R S G]
    (Q Q' : Ideal S) [Q.IsPrime] [Q'.IsPrime]
    [Finite (S ⧸ Q)] [Finite (S ⧸ Q')]
    (h : Q.under R = Q'.under R) :
    arithFrobAt R G Q = arithFrobAt R G Q' :=
  isConj_iff_eq.mp (isConj_arithFrobAt R G Q Q' h)

theorem arithFrobAt_sub_pow_mem_map
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [CommGroup G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Finite G] [Algebra.IsInvariant R S G] [Algebra.EssFiniteType R S]
    [Ring.HasFiniteQuotients S] [FaithfulSMul R S]
    (P : Ideal R) [P.IsMaximal] (hP : P ≠ ⊥)
    (hunr : Algebra.IsUnramifiedIn S P)
    (Q : Ideal S) [Q.IsPrime] [Q.LiesOver P] [Finite (S ⧸ Q)] (x : S) :
    arithFrobAt R G Q • x - x ^ Nat.card (R ⧸ P) ∈ P.map (algebraMap R S) := by
  apply mem_map_of_forall_mem_primesOver P hunr
  intro Q' hQ' hover
  have : Q'.LiesOver P := hover
  have : Finite (S ⧸ Q') := Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.ne_bot_of_liesOver_of_ne_bot hP Q')
  have hbase : Q.under R = Q'.under R := (Q.over_def P).symm.trans (Q'.over_def P)
  rw [arithFrobAt_eq_of_under_eq Q Q' hbase, Q'.over_def P]
  exact IsArithFrobAt.arithFrobAt R G Q' x

theorem prime_dvd_pow_sub_arithFrobAt
    {S G : Type*} [CommRing S] [CommGroup G] [MulSemiringAction G S]
    [SMulCommClass G ℤ S] [Finite G] [Algebra.IsInvariant ℤ S G]
    [Algebra.EssFiniteType ℤ S] [Ring.HasFiniteQuotients S] [CharZero S]
    (p : ℕ) [Fact p.Prime]
    (hunr : Algebra.IsUnramifiedIn S (Ideal.span {(p : ℤ)}))
    (Q : Ideal S) [Q.IsPrime] [Q.LiesOver (Ideal.span {(p : ℤ)})]
    [Finite (S ⧸ Q)] (x : S) :
    (p : S) ∣ x ^ p - arithFrobAt ℤ G Q • x := by
  have hP : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa using (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero : (p : ℤ) ≠ 0)
  have h := arithFrobAt_sub_pow_mem_map (G := G)
    (Ideal.span {(p : ℤ)}) hP hunr Q x
  rw [Int.card_ideal_quot, Ideal.map_span, Set.image_singleton, map_natCast,
    Ideal.mem_span_singleton] at h
  simpa only [neg_sub] using dvd_neg.mpr h

theorem ringOfIntegers_isInvariant
    {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K] :
    Algebra.IsInvariant ℤ (𝓞 K) (K ≃ₐ[ℚ] K) := by
  refine ⟨fun x hx ↦ ?_⟩
  apply (Algebra.isInvariant_of_isGalois ℤ ℚ K (𝓞 K)).isInvariant x
  intro g
  apply NumberField.RingOfIntegers.ext
  change algebraMap (𝓞 K) K (galRestrict ℤ ℚ K (𝓞 K) g x) = algebraMap (𝓞 K) K x
  rw [algebraMap_galRestrict_apply]
  exact congrArg (fun z : 𝓞 K ↦ (z : K)) (hx g)

theorem exists_integer_frobenius_congruence
    {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    (hcomm : ∀ f g : K ≃ₐ[ℚ] K, Commute f g)
    (p : ℕ) [Fact p.Prime]
    (hunr : Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)})) :
    ∃ σ : K ≃ₐ[ℚ] K,
      (∀ (Q : Ideal (𝓞 K)) (_ : Q.IsPrime),
        Q.LiesOver (Ideal.span {(p : ℤ)}) → IsArithFrobAt ℤ σ Q) ∧
      ∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - σ • x := by
  let : CommGroup (K ≃ₐ[ℚ] K) := .mk hcomm
  have : Algebra.IsInvariant ℤ (𝓞 K) (K ≃ₐ[ℚ] K) := ringOfIntegers_isInvariant
  obtain ⟨Q, hQ, hover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 K) (Ideal.span {(p : ℤ)})
  have : Q.LiesOver (Ideal.span {(p : ℤ)}) := hover
  have hp0 : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa using (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero : (p : ℤ) ≠ 0)
  have : Finite ((𝓞 K) ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Q)
  refine ⟨arithFrobAt ℤ (K ≃ₐ[ℚ] K) Q, ?_, prime_dvd_pow_sub_arithFrobAt p hunr Q⟩
  intro Q' hQ' hover'
  have : Q'.LiesOver (Ideal.span {(p : ℤ)}) := hover'
  have : Finite ((𝓞 K) ⧸ Q') := Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Q')
  have hbase : Q.under ℤ = Q'.under ℤ := hover.over.symm.trans hover'.over
  rw [arithFrobAt_eq_of_under_eq Q Q' hbase]
  exact IsArithFrobAt.arithFrobAt ℤ (K ≃ₐ[ℚ] K) Q'



theorem cyclotomic_isUnramifiedIn
    (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] (p : ℕ) [Fact p.Prime] (hpn : ¬ p ∣ n) :
    Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)}) := by
  rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  intro Q hQ hover
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p K Q hpn

theorem exists_cyclotomic_frobenius_congruence
    (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] (p : ℕ) [Fact p.Prime] (hpn : ¬ p ∣ n) :
    ∃ σ : K ≃ₐ[ℚ] K,
      (∀ (Q : Ideal (𝓞 K)) (_ : Q.IsPrime),
        Q.LiesOver (Ideal.span {(p : ℤ)}) → IsArithFrobAt ℤ σ Q) ∧
      ∀ x : 𝓞 K, (p : 𝓞 K) ∣ x ^ p - σ • x := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
  apply exists_integer_frobenius_congruence (p := p)
  · intro σ τ
    change σ * τ = τ * σ
    apply (IsCyclotomicExtension.Rat.galEquivZMod n K).injective
    simp only [map_mul, mul_comm]
  · exact cyclotomic_isUnramifiedIn n K p hpn



theorem not_isSquare_rat_two : ¬ IsSquare (2 : ℚ) := by
  norm_num



theorem real_character_inv {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) : χ⁻¹ = χ := by
  rw [← MulChar.star_eq_inv]
  apply MulChar.ext'
  intro a
  exact Complex.conj_eq_iff_im.mpr (hreal a)

theorem real_character_isQuadratic {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) : χ.IsQuadratic := by
  rw [MulChar.isQuadratic_iff_sq_eq_one]
  calc
    χ ^ 2 = χ⁻¹ * χ := by rw [pow_two, real_character_inv χ hreal]
    _ = 1 := inv_mul_cancel χ



open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero

attribute [local instance] canonicalCyclotomicExtension

attribute [local instance] canonicalCyclotomicNumberField

attribute [local instance] canonicalCyclotomicAbelian



open NumberField IsCyclotomicExtension.Rat

end WeightedTorusJets

open scoped NumberField

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_QuadraticAdjoinBasis
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
namespace WeightedTorusJets

open Module NumberField

theorem trace_norm_quadratic_basis {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d r s : ℚ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) :
    Algebra.trace ℚ K ((r : K) + s * a) = 2 * r ∧
      Algebra.norm ℚ ((r : K) + s * a) = r ^ 2 - d * s ^ 2 := by
  have hu0 : u 0 = 1 := congrFun hu 0
  have hu1 : u 1 = a := congrFun hu 1
  have hr0 : u.repr 1 = Finsupp.single 0 1 := by rw [← hu0, u.repr_self]
  have hr1 : u.repr a = Finsupp.single 1 1 := by rw [← hu1, u.repr_self]
  have hrc (c : ℚ) : u.repr (c : K) = c • Finsupp.single 0 1 := by
    simpa [Algebra.smul_def, hr0] using u.repr.map_smul c (1 : K)
  have hm0 : ((r : K) + s * a) * 1 = r • (1 : K) + s • a := by
    simp [Algebra.smul_def]
  have hm1 : ((r : K) + s * a) * a = (d * s) • (1 : K) + r • a := by
    calc
      _ = (s : K) * a ^ 2 + r * a := by ring
      _ = _ := by rw [ha]; simp [Algebra.smul_def, mul_comm]
  have hmat : Algebra.leftMulMatrix u ((r : K) + s * a) = !![r, d*s; s,r] := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    fin_cases i <;> fin_cases j
    all_goals simp [-Rat.cast_mul, hu0, hu1, hm0, hm1, hrc, hr1]
  rw [Algebra.trace_eq_matrix_trace u, Algebra.norm_eq_matrix_det u, hmat]
  simp [Matrix.trace, Matrix.det_fin_two, Fin.sum_univ_succ]
  constructor <;> ring

theorem rat_int_of_squarefree_mul_sq_eq_int (d n : ℤ) (hd : Squarefree d)
    (x : ℚ) (hx : (d : ℚ) * x ^ 2 = n) : ∃ m : ℤ, x = m := by
  have heq : d * x.num ^ 2 = n * (x.den : ℤ) ^ 2 := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [← x.num_div_den] at hx
    have hden : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
    field_simp at hx
    nlinarith [hx]
  have hdiv : (x.den : ℤ) * (x.den : ℤ) ∣ d * x.num ^ 2 := by
    rw [heq, ← pow_two]
    exact dvd_mul_left _ _
  have hden := hd.dvd_of_squarefree_of_mul_dvd_mul_right hdiv
  have hden_nat : x.den ∣ x.num.natAbs ^ 2 := by
    simpa only [Int.natCast_dvd, Int.natAbs_pow] using hden
  have hone : x.den = 1 := Nat.eq_one_of_dvd_coprimes (x.reduced.pow_left 2)
    hden_nat (dvd_refl _)
  exact ⟨x.num, ((Rat.den_eq_one_iff x).mp hone).symm⟩

theorem integral_quadratic_half_coordinates {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ) (r s : ℚ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d)
    (hx : IsIntegral ℤ ((r : K) + s * a)) :
    ∃ m k : ℤ, 2 * r = m ∧ 2 * s = k ∧ 4 ∣ m ^ 2 - d * k ^ 2 := by
  obtain ⟨ht, hn⟩ := trace_norm_quadratic_basis u a (d : ℚ) r s hu (by simpa using ha)
  have hit : IsIntegral ℤ (2 * r) := ht ▸ Algebra.isIntegral_trace hx
  have hin : IsIntegral ℤ (r ^ 2 - (d : ℚ) * s ^ 2) := hn ▸ Algebra.isIntegral_norm ℚ hx
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hit
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hin
  change (m : ℚ) = 2 * r at hm
  change (n : ℚ) = r ^ 2 - (d : ℚ) * s ^ 2 at hn
  have hsq : (d : ℚ) * (2 * s) ^ 2 = (m ^ 2 - 4 * n : ℤ) := by
    push_cast
    rw [hm, hn]
    ring
  obtain ⟨k, hk⟩ := rat_int_of_squarefree_mul_sq_eq_int d (m ^ 2 - 4 * n) hd (2 * s) hsq
  refine ⟨m, k, hm.symm, hk, n, ?_⟩
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [hm, ← hk, hn]
  ring

theorem even_coordinates_of_four_dvd (d m k : ℤ) (hd : d % 4 = 2 ∨ d % 4 = 3)
    (h : 4 ∣ m ^ 2 - d * k ^ 2) : Even m ∧ Even k := by
  have heq : (m ^ 2 - d * k ^ 2) % 4 = 0 := Int.emod_eq_zero_of_dvd h
  rw [Int.sub_emod, Int.mul_emod, Int.sq_emod_four, Int.sq_emod_four] at heq
  simp only [Int.even_iff]
  rcases hd with hd | hd <;> rw [hd] at heq <;> omega

theorem even_sub_coordinates_of_four_dvd (d m k : ℤ) (hd : d % 4 = 1)
    (h : 4 ∣ m ^ 2 - d * k ^ 2) : Even (m - k) := by
  have heq : (m ^ 2 - d * k ^ 2) % 4 = 0 := Int.emod_eq_zero_of_dvd h
  rw [Int.sub_emod, Int.mul_emod, Int.sq_emod_four, Int.sq_emod_four, hd] at heq
  simp only [Int.even_iff]
  omega

theorem integral_quadratic_eq_int_add_int_mul {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d)
    (hd4 : d % 4 = 2 ∨ d % 4 = 3) (x : K) (hx : IsIntegral ℤ x) :
    ∃ i j : ℤ, x = i + j * a := by
  let r := u.repr x 0
  let s := u.repr x 1
  have hrep : (r : K) + s * a = x := by
    simpa [r, s, hu, Fin.sum_univ_succ, Algebra.smul_def] using u.sum_repr x
  obtain ⟨m, k, hm, hk, hmk⟩ := integral_quadratic_half_coordinates u a d r s hu ha hd
    (by simpa only [hrep] using hx)
  obtain ⟨hm2, hk2⟩ := even_coordinates_of_four_dvd d m k hd4 hmk
  obtain ⟨i, hi⟩ := even_iff_two_dvd.mp hm2
  obtain ⟨j, hj⟩ := even_iff_two_dvd.mp hk2
  have hri : r = (i : ℚ) := by
    have hi' : (m : ℚ) = 2 * i := by exact_mod_cast hi
    linarith
  have hsj : s = (j : ℚ) := by
    have hj' : (k : ℚ) = 2 * j := by exact_mod_cast hj
    linarith
  refine ⟨i, j, ?_⟩
  rw [← hrep, hri, hsj]
  norm_cast

theorem integral_quadratic_eq_int_add_int_mul_half {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d)
    (hd4 : d % 4 = 1) (x : K) (hx : IsIntegral ℤ x) :
    ∃ i j : ℤ, x = i + j * ((1 + a) / 2) := by
  let r := u.repr x 0
  let s := u.repr x 1
  have hrep : (r : K) + s * a = x := by
    simpa [r, s, hu, Fin.sum_univ_succ, Algebra.smul_def] using u.sum_repr x
  obtain ⟨m, k, hm, hk, hmk⟩ := integral_quadratic_half_coordinates u a d r s hu ha hd
    (by simpa only [hrep] using hx)
  obtain ⟨i, hi⟩ := even_iff_two_dvd.mp (even_sub_coordinates_of_four_dvd d m k hd4 hmk)
  have hri : r = (i : ℚ) + (k : ℚ) / 2 := by
    have hi' : (m : ℚ) - k = 2 * i := by exact_mod_cast hi
    linarith
  have hsk : s = (k : ℚ) / 2 := by linarith
  refine ⟨i, k, ?_⟩
  rw [← hrep, hri, hsk]
  push_cast
  ring

theorem integral_quadratic_half_generator {K : Type*} [Field K] [CharZero K]
    (a : K) (d : ℤ) (ha : a ^ 2 = d) (hd : d % 4 = 1) :
    IsIntegral ℤ ((1 + a) / 2) := by
  have hdv : d = 4 * (d / 4) + 1 := by omega
  refine ⟨Polynomial.X ^ 2 - (Polynomial.X + Polynomial.C (d / 4)),
    Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X_add_C]; norm_num), ?_⟩
  change Polynomial.aeval ((1 + a) / 2)
    (Polynomial.X ^ 2 - (Polynomial.X + Polynomial.C (d / 4))) = 0
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_add, Polynomial.aeval_C]
  have hdK : (d : K) = 4 * ((d / 4 : ℤ) : K) + 1 := by exact_mod_cast hdv
  field_simp
  linear_combination ha + hdK

theorem exists_ringOfIntegers_pair_basis {K : Type*} [Field K] [NumberField K]
    (w : K) (hw : IsIntegral ℤ w) (hdim : Module.finrank ℚ K = 2)
    (hspan : ∀ x : K, IsIntegral ℤ x → ∃ m n : ℤ, x = m + n * w) :
    ∃ B : Basis (Fin 2) ℤ (𝓞 K),
      (fun i => ((B i : 𝓞 K) : K)) = ![1, w] := by
  let W : 𝓞 K := ⟨w, hw⟩
  let v : Fin 2 → 𝓞 K := ![1, W]
  have hs : ⊤ ≤ Submodule.span ℤ (Set.range v) := by
    intro x _
    obtain ⟨m, n, hmn⟩ := hspan x x.property
    have hmn' : x = m • (1 : 𝓞 K) + n • W := by
      apply RingOfIntegers.ext
      change (x : K) = algebraMap (𝓞 K) K (m • (1 : 𝓞 K) + n • W)
      rw [map_add, map_zsmul, map_zsmul, map_one]
      change (x : K) = m • (1 : K) + n • w
      simpa [Algebra.smul_def] using hmn
    rw [hmn']
    exact Submodule.add_mem _
      (Submodule.smul_mem _ m (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ n (Submodule.subset_span ⟨1, rfl⟩))
  have hc : Fintype.card (Fin 2) = Module.finrank ℤ (𝓞 K) := by
    simpa [RingOfIntegers.rank] using hdim.symm
  let B : Basis (Fin 2) ℤ (𝓞 K) := basisOfTopLeSpanOfCardEqFinrank v hs hc
  refine ⟨B, ?_⟩
  ext i
  fin_cases i <;> simp [B, v, W]
  rfl

theorem discr_quadratic_pair {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d r s : ℚ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) :
    Algebra.discr ℚ ![1, (r : K) + s * a] = 4 * d * s ^ 2 := by
  have ht := (trace_norm_quadratic_basis u a d r s hu ha).1
  have ht1 : Algebra.trace ℚ K 1 = 2 := by
    simpa using Algebra.trace_algebraMap_of_basis u (1 : ℚ)
  have hww : ((r : K) + s * a) * ((r : K) + s * a) =
      ((r ^ 2 + d * s ^ 2 : ℚ) : K) + ((2 * r * s : ℚ) : K) * a := by
    push_cast
    linear_combination (s : K) ^ 2 * ha
  have htww : Algebra.trace ℚ K (((r : K) + s * a) * ((r : K) + s * a)) =
      2 * (r ^ 2 + d * s ^ 2) := by
    rw [hww]
    exact (trace_norm_quadratic_basis u a d (r ^ 2 + d * s ^ 2) (2 * r * s) hu ha).1
  rw [Algebra.discr_def, Matrix.det_fin_two]
  change Algebra.trace ℚ K (1 * 1) *
      Algebra.trace ℚ K (((r : K) + s * a) * ((r : K) + s * a)) -
    Algebra.trace ℚ K (1 * ((r : K) + s * a)) *
      Algebra.trace ℚ K (((r : K) + s * a) * 1) = _
  rw [one_mul, one_mul, mul_one, ht, ht1, htww]
  ring

theorem coe_discr_eq_pair_of_integer_basis {K : Type*} [Field K] [NumberField K]
    (B : Basis (Fin 2) ℤ (𝓞 K)) (w : K)
    (hB : (fun i => ((B i : 𝓞 K) : K)) = ![1, w]) :
    (NumberField.discr K : ℚ) = Algebra.discr ℚ ![1, w] := by
  rw [← NumberField.discr_eq_discr K B]
  change (algebraMap ℤ ℚ) (Algebra.discr ℤ B) = _
  rw [← Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) K B]
  congr 1
  funext i
  rw [Basis.localizationLocalization_apply]
  exact congrFun hB i

theorem numberField_discr_quadratic_eq_four_mul {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d)
    (hd4 : d % 4 = 2 ∨ d % 4 = 3) : NumberField.discr K = 4 * d := by
  have hai : IsIntegral ℤ a := IsIntegral.of_pow (by decide : 0 < 2)
    (ha ▸ isIntegral_intCast d)
  have hdim : Module.finrank ℚ K = 2 := by simpa using Module.finrank_eq_card_basis u
  obtain ⟨B, hB⟩ := exists_ringOfIntegers_pair_basis a hai hdim
    (integral_quadratic_eq_int_add_int_mul u a d hu ha hd hd4)
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [coe_discr_eq_pair_of_integer_basis B a hB]
  simpa using discr_quadratic_pair u a (d : ℚ) 0 1 hu (by simpa using ha)

theorem numberField_discr_quadratic_eq_self {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d)
    (hd4 : d % 4 = 1) : NumberField.discr K = d := by
  have hwi := integral_quadratic_half_generator a d ha hd4
  have hdim : Module.finrank ℚ K = 2 := by simpa using Module.finrank_eq_card_basis u
  obtain ⟨B, hB⟩ := exists_ringOfIntegers_pair_basis ((1 + a) / 2) hwi hdim
    (integral_quadratic_eq_int_add_int_mul_half u a d hu ha hd hd4)
  have hw : (1 + a) / 2 = ((1 / 2 : ℚ) : K) + ((1 / 2 : ℚ) : K) * a := by
    push_cast
    ring
  apply Int.cast_injective (α := ℚ)
  rw [coe_discr_eq_pair_of_integer_basis B ((1 + a) / 2) hB, hw,
    discr_quadratic_pair u a (d : ℚ) (1 / 2) (1 / 2) hu (by simpa using ha)]
  ring

theorem isFundamentalDiscr_quadratic {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d) :
    Int.IsFundamentalDiscr (NumberField.discr K) := by
  by_cases hd1 : d % 4 = 1
  · rw [numberField_discr_quadratic_eq_self u a d hu ha hd hd1]
    exact Int.isFundamentalDiscr_iff_squarefree.mpr (Or.inl ⟨hd1, hd⟩)
  · have hd0 : d % 4 ≠ 0 := by
      intro h
      exact Int.squarefree_iff_prime_sq_not_dvd.mp hd 2 Nat.prime_two
        (by simpa using Int.dvd_of_emod_eq_zero h)
    have hd4 : d % 4 = 2 ∨ d % 4 = 3 := by omega
    rw [numberField_discr_quadratic_eq_four_mul u a d hu ha hd hd4]
    exact Int.isFundamentalDiscr_four_mul.mpr ⟨hd, hd4⟩

theorem isUnramifiedIn_two_iff_radical_mod_four {K : Type*} [Field K] [NumberField K]
    (u : Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d) (hd : Squarefree d) :
    Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(2 : ℤ)}) ↔ d % 4 = 1 := by
  rw [← NumberField.not_dvd_discr_iff_isUnramifiedIn K (𝓞 K)
    ((Int.prime_iff_natAbs_prime (k := 2)).mpr Nat.prime_two)]
  by_cases hd1 : d % 4 = 1
  · rw [numberField_discr_quadratic_eq_self u a d hu ha hd hd1]
    have hodd : ¬ (2 : ℤ) ∣ d := by
      rw [Int.dvd_iff_emod_eq_zero]
      omega
    simp [hodd, hd1]
  · have hd0 : d % 4 ≠ 0 := by
      intro h
      exact Int.squarefree_iff_prime_sq_not_dvd.mp hd 2 Nat.prime_two
        (by simpa using Int.dvd_of_emod_eq_zero h)
    have hd4 : d % 4 = 2 ∨ d % 4 = 3 := by omega
    rw [numberField_discr_quadratic_eq_four_mul u a d hu ha hd hd4]
    have hdiv : (2 : ℤ) ∣ 4 * d := dvd_mul_of_dvd_left (by norm_num) d
    simp [hdiv, hd1]

end WeightedTorusJets

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_SqrtTwoField
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
attribute [-simp] _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField

namespace WeightedTorusJets

open NumberField

theorem quadraticAdjoin_discriminant {L : Type*} [Field L] [NumberField L]
    (a : L) (d : ℤ) (ha : a ^ 2 = d) (hd : Squarefree d)
    (hns : ¬ IsSquare (d : ℚ)) :
    NumberField.discr (IntermediateField.adjoin ℚ {a}) =
      (if d % 4 = 1 then d else 4 * d) ∧
    Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
    (Algebra.IsUnramifiedIn (𝓞 (IntermediateField.adjoin ℚ {a}))
      (Ideal.span {(2 : ℤ)}) ↔ d % 4 = 1) := by
  let F := IntermediateField.adjoin ℚ {a}
  let A : F := IntermediateField.AdjoinSimple.gen ℚ a
  have hroot : a ^ 2 = algebraMap ℚ L (d : ℚ) := by simpa using ha
  have hi : IsIntegral ℚ a := IsIntegral.of_pow (by decide : 0 < 2)
    (hroot ▸ isIntegral_algebraMap)
  have hdim := finrank_adjoin_sqrt a (d : ℚ) hroot hns
  let u : Module.Basis (Fin 2) ℚ F := quadraticAdjoinBasis a hi hdim
  have hu : (u : Fin 2 → F) = ![1, A] := by
    funext i
    exact quadraticAdjoinBasis_apply a hi hdim i
  have hA : A ^ 2 = (d : F) := by
    apply Subtype.ext
    exact ha
  refine ⟨?_, isFundamentalDiscr_quadratic u A d hu hA hd,
    isUnramifiedIn_two_iff_radical_mod_four u A d hu hA hd⟩
  by_cases hd1 : d % 4 = 1
  · simp only [ite_eq_left hd1]
    exact numberField_discr_quadratic_eq_self u A d hu hA hd hd1
  · simp only [ite_eq_right hd1]
    have hd0 : d % 4 ≠ 0 := by
      intro h
      exact Int.squarefree_iff_prime_sq_not_dvd.mp hd 2 Nat.prime_two
        (by simpa using Int.dvd_of_emod_eq_zero h)
    exact numberField_discr_quadratic_eq_four_mul u A d hu hA hd (by omega)



open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

end WeightedTorusJets

namespace WeightedTorusJets

open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat

theorem exists_auxiliary_sqrt_pair_of_field_ne (q : ℕ) [NeZero q]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {8 * q} ℚ L]
    [NeZero (8 * q)] [IsAbelianGalois ℚ L]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    (hne : χ ≠ 1) (hfield : characterField (8 * q) L ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠ sourceSqrtTwoField q L) :
    ∃ (d : ℤ) (a b : L), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : L) ∧ b ^ 2 = 2 ∧
      IsIntegral ℤ a ∧ IsIntegral ℤ b ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) L ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      IntermediateField.adjoin ℚ {a} ≠ IntermediateField.adjoin ℚ {b} ∧
      ∀ (p : ℕ), p.Prime → ¬ p ∣ 2 * q →
        ∀ (P : Ideal (𝓞 L)), P.under ℤ = Ideal.span {(p : ℤ)} →
          ∀ (σ : Gal(L/ℚ)), IsArithFrobAt ℤ σ P → χ p = -1 → σ a = -a := by
  have hqm : q ∣ 8 * q := dvd_mul_left q 8
  have h8m : 8 ∣ 8 * q := dvd_mul_right 8 q
  let K := cyclotomicDivisorField q (8 * q) L
  let : IsCyclotomicExtension {q} ℚ K :=
    cyclotomicDivisorField_isCyclotomicExtension q (8 * q) L hqm
  let : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {q} ℚ K
  obtain ⟨d, aK, hd, hbound, hddiv, hdns, haK, _, hadjK, hsign⟩ :=
    exists_squarefree_generator_frobenius_sign q (8 * q) K L hqm χ hχ hprim hne
  let a : L := algebraMap K L aK
  have ha : a ^ 2 = (d : L) := by
    change (algebraMap K L aK) ^ 2 = _
    rw [← map_pow, haK, map_intCast]
  let ζ : L := zeta (8 * q) ℚ L ^ ((8 * q) / 8)
  have hζ : IsPrimitiveRoot ζ 8 :=
    (zeta_spec (8 * q) ℚ L).pow (NeZero.pos (8 * q)) (Nat.div_mul_cancel h8m).symm
  let b := ζ - ζ ^ 3
  have hb : b ^ 2 = 2 := primitive_eighth_root_difference_sq hζ
  have hadj : IntermediateField.adjoin ℚ {a} =
      characterField (8 * q) L ℂ (DirichletCharacter.changeLevel hqm χ) := by
    rw [characterField_changeLevel q K ℂ L hqm χ hχ, ← hadjK,
      IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have hneq : IntermediateField.adjoin ℚ {a} ≠ IntermediateField.adjoin ℚ {b} := by
    intro heq
    exact hfield (hadj.symm.trans heq)
  refine ⟨d, a, b, hd, hbound, hddiv, hdns, ha, hb, ?_, ?_, hadj, hneq, ?_⟩
  · apply IsIntegral.of_pow (by decide : 0 < 2)
    rw [ha]
    exact isIntegral_algebraMap
  · apply IsIntegral.of_pow (by decide : 0 < 2)
    rw [hb]
    exact isIntegral_natCast 2
  · intro p hp hpn P hP σ hσ hχp
    have hc : p.Coprime (2 * q) := hp.coprime_iff_not_dvd.mpr hpn
    have h2 := (Nat.coprime_mul_iff_right.mp hc).1
    have hq := (Nat.coprime_mul_iff_right.mp hc).2
    have h8 : p.Coprime 8 := by simpa using h2.pow_right 3
    exact hsign p hp (h8.mul_right hq) P hP σ hσ hχp

end WeightedTorusJets

namespace WeightedTorusJets

open NumberField

theorem source_biquadratic_arithmetic_of_field_ne_jb247_oai (q : ℕ) [NeZero q]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {8 * q} ℚ L]
    [NeZero (8 * q)] [IsAbelianGalois ℚ L]
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) (hfield : characterField (8 * q) L ℂ
      (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ≠ sourceSqrtTwoField q L) :
    ∃ (d : ℤ) (a b : L), Squarefree d ∧ d.natAbs ≤ q ∧ d.natAbs ∣ q ∧
      ¬ IsSquare (d : ℚ) ∧ a ^ 2 = (d : L) ∧ b ^ 2 = 2 ∧
      IntermediateField.adjoin ℚ {a} = characterField (8 * q) L ℂ
        (DirichletCharacter.changeLevel (dvd_mul_left q 8) χ) ∧
      (NumberField.discr (IntermediateField.adjoin ℚ {a})).natAbs = q ∧
      Int.IsFundamentalDiscr (NumberField.discr (IntermediateField.adjoin ℚ {a})) ∧
      NumberField.discr (IntermediateField.adjoin ℚ {a}) =
        (if d % 4 = 1 then d else 4 * d) ∧
      let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
      let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
      ∃ v : Module.Basis (Fin 4) ℚ B,
        (∀ i, v i = ![1, a', b', a' * b'] i) ∧
        (∀ i, IsIntegral ℤ (v i)) ∧ Module.finrank ℚ B = 4 ∧
        ∃ σ τ : B ≃ₐ[ℚ] B,
          σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
          Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
          (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
          (∀ f g : B ≃ₐ[ℚ] B, Commute f g) ∧
          ∀ (p : ℕ), p.Prime → ¬ p ∣ 2 * q → χ p = -1 →
            ((∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - σ • x) ∨
              (∀ x : 𝓞 B, (p : 𝓞 B) ∣ x ^ p - (σ * τ) • x)) := by
  have hquad := real_character_isQuadratic χ hreal
  obtain ⟨d, a, b, hd, hbound, hddiv, hdns, ha, hb, _, _, hadj, hfields, hsign⟩ :=
    exists_auxiliary_sqrt_pair_of_field_ne q L χ hquad hprim hne hfield
  have haRat : a ^ 2 = algebraMap ℚ L (d : ℚ) := by simpa using ha
  have hbRat : b ^ 2 = algebraMap ℚ L (2 : ℚ) := by simpa using hb
  let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
  let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let v := sqrtPairBasis a b (d : ℚ) 2 haRat hbRat hdns not_isSquare_rat_two hfields
  have hv (i : Fin 4) : v i = ![1, a', b', a' * b'] i := by
    apply Subtype.ext
    change (sqrtPairBasis a b (d : ℚ) 2 haRat hbRat hdns not_isSquare_rat_two hfields i : L) = _
    rw [coe_sqrtPairBasis_apply]
    fin_cases i <;> rfl
  have ha' : a' ^ 2 = (d : B) := by apply Subtype.ext; exact ha
  have hb' : b' ^ 2 = (2 : B) := by apply Subtype.ext; exact hb
  have hint := biquadratic_monomials_integral a' b' d 2 ha' (by simpa using hb')
  obtain ⟨σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, hdesc⟩ :=
    sqrtPair_frobenius_directions a b (d : ℚ) 2 haRat hbRat hdns not_isSquare_rat_two hfields
  obtain ⟨hformula, hfund, _⟩ := quadraticAdjoin_discriminant a d ha hd hdns
  refine ⟨d, a, b, hd, hbound, hddiv, hdns, ha, hb, hadj, ?_, hfund, hformula, v, hv, ?_, ?_,
    σ, τ, hσa, hσb, hτa, hτb, hcard, hall, hcomm, ?_⟩
  · rw [hadj]
    exact characterField_changeLevel_discr_natAbs_jb247 (dvd_mul_left q 8) χ hquad hprim hne
  · intro i
    rw [hv]
    fin_cases i
    · exact hint.1
    · exact hint.2.1
    · exact hint.2.2.1
    · exact hint.2.2.2
  · exact finrank_adjoin_pair_sqrt a b (d : ℚ) 2 haRat hbRat hdns not_isSquare_rat_two hfields
  · intro p hp hpn hχp
    let : Fact p.Prime := ⟨hp⟩
    let : NeZero (8 * q) := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne q)⟩
    have hc : p.Coprime (2 * q) := hp.coprime_iff_not_dvd.mpr hpn
    have h2 := (Nat.coprime_mul_iff_right.mp hc).1
    have hq := (Nat.coprime_mul_iff_right.mp hc).2
    have h8 : p.Coprime 8 := by simpa using h2.pow_right 3
    have hpm : ¬ p ∣ 8 * q := hp.coprime_iff_not_dvd.mp (h8.mul_right hq)
    obtain ⟨φ, hfrob, hglobal⟩ := exists_cyclotomic_frobenius_congruence (8 * q) L p hpm
    obtain ⟨P, hP, hover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := 𝓞 L) (Ideal.span {(p : ℤ)})
    exact hdesc p φ (hsign p hp hpn P hover.over.symm φ (hfrob P inferInstance hover) hχp) hglobal

end WeightedTorusJets

end

end Erdos970

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Erdos970.WeightedTorusJets.source_biquadratic_arithmetic_of_field_ne_jb247_oai.{u_1} := @OAI.Erdos970.WeightedTorusJets.source_biquadratic_arithmetic_of_field_ne_jb247_oai.{u_1}
