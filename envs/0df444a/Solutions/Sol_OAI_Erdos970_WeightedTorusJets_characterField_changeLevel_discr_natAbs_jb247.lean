-- Prove2me | solution 1 for OAI.Erdos970.WeightedTorusJets.characterField_changeLevel_discr_natAbs_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:48:23.914233+00:00
-- url     : https://prove2.me/submissions/46ba6214-b0ae-42bd-9b4f-57291668f7fc

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
import Definitions.Def_OAIQ247J005

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

theorem _root_.Int.IsFundamentalDiscr.emod_four_eq_zero_or_one {D : ℤ} (h : Int.IsFundamentalDiscr D) :
    D % 4 = 0 ∨ D % 4 = 1 := by
  rcases h with ⟨h, _⟩ | ⟨e, he, _, _⟩ <;> omega

end OAICompat434

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

open scoped NumberField

namespace WeightedTorusJets



theorem cyclotomic_isUnramifiedIn
    (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] (p : ℕ) [Fact p.Prime] (hpn : ¬ p ∣ n) :
    Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)}) := by
  rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  intro Q hQ hover
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p K Q hpn



open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero

attribute [local instance] canonicalCyclotomicExtension

attribute [local instance] canonicalCyclotomicNumberField

attribute [local instance] canonicalCyclotomicAbelian



open NumberField IsCyclotomicExtension.Rat

end WeightedTorusJets

namespace WeightedTorusJets

theorem quadratic_factorsThrough_of_odd_kernel {q d : ℕ} [NeZero q]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R q) (hχ : χ.IsQuadratic)
    (hd : d ∣ q) (hodd : Odd (Nat.card (ZMod.unitsMap hd).ker)) :
    χ.FactorsThrough d := by
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
  intro u hu
  rw [MonoidHom.mem_ker, ← Units.val_inj, MulChar.coe_toUnitHom, Units.val_one]
  have hupow : u ^ Nat.card (ZMod.unitsMap hd).ker = 1 := by
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨u, hu⟩ : (ZMod.unitsMap hd).ker)))
  have hvpow : χ u ^ Nat.card (ZMod.unitsMap hd).ker = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hupow, Units.val_one, map_one]
  have hchar := congrArg (fun ψ : DirichletCharacter R q ↦ ψ u) (hχ.pow_odd hodd)
  rw [MulChar.pow_apply_coe] at hchar
  exact hchar.symm.trans hvpow

theorem card_unitsMap_kernel_mul_totient {q d : ℕ} [NeZero q] (hd : d ∣ q) :
    Nat.card (ZMod.unitsMap hd).ker * d.totient = q.totient := by
  have : NeZero d := ⟨fun h ↦ (NeZero.ne q) (Nat.eq_zero_of_zero_dvd (h ▸ hd))⟩
  let f := ZMod.unitsMap hd
  have hind : f.ker.index = Nat.card (ZMod d)ˣ := by
    rw [← MonoidHom.comap_bot, Subgroup.index_comap_of_surjective ⊥
      (ZMod.unitsMap_surjective hd), Subgroup.index_bot]
  have hcard := f.ker.card_mul_index
  have hcd : Nat.card (ZMod d)ˣ = d.totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hcq : Nat.card (ZMod q)ˣ = q.totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  rwa [hind, hcd, hcq] at hcard

theorem card_unitsMap_kernel_prime_mul {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0)
    (hpm : p ∣ m) :
    Nat.card (ZMod.unitsMap (Nat.dvd_mul_left m p)).ker = p := by
  have : NeZero (p * m) := ⟨Nat.mul_ne_zero hp.ne_zero hm⟩
  have hcard := card_unitsMap_kernel_mul_totient (Nat.dvd_mul_left m p)
  rw [Nat.totient_mul_of_prime_of_dvd hp hpm] at hcard
  exact Nat.eq_of_mul_eq_mul_right (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm)) hcard

theorem primitive_quadratic_no_odd_prime_square {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R q)
    (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) : ¬ p ^ 2 ∣ q := by
  intro hpq
  obtain ⟨k, hk⟩ := hpq
  have hq : q = p * (p * k) := by rw [hk]; ring
  have hdiv : p * k ∣ q := ⟨p, by rw [hq, mul_comm]⟩
  have hm : p * k ≠ 0 := by
    intro h
    exact (NeZero.ne q) (by rw [hq, h, mul_zero])
  have hcard : Nat.card (ZMod.unitsMap hdiv).ker = p := by
    clear hk
    subst q
    exact card_unitsMap_kernel_prime_mul hp hm (Nat.dvd_mul_right p k)
  have hfactor := quadratic_factorsThrough_of_odd_kernel χ hχ hdiv (hcard.symm ▸ hodd)
  have hle : q ≤ p * k := by
    rw [← hprim]
    exact Nat.sInf_le hfactor
  have hlt : p * k < q := by
    rw [hq]
    exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm) hp.one_lt
  exact (not_lt_of_ge hle) hlt

theorem unitsMap_sixteen_mul_kernel_square {m : ℕ} [NeZero (16 * m)]
    (u : (ZMod (16 * m))ˣ)
    (hu : ZMod.unitsMap (show 8 * m ∣ 16 * m from ⟨2, by ring⟩) u = 1) :
    ∃ y : ZMod (16 * m), y ^ 2 = (u : ZMod (16 * m)) := by
  let hd : 8 * m ∣ 16 * m := ⟨2, by ring⟩
  have hval : ((8 * m : ℕ) : ℤ) ∣ (u.val.val - 1 : ℤ) := by
    rw [← Units.val_inj, Units.val_one, ZMod.unitsMap_def, Units.coe_map] at hu
    have hcast : ZMod.castHom hd (ZMod (8 * m)) u.val =
        ((u.val.val : ℤ) : ZMod (8 * m)) := by simp
    rwa [MonoidHom.coe_coe, hcast, ← Int.cast_one, eq_comm,
      ZMod.intCast_eq_intCast_iff_dvd_sub] at hu
  obtain ⟨k, hk⟩ := hval
  have huval : u.val = 1 + (8 * m : ZMod (16 * m)) * (k : ZMod (16 * m)) := by
    have hcast := congrArg (fun z : ℤ ↦ (z : ZMod (16 * m))) hk
    push_cast at hcast
    rw [ZMod.natCast_zmod_val] at hcast
    rw [sub_eq_iff_eq_add] at hcast
    simpa only [add_comm] using hcast
  refine ⟨1 + (4 * m : ZMod (16 * m)) * (k : ZMod (16 * m)), ?_⟩
  rw [huval]
  have hz : (16 * m : ZMod (16 * m)) = 0 := by
    exact_mod_cast (ZMod.natCast_self (16 * m))
  calc
    (1 + (4 * m : ZMod (16 * m)) * k) ^ 2 =
        1 + (8 * m : ZMod (16 * m)) * k + (16 * m : ZMod (16 * m)) * (m * k ^ 2) := by ring
    _ = _ := by rw [hz, zero_mul, add_zero]

theorem quadratic_factorsThrough_eight_mul {m : ℕ} [NeZero (16 * m)]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R (16 * m)) (hχ : χ.IsQuadratic) :
    χ.FactorsThrough (8 * m) := by
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (show 8 * m ∣ 16 * m from ⟨2, by ring⟩)]
  intro u hu
  rw [MonoidHom.mem_ker] at hu
  rw [MonoidHom.mem_ker, ← Units.val_inj, MulChar.coe_toUnitHom, Units.val_one]
  obtain ⟨y, hy⟩ := unitsMap_sixteen_mul_kernel_square u hu
  have hyunit : IsUnit y := (isUnit_pow_iff (by decide : 2 ≠ 0)).mp (hy.symm ▸ u.isUnit)
  rw [← hy, map_pow]
  have hs := congrArg (fun ψ : DirichletCharacter R (16 * m) ↦ ψ hyunit.unit) hχ.sq_eq_one
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe] at hs
  simpa only [hyunit.unit_spec] using hs

theorem primitive_quadratic_not_sixteen_dvd {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R q)
    (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) : ¬ 16 ∣ q := by
  rintro ⟨m, rfl⟩
  have hm : 0 < m := Nat.pos_of_ne_zero fun h ↦ (NeZero.ne (16 * m)) (by simp [h])
  have hle : 16 * m ≤ 8 * m := by
    rw [← hprim]
    exact Nat.sInf_le (quadratic_factorsThrough_eight_mul χ hχ)
  omega

theorem quadratic_factorsThrough_odd_two_mul {m : ℕ} [NeZero (2 * m)]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R (2 * m))
    (hχ : χ.IsQuadratic) (hm : Odd m) : χ.FactorsThrough m := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero fun h ↦ (NeZero.ne (2 * m)) (by simp [h])
  have hcard : Nat.card (ZMod.unitsMap (Nat.dvd_mul_left m 2)).ker = 1 := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.totient_pos.mpr hmpos)
    rw [one_mul, card_unitsMap_kernel_mul_totient, Nat.totient_two_mul_of_odd hm]
  apply quadratic_factorsThrough_of_odd_kernel χ hχ (Nat.dvd_mul_left m 2)
  rw [hcard]
  decide

theorem primitive_quadratic_mod_four_ne_two {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R q)
    (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) : q % 4 ≠ 2 := by
  intro hqmod
  have hq : q = 2 * (2 * (q / 4) + 1) := by omega
  obtain ⟨m, hm, hq⟩ : ∃ m, Odd m ∧ q = 2 * m :=
    ⟨2 * (q / 4) + 1, ⟨q / 4, rfl⟩, hq⟩
  subst q
  have hle : 2 * m ≤ m := by
    rw [← hprim]
    exact Nat.sInf_le (quadratic_factorsThrough_odd_two_mul χ hχ hm)
  have hmpos : 0 < m := Nat.pos_of_ne_zero fun h ↦ (NeZero.ne (2 * m)) (by simp [h])
  omega

theorem square_divisor_of_primitive_quadratic {q c : ℕ} [NeZero q]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R q)
    (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) (hc : c ^ 2 ∣ q) : c = 1 ∨ c = 2 := by
  have hc0 : c ≠ 0 := by
    intro h
    apply NeZero.ne q
    apply Nat.eq_zero_of_zero_dvd
    simpa [h] using hc
  obtain ⟨k, hk⟩ : ∃ k, c = 2 ^ k := ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (p := 2) hc0 (by
    intro p hp hpc
    by_contra hne
    exact primitive_quadratic_no_odd_prime_square χ hχ hprim hp (hp.odd_of_ne_two hne)
      ((pow_dvd_pow_of_dvd hpc 2).trans hc))⟩
  have hk1 : k ≤ 1 := by
    by_contra! hk2
    have h16 : 16 ∣ c ^ 2 := by
      rw [hk, ← pow_mul]
      exact pow_dvd_pow 2 (by omega : 4 ≤ k * 2)
    exact primitive_quadratic_not_sixteen_dvd χ hχ hprim (h16.trans hc)
  interval_cases k <;> simp_all

theorem primitive_quadratic_radicand_eq_or_four_mul {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R q)
    (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    {D c d : ℤ} (hD : D.natAbs = q) (hDc : D = c ^ 2 * d) : D = d ∨ D = 4 * d := by
  have hdiv : c.natAbs ^ 2 ∣ q := by
    have h := Int.natAbs_dvd_natAbs.mpr (show c ^ 2 ∣ D from ⟨d, hDc⟩)
    simpa only [Int.natAbs_pow, hD] using h
  rcases square_divisor_of_primitive_quadratic χ hχ hprim hdiv with hc | hc
  · have hsq : c ^ 2 = 1 := by
      have h := congrArg (fun n : ℕ ↦ (n : ℤ) ^ 2) hc
      norm_num [Int.natCast_natAbs] at h
      rcases h with rfl | rfl <;> norm_num
    left
    simpa only [hsq, one_mul] using hDc
  · have hsq : c ^ 2 = 4 := by
      have h := congrArg (fun n : ℕ ↦ (n : ℤ) ^ 2) hc
      norm_num [Int.natCast_natAbs] at h
      exact h
    right
    simpa only [hsq] using hDc

theorem odd_divisor_primitive_quadratic_squarefree {q m : ℕ} [NeZero q]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R q)
    (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) (hm : Odd m) (hmq : m ∣ q) :
    Squarefree m := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  rcases hp.eq_two_or_odd' with rfl | hodd
  · exact hm.not_two_dvd_nat ((Nat.dvd_mul_right 2 2).trans hpp)
  · exact primitive_quadratic_no_odd_prime_square χ hχ hprim hp hodd
      ((by simpa only [pow_two] using hpp : p ^ 2 ∣ m).trans hmq)

theorem primitive_quadratic_conductor_shape {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] (χ : DirichletCharacter R q)
    (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) :
    ∃ u : ℕ, Odd u ∧ Squarefree u ∧ (q = u ∨ q = 4 * u ∨ q = 8 * u) := by
  have h16 : q % 16 ≠ 0 := fun h ↦
    primitive_quadratic_not_sixteen_dvd χ hχ hprim (Nat.dvd_of_mod_eq_zero h)
  have h4 := primitive_quadratic_mod_four_ne_two χ hχ hprim
  by_cases hodd : q % 2 = 1
  · have ho : Odd q := Nat.odd_iff.mpr hodd
    exact ⟨q, ho, odd_divisor_primitive_quadratic_squarefree χ hχ hprim ho dvd_rfl,
      Or.inl rfl⟩
  · by_cases h8 : q % 8 = 0
    · have hq : q = 8 * (q / 8) := by omega
      have ho : Odd (q / 8) := Nat.odd_iff.mpr (by omega)
      have hd : q / 8 ∣ q := ⟨8, by omega⟩
      exact ⟨q / 8, ho, odd_divisor_primitive_quadratic_squarefree χ hχ hprim ho hd,
        Or.inr (Or.inr hq)⟩
    · have hq : q = 4 * (q / 4) := by omega
      have ho : Odd (q / 4) := Nat.odd_iff.mpr (by omega)
      have hd : q / 4 ∣ q := ⟨4, by omega⟩
      exact ⟨q / 4, ho, odd_divisor_primitive_quadratic_squarefree χ hχ hprim ho hd,
        Or.inr (Or.inl hq)⟩

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

namespace WeightedTorusJets

theorem isUnramifiedIn_of_numberField_extension
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] (P : Ideal ℤ) (hunr : Algebra.IsUnramifiedIn (𝓞 L) P) :
    Algebra.IsUnramifiedIn (𝓞 K) P := by
  intro Q hQ hover
  obtain ⟨⟨Q', hQ', hover'⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 L) Q
  have : Q'.LiesOver P := Ideal.LiesOver.trans Q' Q P
  have : Algebra.IsUnramifiedAt ℤ Q' := hunr Q' inferInstance inferInstance
  exact Algebra.IsUnramifiedAt.of_liesOver ℤ Q Q'



theorem quadratic_radical_mod_four_of_odd_cyclotomic_overfield
    (n : ℕ) [NeZero n] (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    [IsCyclotomicExtension {n} ℚ L]
    (u : Module.Basis (Fin 2) ℚ K) (a : K) (d : ℤ)
    (hu : (u : Fin 2 → K) = ![1, a]) (ha : a ^ 2 = d)
    (hd : Squarefree d) (hn : Odd n) : d % 4 = 1 := by
  apply (isUnramifiedIn_two_iff_radical_mod_four u a d hu ha hd).mp
  exact isUnramifiedIn_of_numberField_extension (L := L) _
    (cyclotomic_isUnramifiedIn n L 2 hn.not_two_dvd_nat)



open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat

theorem primitive_odd_quadratic_signed_level_mod_four {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℤ q) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    (hodd : Odd q) : (χ (-1) * (q : ℤ)) % 4 = 1 := by
  classical
  by_cases hne : χ = 1
  · subst χ
    have hq : q = 1 := hprim.symm.trans DirichletCharacter.conductor_one
    subst q
    rw [MulChar.one_apply isUnit_neg_one]
    norm_num
  let K := CyclotomicField q ℚ
  let : IsCyclotomicExtension {q} ℚ K := CyclotomicField.isCyclotomicExtension q ℚ
  let : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {q} ℚ K
  let χK := χ.ringHomComp (Int.castRingHom K)
  have hpK : DirichletCharacter.IsPrimitive χK := by
    rw [DirichletCharacter.isPrimitive_def, conductor_ringHomComp χ (Int.castRingHom K)
      (Int.cast_injective (α := K))]
    exact hprim
  let e := AddChar.zmodChar q (zeta_spec q ℚ K).pow_eq_one
  have he : e.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root q (zeta_spec q ℚ K)
  let g := gaussSum χK e
  let D : ℤ := χ (-1) * q
  have hgD : g ^ 2 = (D : K) := by
    change gaussSum χK e ^ 2 = ((χ (-1) * (q : ℤ) : ℤ) : K)
    rw [primitive_quadratic_gaussSum_sq hpK (hχ.comp (Int.castRingHom K)) he]
    change (χ (-1) : K) * (q : K) = ((χ (-1) * (q : ℤ) : ℤ) : K)
    rw [Int.cast_mul, Int.cast_natCast]
  have hqsf : Squarefree q := odd_divisor_primitive_quadratic_squarefree χ hχ hprim hodd dvd_rfl
  have hDsf : Squarefree D := by
    apply Int.squarefree_natAbs.mp
    change Squarefree (χ (-1) * (q : ℤ)).natAbs
    rw [Int.natAbs_mul, Int.natAbs_of_isUnit (isUnit_neg_one.map χ), one_mul]
    exact hqsf
  have hneC : χ.ringHomComp (Int.castRingHom ℂ) ≠ 1 := by
    exact (MulChar.ringHomComp_ne_one_iff (f := Int.castRingHom ℂ)
      (Int.cast_injective (α := ℂ))).mpr hne
  have hdim : Module.finrank ℚ (IntermediateField.adjoin ℚ {g}) = 2 := by
    rw [show IntermediateField.adjoin ℚ {g} =
        characterField q K ℂ (χ.ringHomComp (Int.castRingHom ℂ)) from
      gaussSum_adjoin_eq_characterField χ hχ hprim e he]
    exact characterField_finrank q K ℂ _ (hχ.comp (Int.castRingHom ℂ)) hneC
  have hgi : IsIntegral ℚ g := IsIntegral.of_pow (by decide : 0 < 2)
    (hgD ▸ isIntegral_intCast D)
  let F := IntermediateField.adjoin ℚ {g}
  let a : F := IntermediateField.AdjoinSimple.gen ℚ g
  let u := quadraticAdjoinBasis g hgi hdim
  have hu : (u : Fin 2 → F) = ![1, a] := by
    funext i
    exact quadraticAdjoinBasis_apply g hgi hdim i
  have ha : a ^ 2 = (D : F) := by
    apply Subtype.ext
    exact hgD
  exact quadratic_radical_mod_four_of_odd_cyclotomic_overfield q F K u a D hu ha hDsf hodd

end WeightedTorusJets

namespace WeightedTorusJets

theorem crtCharacter_decomposition {m n : ℕ} {R : Type*} [CommRing R]
    (h : m.Coprime n) (χ : DirichletCharacter R (m * n)) :
    χ = DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) (crtCharacterLeft h χ) *
      DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) (crtCharacterRight h χ) := by
  apply MulChar.ext
  intro u
  rw [MulChar.mul_apply]
  simp only [DirichletCharacter.changeLevel_def, MulChar.ofUnitHom_coe,
    MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  rw [crtCharacterLeft_apply_unit, crtCharacterRight_apply_unit, ← map_mul]
  congr 1
  have hu : u = (crtUnits h).symm (ZMod.unitsMap (Nat.dvd_mul_right m n) u, 1) *
      (crtUnits h).symm (1, ZMod.unitsMap (Nat.dvd_mul_left n m) u) := by
    apply (crtUnits h).injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    apply Prod.ext <;> simp
  exact congrArg Units.val hu

theorem crtCharacterLeft_isPrimitive {m n : ℕ} [NeZero m] [NeZero n]
    {R : Type*} [CommRing R] (h : m.Coprime n)
    (χ : DirichletCharacter R (m * n)) (hprim : χ.IsPrimitive) :
    (crtCharacterLeft h χ).IsPrimitive := by
  have hdiv := DirichletCharacter.conductor_mul_dvd_lcm_conductor
    (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) (crtCharacterLeft h χ))
    (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) (crtCharacterRight h χ))
  rw [← crtCharacter_decomposition h χ, hprim,
    DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel] at hdiv
  apply Nat.dvd_antisymm (crtCharacterLeft h χ).conductor_dvd_level
  apply Nat.dvd_of_mul_dvd_mul_right (NeZero.pos n)
  exact hdiv.trans (Nat.lcm_dvd (Nat.dvd_mul_right _ n)
    ((crtCharacterRight h χ).conductor_dvd_level.trans (Nat.dvd_mul_left n _)))

theorem crtCharacterRight_isPrimitive {m n : ℕ} [NeZero m] [NeZero n]
    {R : Type*} [CommRing R] (h : m.Coprime n)
    (χ : DirichletCharacter R (m * n)) (hprim : χ.IsPrimitive) :
    (crtCharacterRight h χ).IsPrimitive := by
  have hdiv := DirichletCharacter.conductor_mul_dvd_lcm_conductor
    (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) (crtCharacterLeft h χ))
    (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) (crtCharacterRight h χ))
  rw [← crtCharacter_decomposition h χ, hprim,
    DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel] at hdiv
  apply Nat.dvd_antisymm (crtCharacterRight h χ).conductor_dvd_level
  apply Nat.dvd_of_mul_dvd_mul_left (NeZero.pos m)
  exact hdiv.trans (Nat.lcm_dvd
    ((crtCharacterLeft h χ).conductor_dvd_level.trans (Nat.dvd_mul_right m _))
    (Nat.dvd_mul_left _ m))

theorem changeLevel_neg_one {m n : ℕ} {R : Type*} [CommRing R]
    (h : m ∣ n) (χ : DirichletCharacter R m) :
    DirichletCharacter.changeLevel h χ (-1) = χ (-1) := by
  have he := DirichletCharacter.changeLevel_eq_cast_of_dvd χ h (-1 : (ZMod n)ˣ)
  simpa only [Units.val_neg, Units.val_one, ZMod.cast_neg h, ZMod.cast_one h] using he

theorem crtCharacter_neg_one {m n : ℕ} {R : Type*} [CommRing R]
    (h : m.Coprime n) (χ : DirichletCharacter R (m * n)) :
    χ (-1) = crtCharacterLeft h χ (-1) * crtCharacterRight h χ (-1) := by
  have he := congrArg (fun ψ : DirichletCharacter R (m * n) => ψ (-1))
    (crtCharacter_decomposition h χ)
  simpa only [MulChar.mul_apply, changeLevel_neg_one] using he

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

theorem primitive_mod_four_character_neg_one (χ : DirichletCharacter ℤ 4)
    (hprim : χ.IsPrimitive) : χ (-1) = -1 := by
  have hne : χ ≠ 1 := by
    intro h
    have hc := hprim
    rw [DirichletCharacter.isPrimitive_def, h, DirichletCharacter.conductor_one] at hc
    norm_num at hc
  obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hne
  have hu_cases : u = 1 ∨ u = -1 := by
    exact (by decide : ∀ u : (ZMod 4)ˣ, u = 1 ∨ u = -1) u
  rcases hu_cases with rfl | rfl
  · simp at hu
  · have hval := Int.isUnit_eq_one_or ((isUnit_neg_one : IsUnit (-1 : ZMod 4)).map χ)
    exact hval.resolve_left (by simpa only [Units.val_neg, Units.val_one] using hu)



theorem primitive_four_mul_exists_odd_part {u : ℕ} [NeZero u] (hu : Odd u)
    (χ : DirichletCharacter ℤ (4 * u)) (hprim : χ.IsPrimitive) :
    ∃ η : DirichletCharacter ℤ u, η.IsPrimitive ∧ χ (-1) = -η (-1) := by
  have hc : Nat.Coprime 4 u := by
    simpa using hu.coprime_two_left.pow_left 2
  refine ⟨crtCharacterRight hc χ, crtCharacterRight_isPrimitive hc χ hprim, ?_⟩
  rw [crtCharacter_neg_one hc χ, primitive_mod_four_character_neg_one _
    (crtCharacterLeft_isPrimitive hc χ hprim), neg_one_mul]



theorem primitive_four_mul_quadratic_signed_part_mod_four {u : ℕ} [NeZero u]
    (χ : DirichletCharacter ℤ (4 * u)) (hprim : χ.IsPrimitive) (hu : Odd u) :
    (χ (-1) * (u : ℤ)) % 4 = 3 := by
  obtain ⟨η, hηprim, hneg⟩ := primitive_four_mul_exists_odd_part hu χ hprim
  have hηquad : η.IsQuadratic := by
    intro a
    by_cases ha : IsUnit a
    · exact Or.inr (Int.isUnit_eq_one_or (ha.map η))
    · exact Or.inl (η.map_nonunit ha)
  have hodd := primitive_odd_quadratic_signed_level_mod_four η hηquad hηprim hu
  rw [hneg, neg_mul]
  omega



theorem fundamentalDiscr_eight_odd_case {D d : ℤ} {u : ℕ} (hu : Odd u)
    (hd : Squarefree d) (hDd : D = d ∨ D = 4 * d) (hD : D.natAbs = 8 * u) :
    Int.IsFundamentalDiscr D := by
  rcases hDd with rfl | hDd
  · have hf := Nat.squarefree_iff_prime_squarefree.mp (Int.squarefree_natAbs.mpr hd)
    exact (hf 2 Nat.prime_two ⟨2 * u, by omega⟩).elim
  · rw [hDd, Int.isFundamentalDiscr_four_mul]
    refine ⟨hd, Or.inl ?_⟩
    have heq : 4 * d.natAbs = 8 * u := by simpa [hDd, Int.natAbs_mul] using hD
    have hn : d.natAbs = 2 * u := by omega
    have hh := congrArg (fun n : ℕ ↦ (n : ℤ)) hn
    rw [Int.natCast_natAbs, Nat.cast_mul, Nat.cast_ofNat] at hh
    obtain ⟨k, hk⟩ := hu
    rcases le_total 0 d with h | h
    · rw [abs_of_nonneg h] at hh
      omega
    · rw [abs_of_nonpos h] at hh
      omega

theorem fundamentalDiscr_four_parity_case {D d s : ℤ} {u : ℕ}
    (hd : Squarefree d) (hDd : D = d ∨ D = 4 * d)
    (hD : D = s * (4 * (u : ℤ))) (hparity : (s * (u : ℤ)) % 4 = 3) :
    Int.IsFundamentalDiscr D := by
  rcases hDd with rfl | hDd
  · have hf := Int.squarefree_iff_prime_sq_not_dvd.mp hd 2 Nat.prime_two
    apply (hf ?_).elim
    refine ⟨s * (u : ℤ), ?_⟩
    rw [hD]
    ring
  · rw [hDd, Int.isFundamentalDiscr_four_mul]
    refine ⟨hd, Or.inr ?_⟩
    have heq : d = s * (u : ℤ) := by
      apply mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0)
      calc
        4 * d = D := hDd.symm
        _ = s * (4 * (u : ℤ)) := hD
        _ = 4 * (s * (u : ℤ)) := by ring
    rwa [heq]



open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat

theorem exists_signed_squarefree_characterField_generator {n : ℕ} [NeZero n] {K : Type*}
    [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] [IsAbelianGalois ℚ K]
    (χ : DirichletCharacter ℂ n) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    (hne : χ ≠ 1) :
    ∃ (D d : ℤ) (a : K), D = integerCharacter χ hχ (-1) * (n : ℤ) ∧
      D.natAbs = n ∧ Squarefree d ∧ (D = d ∨ D = 4 * d) ∧
      d.natAbs ≤ n ∧ d.natAbs ∣ n ∧
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
  have hDchar : D = χI (-1) * (n : ℤ) := by
    apply Int.cast_injective (α := K)
    push_cast
    calc
      (D : K) = gaussSum χK e ^ 2 := hgD.symm
      _ = χK (-1) * (n : K) := primitive_quadratic_gaussSum_sq hpK hK he
      _ = (χI (-1) : K) * (n : K) := rfl
  have hcases := primitive_quadratic_radicand_eq_or_four_mul χ hχ hprim hDabs hdc
  refine ⟨D, d, a, hDchar, hDabs, hd, hcases, hDabs ▸ hbound, hdiv, hnsq,
    ha, hint, hadjχ, ?_⟩
  intro σ
  have hact := cyclotomic_gaussSum_action χK hK e σ
  rw [hga, map_mul, map_intCast] at hact
  apply mul_left_cancel₀ (Int.cast_ne_zero.mpr hc : (c : K) ≠ 0)
  change (c : K) * σ a = (χI (galEquivZMod n K σ) : K) * ((c : K) * a) at hact
  simpa only [χI, mul_left_comm] using hact

end WeightedTorusJets

namespace WeightedTorusJets

open Module NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat

theorem normalized_signed_conductor_isFundamentalDiscr {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℤ q) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    {D d : ℤ} (hDsign : D = χ (-1) * (q : ℤ)) (hDabs : D.natAbs = q)
    (hd : Squarefree d) (hDd : D = d ∨ D = 4 * d) : Int.IsFundamentalDiscr D := by
  obtain ⟨u, hu, hsfu, hq | hq | hq⟩ := primitive_quadratic_conductor_shape χ hχ hprim
  · have hodd : Odd q := hq ▸ hu
    apply Int.isFundamentalDiscr_iff_squarefree.mpr
    refine Or.inl ⟨?_, Int.squarefree_natAbs.mp ?_⟩
    · rw [hDsign]
      exact primitive_odd_quadratic_signed_level_mod_four χ hχ hprim hodd
    · rwa [hDabs, hq]
  · subst hq
    let : NeZero u := ⟨hsfu.ne_zero⟩
    exact fundamentalDiscr_four_parity_case hd hDd
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hDsign)
      (primitive_four_mul_quadratic_signed_part_mod_four χ hprim hu)
  · exact fundamentalDiscr_eight_odd_case hu hd hDd (hDabs.trans hq)

theorem characterField_discr_eq_signed_conductor {n : ℕ} [NeZero n]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    [IsAbelianGalois ℚ K] (χ : DirichletCharacter ℂ n) (hχ : χ.IsQuadratic)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) :
    NumberField.discr (characterField n K ℂ χ) = integerCharacter χ hχ (-1) * (n : ℤ) := by
  obtain ⟨D, d, a, hDsign, hDabs, hd, hDd, _, _, _, ha, hint, hadj, _⟩ :=
    exists_signed_squarefree_characterField_generator (K := K) χ hχ hprim hne
  have hfund := normalized_signed_conductor_isFundamentalDiscr (integerCharacter χ hχ)
    (integerCharacter_isQuadratic χ hχ) (integerCharacter_isPrimitive χ hχ hprim)
    hDsign hDabs hd hDd
  have hdim : Module.finrank ℚ (IntermediateField.adjoin ℚ {a}) = 2 := by
    rw [hadj]
    exact characterField_finrank n K ℂ χ hχ hne
  have hai : IsIntegral ℚ a := hint.tower_top
  let u := quadraticAdjoinBasis a hai hdim
  let a' := IntermediateField.AdjoinSimple.gen ℚ a
  have hu : (u : Fin 2 → IntermediateField.adjoin ℚ {a}) = ![1, a'] := by
    funext i
    exact quadraticAdjoinBasis_apply a hai hdim i
  have ha' : a' ^ 2 = (d : IntermediateField.adjoin ℚ {a}) := by
    apply Subtype.ext
    exact ha
  have hdiscr : NumberField.discr (IntermediateField.adjoin ℚ {a}) = D := by
    rcases hDd with hDd | hDd
    · rw [hDd] at hfund ⊢
      have hd4 : d % 4 ≠ 0 := by
        intro h
        exact Int.squarefree_iff_prime_sq_not_dvd.mp hd 2 Nat.prime_two
          (by simpa using Int.dvd_of_emod_eq_zero h)
      exact numberField_discr_quadratic_eq_self u a' d hu ha' hd
        (hfund.emod_four_eq_zero_or_one.resolve_left hd4)
    · rw [hDd] at hfund ⊢
      exact numberField_discr_quadratic_eq_four_mul u a' d hu ha' hd
        (Int.isFundamentalDiscr_four_mul.mp hfund).2
  rw [hadj, hDsign] at hdiscr
  exact hdiscr



open NumberField IsCyclotomicExtension.Rat

end WeightedTorusJets

namespace WeightedTorusJets

open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat

theorem characterField_changeLevel_discr_eq_signed_conductor {q m : ℕ}
    [NeZero q] [NeZero m] {L : Type*} [Field L] [NumberField L]
    [IsCyclotomicExtension {m} ℚ L] [IsAbelianGalois ℚ L]
    (hdiv : q ∣ m) (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) :
    NumberField.discr (characterField m L ℂ (DirichletCharacter.changeLevel hdiv χ)) =
      integerCharacter χ hχ (-1) * (q : ℤ) := by
  let K := cyclotomicDivisorField q m L
  let : IsCyclotomicExtension {q} ℚ K :=
    cyclotomicDivisorField_isCyclotomicExtension q m L hdiv
  let : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {q} ℚ K
  rw [characterField_changeLevel q K ℂ L hdiv χ hχ]
  exact (NumberField.discr_eq_discr_of_algEquiv (characterField q K ℂ χ)
    ((characterField q K ℂ χ).equivMap (IsScalarTower.toAlgHom ℚ K L))).symm.trans
      (characterField_discr_eq_signed_conductor χ hχ hprim hne)

theorem characterField_changeLevel_discr_natAbs_jb247_oai {q m : ℕ}
    [NeZero q] [NeZero m] {L : Type*} [Field L] [NumberField L]
    [IsCyclotomicExtension {m} ℚ L] [IsAbelianGalois ℚ L]
    (hdiv : q ∣ m) (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) :
    (NumberField.discr
      (characterField m L ℂ (DirichletCharacter.changeLevel hdiv χ))).natAbs = q := by
  rw [characterField_changeLevel_discr_eq_signed_conductor hdiv χ hχ hprim hne]
  rcases Int.isUnit_eq_one_or ((isUnit_neg_one : IsUnit (-1 : ZMod q)).map
    (integerCharacter χ hχ)) with h | h <;> simp [h]

end WeightedTorusJets

end

end Erdos970

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Erdos970.WeightedTorusJets.characterField_changeLevel_discr_natAbs_jb247_oai.{u_1} := @OAI.Erdos970.WeightedTorusJets.characterField_changeLevel_discr_natAbs_jb247_oai.{u_1}
