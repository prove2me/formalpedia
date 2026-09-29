-- Prove2me | solution 1 for ModularCurve.FullLevel.inclusion_mem_integers_iff_mem_constantReduction_integers_of_igusaEnd_igusaBranch
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/8bfc6109-6dc3-5725-90e7-21c0229cfc1d

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ValuationSubring_algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_inclusion_mem_integers_iff_mem_constantReduction_integers_of_igusaEnd_igusaBranch

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open scoped MatrixGroups Polynomial

namespace IgIntSol

theorem eval₂_intCast_mem {R : Type*} [Ring R] {S : Type*} [SetLike S R] [SubringClass S R] (s : S)
    (Φ : ℤ[X]) {x : R} (hx : x ∈ s) : Φ.eval₂ (Int.castRingHom R) x ∈ s := by
  induction Φ using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval₂_add]; exact add_mem hp hq
  | monomial n a =>
      rw [Polynomial.eval₂_monomial]
      exact mul_mem (by simpa using intCast_mem s a) (pow_mem hx n)

theorem map_eval₂_intCast {R S : Type*} [Ring R] [Ring S] (g : R →+* S) (Φ : ℤ[X]) (x : R) :
    g (Φ.eval₂ (Int.castRingHom R) x) = Φ.eval₂ (Int.castRingHom S) (g x) := by
  rw [Polynomial.hom_eval₂, RingHom.ext_int (g.comp (Int.castRingHom R)) (Int.castRingHom S)]

theorem map_eval₂_intCast' {R S T : Type*} [CommSemiring T] [Ring R] [Ring S] [Algebra T R] [Algebra T S]
    (g : R →ₐ[T] S) (Φ : ℤ[X]) (x : R) :
    g (Φ.eval₂ (Int.castRingHom R) x) = Φ.eval₂ (Int.castRingHom S) (g x) :=
  map_eval₂_intCast g.toRingHom Φ x

theorem aeval_map_intCast {κ B : Type*} [CommRing κ] [Ring B] [Algebra κ B] (Φ : ℤ[X]) (x : B) :
    Polynomial.aeval x (Φ.map (Int.castRingHom κ)) = Φ.eval₂ (Int.castRingHom B) x := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map,
    RingHom.ext_int ((algebraMap κ B).comp (Int.castRingHom κ)) (Int.castRingHom B)]

theorem exists_eq_C_mul_of_ne_zero {L : Type} [Field L] (A : ValuationSubring L) (p : L[X]) (hp : p ≠ 0) :
    ∃ (c : L) (p₁ : L[X]) (n₀ : ℕ), c ≠ 0 ∧ p = Polynomial.C c * p₁ ∧ (∀ n, p₁.coeff n ∈ A) ∧ p₁.coeff n₀ = 1 := by
  have hne : p.support.Nonempty := Polynomial.support_nonempty.mpr hp
  obtain ⟨n₀, hn₀, hmax⟩ := Finset.exists_max_image p.support (fun n => A.valuation (p.coeff n)) hne
  have hc : p.coeff n₀ ≠ 0 := Polynomial.mem_support_iff.mp hn₀
  refine ⟨p.coeff n₀, Polynomial.C (p.coeff n₀)⁻¹ * p, n₀, hc, ?_, ?_, ?_⟩
  · rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1, one_mul]
  · intro n
    rw [Polynomial.coeff_C_mul]
    by_cases hn : n ∈ p.support
    · rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
      have h1 := hmax n hn
      have hc' : A.valuation (p.coeff n₀) ≠ 0 := by rwa [ne_eq, map_eq_zero]
      calc (A.valuation (p.coeff n₀))⁻¹ * A.valuation (p.coeff n)
          ≤ (A.valuation (p.coeff n₀))⁻¹ * A.valuation (p.coeff n₀) := mul_le_mul_right h1 _
        _ = 1 := inv_mul_cancel₀ hc'
    · rw [Polynomial.notMem_support_iff.mp hn, mul_zero]
      exact zero_mem A
  · rw [Polynomial.coeff_C_mul, inv_mul_cancel₀ hc]

theorem aeval_mem_of_forall_coeff_mem {L F : Type} [Field L] [Field F] [Algebra L F] (A : ValuationSubring L)
    (S : Subring F) (hSA : ∀ a : L, a ∈ A → algebraMap L F a ∈ S)
    (x : F) (hx : x ∈ S) (p : L[X]) (hp : ∀ n, p.coeff n ∈ A) : Polynomial.aeval x p ∈ S := by
  rw [Polynomial.aeval_eq_sum_range]
  refine Subring.sum_mem _ (fun n _ => ?_)
  rw [Algebra.smul_def]
  exact Subring.mul_mem _ (hSA _ (hp n)) (Subring.pow_mem _ hx n)

theorem inv_mem_of_isUnit {F : Type} [Field F] (S : ValuationSubring F) (t : ↥S) (ht : IsUnit t) :
    ((t : F))⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := ht
  have hmul : (t : F) * (((u⁻¹ : (↥S)ˣ) : ↥S) : F) = 1 := by
    have h := congrArg (fun z : ↥S => (z : F)) u.mul_inv
    simp only [Units.val_mul, hu] at h
    exact h
  by_cases ht0 : (t : F) = 0
  · rw [ht0, zero_mul] at hmul; exact absurd hmul zero_ne_one
  rw [inv_eq_of_mul_eq_one_right hmul]
  exact Subtype.mem _

theorem isUnit_of_inv_mem {F : Type} [Field F] (S : ValuationSubring F) (x : F) (hx : x ∈ S) (hx0 : x ≠ 0)
    (hinv : x⁻¹ ∈ S) : IsUnit (⟨x, hx⟩ : ↥S) :=
  isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

theorem ord_nonneg_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ≠ 0) (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem transcendental_of_forall_intPoly {κ B : Type} [Field κ] [Field B] [Algebra κ B] [IsAlgClosed κ]
    (q : ℕ) [Fact q.Prime] [Algebra (ZMod q) κ] [Algebra.IsAlgebraic (ZMod q) κ]
    (x : B) (hx : ∀ Φ : ℤ[X], Φ.map (Int.castRingHom κ) ≠ 0 → Φ.eval₂ (Int.castRingHom B) x ≠ 0) :
    Transcendental κ x := by
  intro halg

  have hint : IsIntegral κ x := halg.isIntegral
  have hirr : Irreducible (minpoly κ x) := minpoly.irreducible hint
  have hdeg : (minpoly κ x).degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible κ hirr
  have hmonic : (minpoly κ x).Monic := minpoly.monic hint
  set a : κ := -((minpoly κ x).coeff 0) with ha
  have hxa : x = algebraMap κ B a := by
    have h0 : Polynomial.aeval x (minpoly κ x) = 0 := minpoly.aeval κ x
    have hform := Polynomial.eq_X_add_C_of_degree_eq_one hdeg
    have hlc : (minpoly κ x).leadingCoeff = 1 := hmonic.leadingCoeff
    rw [hform, hlc, Polynomial.C_1, one_mul, map_add, Polynomial.aeval_X, Polynomial.aeval_C] at h0
    rw [ha, map_neg]
    exact eq_neg_of_add_eq_zero_left h0

  obtain ⟨ψ, hψ0, hψa⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ZMod q) a
  obtain ⟨Φ, hΦ⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod q)) (ZMod.intCast_surjective) ψ
  have hcomp : (algebraMap (ZMod q) κ).comp (Int.castRingHom (ZMod q)) = Int.castRingHom κ := RingHom.ext_int _ _
  have hΦκ : Φ.map (Int.castRingHom κ) = ψ.map (algebraMap (ZMod q) κ) := by
    rw [← hΦ, Polynomial.map_map, hcomp]
  apply hx Φ
  · rw [hΦκ]
    intro h0
    exact hψ0 ((Polynomial.map_eq_zero_iff (algebraMap (ZMod q) κ).injective).mp h0)
  · rw [← aeval_map_intCast (κ := κ), hΦκ, hxa, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_map_algebraMap,
      hψa, map_zero]

end IgIntSol

end

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open scoped MatrixGroups Polynomial

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open IgIntSol in
set_option maxHeartbeats 64000000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)

    (hGU : ∀ V : ValuationSubring ↥(modularFunctionFieldBar M'),
        (∀ a : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') a ∈ V ↔ a ∈ A) →
        ∀ hj : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) ∈ V,
          (∀ p : Polynomial (AlgebraicClosure ℚ), (∀ n, p.coeff n ∈ A) →
            (∃ hm : Polynomial.aeval (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) p ∈ V, (⟨_, hm⟩ : ↥V) ∈ maximalIdeal ↥V) →
              ∀ n, ∃ hc : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (p.coeff n) ∈ V, (⟨_, hc⟩ : ↥V) ∈ maximalIdeal ↥V) →
          ∀ f : ↥(modularFunctionFieldBar M'), f ∈ V ↔ f ∈ R₀.integers)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),

      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →

      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → (AlgebraicClosure ℚ)) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
    ∀ (W₀ : ValuationSubring ↥F₀),

      ((∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ W₀) ∧
      IsDiscreteValuationRing ↥W₀ ∧
      (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ W₀, maximalIdeal ↥W₀ = Ideal.span {(⟨_, hπW⟩ : ↥W₀)})) →

    ∀ (O : Subring ↥F₀) [IsLocalRing ↥O] [IsNoetherianRing ↥O],
      (∀ f : ↥F₀, f ∈ O → f ∈ W₀) →
      (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ O) →
      (∀ (f : ↥F₀) (hf : f ∈ O), ∃ (x : ↥k₀) (hx : algebraMap ↥k₀ ↥F₀ x ∈ O), (x : (AlgebraicClosure ℚ)) ∈ A ∧
              ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, hx⟩)) →

      (∀ f : ↥F₀, ∃ g h : ↥F₀, g ∈ O ∧ h ∈ O ∧ h ≠ 0 ∧ f * h = g) →
    ∀ (E₀ : ℕ) (_ : 1 ≤ E₀) (hπO : algebraMap ↥k₀ ↥F₀ π₀ ∈ O) (cx cy : ↥O) (u : (↥O)ˣ)
      (ι : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))
      (γU γV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))ˣ),
      cx * cy = (⟨_, hπO⟩ : ↥O) ^ E₀ * (u : ↥O) →
      (∀ (x : ↥k₀) (hx : (x : (AlgebraicClosure ℚ)) ∈ A) (hxO : algebraMap ↥k₀ ↥F₀ x ∈ O),
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hxO⟩) =
                  UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨x, hx⟩)) →
      ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cx) = (γU : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) →
      ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cy) = (γV : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) →
      ((cy : ↥F₀) ∈ W₀) → (∀ hcy : (cy : ↥F₀) ∈ W₀, (⟨(cy : ↥F₀), hcy⟩ : ↥W₀) ∈ maximalIdeal ↥W₀) →
      (∀ hcx : (cx : ↥F₀) ∈ W₀, (⟨(cx : ↥F₀), hcx⟩ : ↥W₀) ∉ maximalIdeal ↥W₀) →

    ∀ (Wx : ValuationSubring ↥F₀),
                (∀ f : ↥F₀, f ∈ O → f ∈ Wx) →
                (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ Wx) →
                IsDiscreteValuationRing ↥Wx →
                (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ Wx, maximalIdeal ↥Wx = Ideal.span {(⟨_, hπW⟩ : ↥Wx)}) →
                (∃ t : ↥Wx, ∀ p : Polynomial ↥k₀, (∀ n, ((p.coeff n : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
                  (∃ hm : Polynomial.aeval (t : ↥F₀) p ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                    ∀ n, ∃ hc : algebraMap ↥k₀ ↥F₀ (p.coeff n) ∈ Wx, (⟨_, hc⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                (∀ hcx : (cx : ↥F₀) ∈ Wx, (⟨(cx : ↥F₀), hcx⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                (∀ hcy : (cy : ↥F₀) ∈ Wx, (⟨(cy : ↥F₀), hcy⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) →
                (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
                  (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
                  (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                    0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                      ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
                    0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
                      ↥(modularFunctionFieldBar M'))) →
                  ∃ hF : (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(fieldBar q M')) ∈ F₀,
                    (⟨_, hF⟩ : ↥F₀) ∈ Wx ∧
                    (∀ hW : (⟨_, hF⟩ : ↥F₀) ∈ Wx, (⟨_, hW⟩ : ↥Wx) ∈ maximalIdeal ↥Wx ↔
                      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') = 0) ∧
                    ((R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                      (⟨_, hF⟩ : ↥F₀) ∈ O ∧
                      ∀ (hO : (⟨_, hF⟩ : ↥F₀) ∈ O) (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A) (hcO : algebraMap ↥k₀ ↥F₀ c ∈ O),
                        residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
                        ¬ IsUnit ((⟨_, hO⟩ : ↥O) - ⟨_, hcO⟩))) →

    ∀ (FI : Type) [Field FI] [Algebra (ResidueField ↥A) FI] (Rx : RegularProlongation A ↥(fieldBar q M') FI),
      (∀ f : ↥F₀, ((f : ↥(fieldBar q M')) ∈ Rx.integers ↔ f ∈ Wx)) →

      (∀ f : ↥(modularFunctionFieldBar M'),
        (IntermediateField.inclusion hle f : ↥(fieldBar q M')) ∈ Rx.integers ↔ f ∈ R₀.integers) := by
  intro F₀ hK1 hLD W₀ hK2 O instL instN hOW₀ hOk hOres hOfrac E₀ hE₀ hπO cx cy u ι γU γV hxy hconst hιx hιy hcyW₀ hcyW₀m
    hcxW₀m Wx hOWx hWxk₀ hWxdvr hWxunif hWxt hcxWxm hcyWxm hN3 FI instF instA Rx hRx
  classical
  haveI := hWxdvr

  set jhat : ↥(modularFunctionFieldBar M') := (⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
      ↥(modularFunctionFieldBar M')) with hjhat_def
  set incl : ↥(modularFunctionFieldBar M') →ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') := IntermediateField.inclusion hle
    with hincl_def

  have hqp : q.Prime := Fact.out
  haveI hQalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  have hqA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A := A.nonunits_subset hA
  have hqm : (⟨(q : AlgebraicClosure ℚ), hqA⟩ : ↥A) ∈ maximalIdeal ↥A := ValuationSubring.coe_mem_nonunits_iff.mp hA
  have hqκ : ((q : ℕ) : ResidueField ↥A) = 0 := by
    have h1 : ((q : ℕ) : ResidueField ↥A) = residue ↥A ⟨(q : AlgebraicClosure ℚ), hqA⟩ := by
      rw [← map_natCast (residue ↥A) q]
      congr 1
    rw [h1, residue_eq_zero_iff]
    exact hqm
  haveI hcharP : CharP (ResidueField ↥A) q := (CharP.charP_iff_prime_eq_zero hqp).mpr hqκ
  letI instZ : Algebra (ZMod q) (ResidueField ↥A) := ZMod.algebra _ q
  haveI : Algebra.IsAlgebraic (ZMod q) (ResidueField ↥A) :=
    ValuationSubring.algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat (AlgebraicClosure ℚ) A q
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A

  have hcoeA : coeffMap A.subtype (jqModC ↥A) = jqModC (AlgebraicClosure ℚ) := map_jqModC A.subtype
  have hjcoe : (jhat : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
    show coeffEmb (AlgebraicClosure ℚ) jq = _
    rw [← jqModC_rat]
    exact map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))
  have hjmem : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar M' := by
    rw [hcoeA, ← hjcoe]; exact jhat.2
  obtain ⟨hjR', hjres'⟩ := hR₀ (jqModC ↥A) hjmem
  have hjeq : (⟨coeffMap A.subtype (jqModC ↥A), hjmem⟩ : ↥(modularFunctionFieldBar M')) = jhat :=
    Subtype.ext (hcoeA.trans hjcoe.symm)
  have hjR : jhat ∈ R₀.integers := hjeq ▸ hjR'
  set jtil : modularFunctionFieldC (ResidueField ↥A) M' := R₀.residue ⟨jhat, hjR⟩ with hjtil_def
  have hjtil : (jtil : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) := by
    have h1 : (⟨jhat, hjR⟩ : ↥R₀.integers) = ⟨_, hjR'⟩ := Subtype.ext hjeq.symm
    rw [hjtil_def, h1, hjres']
    exact map_jqModC (IsLocalRing.residue ↥A)
  have hjtr : Transcendental (ResidueField ↥A) jtil := by
    have h := ModularCurve.transcendental_jqModC (ResidueField ↥A)
    rw [← hjtil] at h
    exact (transcendental_algebraMap_iff (R := ResidueField ↥A) (S := modularFunctionFieldC (ResidueField ↥A) M')
      (A := LaurentSeries (ResidueField ↥A)) Subtype.val_injective).mp h
  have hj0 : jhat ≠ 0 := by
    intro h0
    apply hjtr
    have : jtil = 0 := by
      rw [hjtil_def, show (⟨jhat, hjR⟩ : ↥R₀.integers) = 0 from Subtype.ext h0, map_zero]
    rw [this]
    exact isAlgebraic_zero

  obtain ⟨V, hVmem⟩ : ∃ V : ValuationSubring ↥(modularFunctionFieldBar M'), ∀ f, f ∈ V ↔ incl f ∈ Rx.integers :=
    ⟨Rx.integers.comap incl.toRingHom, fun f => ValuationSubring.mem_comap⟩
  have hVA : ∀ a : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') a ∈ V ↔ a ∈ A := by
    intro a; rw [hVmem, AlgHom.commutes]; exact Rx.algebraMap_mem_iff a
  have hcV : ∀ a : AlgebraicClosure ℚ, a ∈ A → algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') a ∈ V :=
    fun a ha => (hVA a).mpr ha

  have hjFull : jq ∈ modularFunctionFieldFull M' := modularFunctionField_le_full M' (jq_mem M')
  obtain ⟨hFj, hWxj, -, -⟩ := hN3 jq (modularFunctionField_le_full M' (jq_mem M')) hjR (fun P h => h)
  have hjRx : incl jhat ∈ Rx.integers := (hRx ⟨_, hFj⟩).mpr hWxj
  have hjV : jhat ∈ V := (hVmem _).mpr hjRx
  set jbar : FI := Rx.residue ⟨incl jhat, hjRx⟩ with hjbar_def

  have hint_test : ∀ Φ : ℤ[X], Φ.map (Int.castRingHom (ResidueField ↥A)) ≠ 0 →
      Φ.eval₂ (Int.castRingHom FI) jbar ≠ 0 := by
    intro Φ hΦ
    have hgFull : Φ.eval₂ (Int.castRingHom (LaurentSeries ℚ)) jq ∈ modularFunctionFieldFull M' :=
      eval₂_intCast_mem (modularFunctionFieldFull M') Φ hjFull

    have hgeq : (⟨coeffEmb (AlgebraicClosure ℚ) (Φ.eval₂ (Int.castRingHom (LaurentSeries ℚ)) jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgFull⟩ : ↥(modularFunctionFieldBar M')) =
        Φ.eval₂ (Int.castRingHom ↥(modularFunctionFieldBar M')) jhat := by
      apply Subtype.ext
      show coeffEmb (AlgebraicClosure ℚ) (Φ.eval₂ (Int.castRingHom (LaurentSeries ℚ)) jq) =
        (modularFunctionFieldBar M').val.toRingHom (Φ.eval₂ (Int.castRingHom ↥(modularFunctionFieldBar M')) jhat)
      rw [map_eval₂_intCast, map_eval₂_intCast]
      rfl
    have hgiΦ : (⟨coeffEmb (AlgebraicClosure ℚ) (Φ.eval₂ (Int.castRingHom (LaurentSeries ℚ)) jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgFull⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers := by
      rw [hgeq]; exact eval₂_intCast_mem R₀.integers Φ hjR
    have hcusp : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord (jhat : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (Φ.eval₂ (Int.castRingHom (LaurentSeries ℚ)) jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgFull⟩ : ↥(modularFunctionFieldBar M')) :
            ↥(modularFunctionFieldBar M')) := by
      intro P hP
      rw [hgeq]
      exact ord_nonneg_of_mem P (eval₂_intCast_mem P.toValuationSubring Φ (mem_of_ord_nonneg P hj0 hP))
    obtain ⟨hFΦ, hWxΦ, hbΦ, -⟩ := hN3 _ hgFull hgiΦ hcusp

    have hres0 : (R₀.residue ⟨_, hgiΦ⟩ : modularFunctionFieldC (ResidueField ↥A) M') =
        Φ.eval₂ (Int.castRingHom (modularFunctionFieldC (ResidueField ↥A) M')) jtil := by
      have h1 : (⟨_, hgiΦ⟩ : ↥R₀.integers) = Φ.eval₂ (Int.castRingHom ↥R₀.integers) ⟨jhat, hjR⟩ := by
        apply Subtype.ext
        show (⟨coeffEmb (AlgebraicClosure ℚ) (Φ.eval₂ (Int.castRingHom (LaurentSeries ℚ)) jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgFull⟩ : ↥(modularFunctionFieldBar M')) =
          R₀.integers.subtype (Φ.eval₂ (Int.castRingHom ↥R₀.integers) ⟨jhat, hjR⟩)
        rw [map_eval₂_intCast R₀.integers.subtype]
        exact hgeq
      rw [h1, map_eval₂_intCast]
    have hres0ne : (R₀.residue ⟨_, hgiΦ⟩ : modularFunctionFieldC (ResidueField ↥A) M') ≠ 0 := by
      rw [hres0, ← aeval_map_intCast (κ := ResidueField ↥A)]
      exact fun h0 => hjtr ⟨_, hΦ, h0⟩

    have hnotmax : (⟨_, hWxΦ⟩ : ↥Wx) ∉ maximalIdeal ↥Wx := fun hmx => hres0ne ((hbΦ hWxΦ).mp hmx)
    have hunitWx : IsUnit (⟨_, hWxΦ⟩ : ↥Wx) := by
      rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hnotmax
    have hinvWx := inv_mem_of_isUnit Wx ⟨_, hWxΦ⟩ hunitWx
    have hΦRx : incl (Φ.eval₂ (Int.castRingHom ↥(modularFunctionFieldBar M')) jhat) ∈ Rx.integers := by
      rw [← hgeq]; exact (hRx ⟨_, hFΦ⟩).mpr hWxΦ
    have hΦRxinv : (incl (Φ.eval₂ (Int.castRingHom ↥(modularFunctionFieldBar M')) jhat))⁻¹ ∈ Rx.integers := by
      rw [← hgeq]
      have := (hRx ⟨_, hFΦ⟩⁻¹).mpr hinvWx
      simpa using this
    have hΦ0 : incl (Φ.eval₂ (Int.castRingHom ↥(modularFunctionFieldBar M')) jhat) ≠ 0 := by
      intro h0
      have h1 : R₀.residue ⟨_, hgiΦ⟩ = 0 := by
        have : (⟨_, hgiΦ⟩ : ↥R₀.integers) = 0 := by
          apply Subtype.ext
          show (⟨coeffEmb (AlgebraicClosure ℚ) (Φ.eval₂ (Int.castRingHom (LaurentSeries ℚ)) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgFull⟩ : ↥(modularFunctionFieldBar M')) = 0
          rw [hgeq]
          exact (map_eq_zero_iff incl incl.toRingHom.injective).mp h0
        rw [this, map_zero]
      exact hres0ne h1
    have hunitRx : IsUnit (⟨_, hΦRx⟩ : ↥Rx.integers) := isUnit_of_inv_mem Rx.integers _ hΦRx hΦ0 hΦRxinv
    have hresRx : Rx.residue ⟨_, hΦRx⟩ = Φ.eval₂ (Int.castRingHom FI) jbar := by
      have h1 : (⟨_, hΦRx⟩ : ↥Rx.integers) = Φ.eval₂ (Int.castRingHom ↥Rx.integers) ⟨incl jhat, hjRx⟩ := by
        apply Subtype.ext
        rw [show ((Φ.eval₂ (Int.castRingHom ↥Rx.integers) ⟨incl jhat, hjRx⟩ : ↥Rx.integers) : ↥(fieldBar q M')) =
          Rx.integers.subtype (Φ.eval₂ (Int.castRingHom ↥Rx.integers) ⟨incl jhat, hjRx⟩) from rfl,
          map_eval₂_intCast Rx.integers.subtype]
        show incl (Φ.eval₂ (Int.castRingHom ↥(modularFunctionFieldBar M')) jhat) = _
        rw [map_eval₂_intCast' incl]
        rfl
      rw [h1, map_eval₂_intCast]
    rw [← hresRx]
    exact Rx.residue_ne_zero_of_isUnit hunitRx

  have hjbar_tr : Transcendental (ResidueField ↥A) jbar := transcendental_of_forall_intPoly q jbar hint_test

  have hunitP : ∀ p₁ : Polynomial (AlgebraicClosure ℚ), (∀ n, p₁.coeff n ∈ A) → (∃ n₀, p₁.coeff n₀ = 1) →
      ∃ hmem : incl (Polynomial.aeval jhat p₁) ∈ Rx.integers, IsUnit (⟨_, hmem⟩ : ↥Rx.integers) := by
    intro p₁ hpA ⟨n₀, hn₀⟩
    have hconstR : ∀ n, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (p₁.coeff n) ∈ Rx.integers :=
      fun n => (Rx.algebraMap_mem_iff _).mpr (hpA n)
    let T : ↥Rx.integers := ∑ n ∈ p₁.support,
      (⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (p₁.coeff n), hconstR n⟩ : ↥Rx.integers) *
        (⟨incl jhat, hjRx⟩ : ↥Rx.integers) ^ n
    have hT : (T : ↥(fieldBar q M')) = incl (Polynomial.aeval jhat p₁) := by
      rw [← Polynomial.aeval_algHom_apply, Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
      show Rx.integers.subtype T = _
      rw [map_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [map_mul, map_pow]
      rfl
    let pbar : Polynomial (ResidueField ↥A) := ∑ n ∈ p₁.support,
      Polynomial.C (IsLocalRing.residue ↥A ⟨p₁.coeff n, hpA n⟩) * Polynomial.X ^ n
    have hresT : Rx.residue T = Polynomial.aeval jbar pbar := by
      simp only [T, pbar, map_sum, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      congr 1
      exact Rx.residue_algebraMap ⟨p₁.coeff n, hpA n⟩
    have hpbar0 : pbar ≠ 0 := by
      intro h0
      have hcoeff : pbar.coeff n₀ = 1 := by
        simp only [pbar, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
        rw [Finset.sum_ite_eq p₁.support n₀]
        have hn₀s : n₀ ∈ p₁.support := Polynomial.mem_support_iff.mpr (by rw [hn₀]; exact one_ne_zero)
        rw [if_pos hn₀s]
        have : (⟨p₁.coeff n₀, hpA n₀⟩ : ↥A) = 1 := Subtype.ext hn₀
        rw [this, map_one]
      rw [h0, Polynomial.coeff_zero] at hcoeff
      exact zero_ne_one hcoeff
    have hresT0 : Rx.residue T ≠ 0 := by
      rw [hresT]
      exact fun h0 => hjbar_tr ⟨pbar, hpbar0, h0⟩
    have hTunit : IsUnit T := Rx.isUnit_of_residue_ne_zero hresT0
    have hmem : incl (Polynomial.aeval jhat p₁) ∈ Rx.integers := hT ▸ T.2
    refine ⟨hmem, ?_⟩
    have : (⟨_, hmem⟩ : ↥Rx.integers) = T := Subtype.ext hT.symm
    rw [this]; exact hTunit

  have hcmax : ∀ (a : AlgebraicClosure ℚ) (ha : a ∈ A), (⟨a, ha⟩ : ↥A) ∈ maximalIdeal ↥A →
      (⟨_, hcV a ha⟩ : ↥V) ∈ maximalIdeal ↥V := by
    intro a ha hma
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hma ⊢
    intro hu
    apply hma
    by_cases ha0 : a = 0
    · exfalso
      have : (⟨_, hcV a ha⟩ : ↥V) = 0 :=
        Subtype.ext (show algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') a = 0 by rw [ha0, map_zero])
      rw [this] at hu
      exact not_isUnit_zero hu
    have hinv : (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') a)⁻¹ ∈ V :=
      inv_mem_of_isUnit V ⟨_, hcV a ha⟩ hu
    rw [← map_inv₀, hVA] at hinv
    exact isUnit_of_inv_mem A a ha ha0 hinv

  have hresV : ∀ p : Polynomial (AlgebraicClosure ℚ), (∀ n, p.coeff n ∈ A) →
      (∃ hm : Polynomial.aeval jhat p ∈ V, (⟨_, hm⟩ : ↥V) ∈ maximalIdeal ↥V) →
        ∀ n, ∃ hc : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (p.coeff n) ∈ V,
          (⟨_, hc⟩ : ↥V) ∈ maximalIdeal ↥V := by
    intro p hpA hm' n
    obtain ⟨hm, hmax⟩ := hm'
    by_cases hp0 : p = 0
    · subst hp0
      refine ⟨by rw [Polynomial.coeff_zero, map_zero]; exact V.zero_mem, ?_⟩
      have : (⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') ((0 : Polynomial (AlgebraicClosure ℚ)).coeff n),
          by rw [Polynomial.coeff_zero, map_zero]; exact V.zero_mem⟩ : ↥V) = 0 :=
        Subtype.ext (show algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M')
          ((0 : Polynomial (AlgebraicClosure ℚ)).coeff n) = 0 by rw [Polynomial.coeff_zero, map_zero])
      rw [this]; exact Ideal.zero_mem _
    obtain ⟨c, p₁, n₀, hc0, hpp, hp₁A, hp₁⟩ := exists_eq_C_mul_of_ne_zero A p hp0
    obtain ⟨hT₁, hT₁u⟩ := hunitP p₁ hp₁A ⟨n₀, hp₁⟩
    have haeval : Polynomial.aeval jhat p =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') c * Polynomial.aeval jhat p₁ := by
      rw [hpp, map_mul, Polynomial.aeval_C]
    have hp₁0 : incl (Polynomial.aeval jhat p₁) ≠ 0 := by
      intro h0
      have : (⟨_, hT₁⟩ : ↥Rx.integers) = 0 := Subtype.ext h0
      rw [this] at hT₁u
      exact not_isUnit_zero hT₁u
    have hcRx : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c ∈ Rx.integers := by
      have h1 : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c =
          incl (Polynomial.aeval jhat p) * (incl (Polynomial.aeval jhat p₁))⁻¹ := by
        rw [haeval, map_mul, AlgHom.commutes, mul_assoc, mul_inv_cancel₀ hp₁0, mul_one]
      rw [h1]
      exact mul_mem ((hVmem _).mp hm) (inv_mem_of_isUnit Rx.integers ⟨_, hT₁⟩ hT₁u)
    have hcA : c ∈ A := (Rx.algebraMap_mem_iff c).mp hcRx
    have hcmaxA : (⟨c, hcA⟩ : ↥A) ∈ maximalIdeal ↥A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hcu
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmax
      apply hmax
      have hinvA : c⁻¹ ∈ A := inv_mem_of_isUnit A ⟨c, hcA⟩ hcu
      have hinv : (Polynomial.aeval jhat p)⁻¹ ∈ V := by
        rw [hVmem, map_inv₀, haeval, map_mul, AlgHom.commutes, mul_inv]
        refine mul_mem ?_ (inv_mem_of_isUnit Rx.integers ⟨_, hT₁⟩ hT₁u)
        rw [← map_inv₀]; exact (Rx.algebraMap_mem_iff _).mpr hinvA
      have hne : Polynomial.aeval jhat p ≠ 0 := by
        rw [haeval]
        refine mul_ne_zero ((map_ne_zero _).mpr hc0) (fun h0 => hp₁0 ?_)
        rw [h0, map_zero]
      exact isUnit_of_inv_mem V _ hm hne hinv
    have hcoeff : p.coeff n = c * p₁.coeff n := by rw [hpp, Polynomial.coeff_C_mul]
    refine ⟨hcV _ (hpA n), ?_⟩
    have hsplit : (⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (p.coeff n), hcV _ (hpA n)⟩ : ↥V) =
        ⟨_, hcV c hcA⟩ * ⟨_, hcV _ (hp₁A n)⟩ :=
      Subtype.ext (show algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (p.coeff n) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') c *
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (p₁.coeff n) by rw [hcoeff, map_mul])
    rw [hsplit]
    exact Ideal.mul_mem_right _ _ (hcmax c hcA hcmaxA)

  intro f
  exact (hVmem f).symm.trans (hGU V hVA hjV hresV f)

end S_ModularCurve_FullLevel_inclusion_mem_integers_iff_mem_constantReduction_integers_of_igusaEnd_igusaBranch
end P2MW
export P2MW.S_ModularCurve_FullLevel_inclusion_mem_integers_iff_mem_constantReduction_integers_of_igusaEnd_igusaBranch (solution)
