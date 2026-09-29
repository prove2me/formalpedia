-- Prove2me | solution 1 for ModularCurve.FullLevel.not_mem_ssTube_of_centred_twoChartIntegralModel_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/d08ab2c5-4e53-5b45-a960-881f4c01e031

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ValuationSubring_ReduceAt
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_not_mem_ssTube_of_centred_twoChartIntegralModel_of_eq_three

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace L2Aux

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel IsLocalRing

universe u

section Overlap

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem exists_mid_of_ιFin_eq_ιInf (y : XFin R F j) (y' : XInf R F j)
    (h : (ιFin R F j).base y = (ιInf R F j).base y') :
    ∃ z : XMid R F j, (fFin R F j).base z = y ∧ (fInf R F j).base z = y' := by
  have h' : (colimit.ι (span (fFin R F j) (fInf R F j)) WalkingSpan.left).base y =
      (colimit.ι (span (fFin R F j) (fInf R F j)) WalkingSpan.right).base y' := h
  obtain ⟨k, fi, fj, z, h1, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff _).1 h'
  rcases k with (_ | _ | _)
  · have hfi : fi = WalkingSpan.Hom.fst := Subsingleton.elim _ _
    have hfj : fj = WalkingSpan.Hom.snd := Subsingleton.elim _ _
    subst hfi hfj
    exact ⟨z, h1, h2⟩
  · exact nomatch fj
  · exact nomatch fi

theorem exists_comap_eq_of_ιFin_eq_ιInf (y : XFin R F j) (y' : XInf R F j)
    (h : (ιFin R F j).base y = (ιInf R F j).base y') :
    ∃ z : XMid R F j, y.asIdeal = Ideal.comap (inclFin R F j).toRingHom z.asIdeal ∧
      y'.asIdeal = Ideal.comap (inclInf R F j).toRingHom z.asIdeal := by
  obtain ⟨z, h1, h2⟩ := exists_mid_of_ιFin_eq_ιInf R F j y y' h
  exact ⟨z, by rw [← h1]; rfl, by rw [← h2]; rfl⟩

theorem jInvChartInf_mem_of_not_mem_range (y' : XInf R F j)
    (hx : (ιInf R F j).base y' ∉ Set.range (ιFin R F j).base) :
    jInvChartInf R F j ∈ y'.asIdeal := by
  by_contra hj
  letI : Algebra (chartAlgInf R F j) (chartAlgMid R F j) := (inclInf R F j).toRingHom.toAlgebra
  haveI : IsLocalization.Away (jInvChartInf R F j) (chartAlgMid R F j) :=
    isLocalization_away_inclInf R F j
  have hdisj : Disjoint (↑(Submonoid.powers (jInvChartInf R F j)) : Set (chartAlgInf R F j))
      (↑y'.asIdeal : Set (chartAlgInf R F j)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hj (y'.isPrime.mem_of_pow_mem n hn)
  have hmem : y' ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (chartAlgInf R F j) (chartAlgMid R F j))) := by
    rw [PrimeSpectrum.localization_comap_range (chartAlgMid R F j)
      (Submonoid.powers (jInvChartInf R F j))]
    exact hdisj
  obtain ⟨z, hz⟩ := hmem
  apply hx
  have hglue : (ιFin R F j).base ((fFin R F j).base z) = (ιInf R F j).base ((fInf R F j).base z) :=
    congrArg (fun f => f.base z) (glue_condition R F j)
  refine ⟨(fFin R F j).base z, hglue.trans ?_⟩
  show (ιInf R F j).base (PrimeSpectrum.comap (inclInf R F j).toRingHom z) = _
  rw [← hz]
  rfl

theorem exists_inf_witness (z : XMid R F j) (b : chartAlgFin R F j) :
    ∃ (n : ℕ) (g : chartAlgInf R F j),
      (b : F) * ((jInvChartInf R F j ^ n : chartAlgInf R F j) : F) = (g : F) ∧
      jInvChartInf R F j ^ n ∉ Ideal.comap (inclInf R F j).toRingHom z.asIdeal ∧
      (b ∈ Ideal.comap (inclFin R F j).toRingHom z.asIdeal ↔
        g ∈ Ideal.comap (inclInf R F j).toRingHom z.asIdeal) := by
  have hj0 : j ≠ 0 := Fact.out
  have hb : (b : F) ∈ chartAlg R F (insert j⁻¹⁻¹ {j⁻¹}) := by
    rw [inv_inv]
    exact chartAlg_mono R F (Set.singleton_subset_iff.2 (Set.mem_insert j _)) b.2
  obtain ⟨n, hn⟩ := exists_pow_mul_mem_chartAlg (Set.mem_singleton j⁻¹) (inv_ne_zero hj0) hb
  have hu : IsUnit (inclInf R F j (jInvChartInf R F j) ^ n) := (isUnit_inclInf_jInvChartInf R F j).pow n
  have e1 : ∀ x, (inclInf R F j).toRingHom x = inclInf R F j x := fun _ => rfl
  have e2 : ∀ x, (inclFin R F j).toRingHom x = inclFin R F j x := fun _ => rfl
  refine ⟨n, ⟨j⁻¹ ^ n * b, hn⟩, ?_, ?_, ?_⟩
  · rw [Subalgebra.coe_pow, coe_jInvChartInf]
    ring
  · intro hmem
    rw [Ideal.mem_comap, e1, map_pow] at hmem
    exact z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)
  · rw [Ideal.mem_comap, Ideal.mem_comap, e1, e2]
    have hprod : inclInf R F j ⟨j⁻¹ ^ n * b, hn⟩ =
        inclInf R F j (jInvChartInf R F j) ^ n * inclFin R F j b := by
      apply Subtype.ext
      rw [Subalgebra.coe_mul, Subalgebra.coe_pow, coe_chartIncl, coe_chartIncl, coe_chartIncl,
        coe_jInvChartInf]
    rw [hprod, Ideal.unit_mul_mem_iff_mem _ hu]

end Overlap

section Eval

variable {K Fb : Type*} [Field K] [Field Fb] [Algebra K Fb] (P : Place K Fb)

noncomputable def resEquiv (hP : P.IsRational) : K ≃+* P.ResidueField :=
  RingEquiv.ofBijective (algebraMap K P.ResidueField) ⟨P.algebraMap_residueField_injective, hP⟩

noncomputable def evalHom (hP : P.IsRational) : P.toValuationSubring →+* K :=
  (resEquiv P hP).symm.toRingHom.comp (residue P.toValuationSubring)

theorem evalHom_apply (hP : P.IsRational) (f : P.toValuationSubring) :
    evalHom P hP f = P.evalAt (f : Fb) := by
  apply (resEquiv P hP).injective
  show resEquiv P hP ((resEquiv P hP).symm (residue _ f)) = algebraMap K P.ResidueField (P.evalAt (f : Fb))
  rw [RingEquiv.apply_symm_apply, Place.algebraMap_evalAt P hP f.2]

theorem evalAt_mul (hP : P.IsRational) {f g : Fb} (hf : f ∈ P.toValuationSubring)
    (hg : g ∈ P.toValuationSubring) : P.evalAt (f * g) = P.evalAt f * P.evalAt g := by
  have h := map_mul (evalHom P hP) ⟨f, hf⟩ ⟨g, hg⟩
  rw [evalHom_apply, evalHom_apply, evalHom_apply] at h
  exact h

end Eval

section Ker

variable {C K : Type*} [CommRing C] [Field K] (e : C →+* K) (A : ValuationSubring K)

noncomputable def toResidue (hA : ∀ c, e c ∈ A) : C →+* ResidueField A :=
  (residue A).comp (e.codRestrict A hA)

theorem toResidue_apply (hA : ∀ c, e c ∈ A) (c : C) :
    toResidue e A hA c = residue A ⟨e c, hA c⟩ := rfl

theorem ker_toResidue (hA : ∀ c, e c ∈ A) (I : Ideal C)
    (hI : ∀ c, A.valuation (e c) < 1 ↔ c ∈ I) : RingHom.ker (toResidue e A hA) = I := by
  ext c
  rw [RingHom.mem_ker, toResidue_apply, ← hI]
  show Ideal.Quotient.mk (maximalIdeal A) _ = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, ValuationSubring.valuation_lt_one_iff]

end Ker

end L2Aux

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 0 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    (R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hR : R.integers = OIg (lineInfty q))
    (hR₀O : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers ↔
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ OIg (lineInfty q))

    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ₀ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ₀⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (ζ₀ : ↥k₀) (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))

    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK₁ : FiniteDimensional ↥k₀ ↥K₁)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A)
    [IsDiscreteValuationRing ↥A₁] [HenselianLocalRing ↥A₁] :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra

    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ' γ f ∈ F₀) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →

    ∀ [Algebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)],
      (∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ)) →
    ∀ (j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))) →
    ∀ [Fact (j₁ ≠ 0)],

    let InStalk : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → Prop := fun x f =>
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)))
    let InMax : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → Prop := fun x f =>
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)))
    let Centred : Place (AlgebraicClosure ℚ) ↥(fieldBar q M') → ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun P x =>
      P.IsRational ∧ ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), InStalk x f →
        (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A ∧
          (A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ InMax x f)

    let GoodPt : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun x =>
      (AlgebraicCurve.TwoChartIntegralModel.toBase ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base x = closedPoint ↥A₁ ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), x ⤳ y → y = x) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* Ω), RingHom.ker φ = y.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ∉ ModularCurve.ssJSet q Ω)

    ∀ x : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), GoodPt x → ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), Centred P x →
      ∀ s : ↥W, ¬ (((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ P.toValuationSubring ∧
              (∀ a : A, residue A a = (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jGeomGen (ResidueField A) M') →
                ∃ h : P.evalAt (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                  (⟨_, h⟩ : A) ∈ maximalIdeal A)) ∧
            ((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq),
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jqN_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ P.toValuationSubring ∧
              (∀ a : A, residue A a = (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jNGeomGen (ResidueField A) M') →
                ∃ h : P.evalAt (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq),
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jqN_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                  (⟨_, h⟩ : A) ∈ maximalIdeal A))) := by
  classical
  intro F₀ hK1 hSTAB hLD hRAT instA₁ hA₁alg j₁ hj₁ instj₁ InStalk InMax Centred GoodPt x hx P hP s hTube
  obtain ⟨-, -, -, -, hx4⟩ := hx
  obtain ⟨hPrat, hPcen⟩ := hP
  obtain ⟨⟨hjP, hjval⟩, -⟩ := hTube
  rw [← hj₁] at hjP hjval
  haveI hcharP : CharP (ResidueField ↥A) q :=
    ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out : q.Prime) hA

  have hss : (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
      (jGeomGen (ResidueField A) M') ∈ ssJSet q (ResidueField ↥A) :=
    ((mem_ssPlaces_iff q M' (ResidueField ↥A)).1 ((hW s).1 s.2)).2.2
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := ↥A)
    ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
      (jGeomGen (ResidueField A) M'))
  obtain ⟨hdiffA, hdiffmax⟩ := hjval a ha
  have hjA : P.evalAt (j₁ : ↥(fieldBar q M')) ∈ A := by
    have := add_mem hdiffA a.2
    simpa using this
  have hresJ : IsLocalRing.residue ↥A ⟨P.evalAt (j₁ : ↥(fieldBar q M')), hjA⟩ ∈ ssJSet q (ResidueField ↥A) := by
    have h0 : IsLocalRing.residue ↥A ⟨P.evalAt (j₁ : ↥(fieldBar q M')) - (a : AlgebraicClosure ℚ), hdiffA⟩ = 0 := by
      show Ideal.Quotient.mk (maximalIdeal ↥A) _ = 0
      exact Ideal.Quotient.eq_zero_iff_mem.2 hdiffmax
    have h1 : (⟨P.evalAt (j₁ : ↥(fieldBar q M')), hjA⟩ : ↥A) =
        ⟨P.evalAt (j₁ : ↥(fieldBar q M')) - (a : AlgebraicClosure ℚ), hdiffA⟩ + a :=
      Subtype.ext (by simp)
    rw [h1, map_add, h0, zero_add, ha]
    exact hss
  have hjt0 : (j₁ : ↥(fieldBar q M')) ≠ 0 := fun h =>
    (Fact.out : j₁ ≠ 0) (Subtype.ext h)
  by_cases hfin : x ∈ Set.range (TwoChartIntegralModel.ιFin ↥A₁ _ j₁).base
  ·
    obtain ⟨y, hy⟩ := hfin
    have hov : ∀ y', (TwoChartIntegralModel.ιInf ↥A₁ _ j₁).base y' = x →
        ∃ z : TwoChartIntegralModel.XMid ↥A₁ _ j₁,
          y.asIdeal = Ideal.comap (TwoChartIntegralModel.inclFin ↥A₁ _ j₁).toRingHom z.asIdeal ∧
          y'.asIdeal = Ideal.comap (TwoChartIntegralModel.inclInf ↥A₁ _ j₁).toRingHom z.asIdeal :=
      fun y' hy' => L2Aux.exists_comap_eq_of_ιFin_eq_ιInf ↥A₁ _ j₁ y y' (hy.trans hy'.symm)

    have hStalk : ∀ b : ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁), InStalk x b.1 := by
      intro b
      refine ⟨fun y₂ _ => ⟨b, 1, (Ideal.ne_top_iff_one _).1 y₂.isPrime.ne_top, by simp⟩, fun y' hy' => ?_⟩
      obtain ⟨z, hzy, hzy'⟩ := hov y' hy'
      obtain ⟨n, g, hbg, hnot, -⟩ := L2Aux.exists_inf_witness ↥A₁ _ j₁ z b
      exact ⟨g, TwoChartIntegralModel.jInvChartInf ↥A₁ _ j₁ ^ n, by rwa [hzy'], hbg⟩

    have hMax : ∀ b : ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁), InMax x b.1 ↔ b ∈ y.asIdeal := by
      intro b
      constructor
      · rintro ⟨hF, -⟩
        obtain ⟨g, h, hh, hg, hbh⟩ := hF y hy
        have hbh' : b * h = g := Subtype.ext hbh
        have hmem : b * h ∈ y.asIdeal := by rw [hbh']; exact hg
        exact (y.isPrime.mem_or_mem hmem).resolve_right hh
      · intro hb
        refine ⟨fun y₂ hy₂ => ?_, fun y' hy' => ?_⟩
        · have hyy : y₂ = y :=
            (TwoChartIntegralModel.ιFin ↥A₁ _ j₁).isOpenEmbedding.injective (hy₂.trans hy.symm)
          subst hyy
          exact ⟨b, 1, (Ideal.ne_top_iff_one _).1 y₂.isPrime.ne_top, hb, by simp⟩
        · obtain ⟨z, hzy, hzy'⟩ := hov y' hy'
          obtain ⟨n, g, hbg, hnot, hiff⟩ := L2Aux.exists_inf_witness ↥A₁ _ j₁ z b
          refine ⟨g, TwoChartIntegralModel.jInvChartInf ↥A₁ _ j₁ ^ n, by rwa [hzy'], ?_, hbg⟩
          rw [hzy']
          exact hiff.1 (by rw [← hzy]; exact hb)
    have hC := fun b : ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁) => hPcen b.1 (hStalk b)

    let toF : ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁) →+* ↥(fieldBar q M') :=
      (algebraMap _ ↥(fieldBar q M')).comp (TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁).val.toRingHom
    have htoF : ∀ b, toF b = (b.1 : ↥(fieldBar q M')) := fun b => rfl
    let ev : ↥(TwoChartIntegralModel.chartAlgFin ↥A₁ _ j₁) →+* AlgebraicClosure ℚ :=
      (L2Aux.evalHom P hPrat).comp (toF.codRestrict P.toValuationSubring (fun b => (hC b).1))
    have hev : ∀ b, ev b = P.evalAt (b.1 : ↥(fieldBar q M')) := fun b =>
      L2Aux.evalHom_apply P hPrat _
    have hevA : ∀ b, ev b ∈ A := fun b => by rw [hev]; exact (hC b).2.1
    have hevI : ∀ b, A.valuation (ev b) < 1 ↔ b ∈ y.asIdeal := fun b => by
      rw [hev, (hC b).2.2]; exact hMax b
    have hker : RingHom.ker (L2Aux.toResidue ev A hevA) = y.asIdeal :=
      L2Aux.ker_toResidue ev A hevA _ hevI
    have hgood := hx4 y hy (ResidueField ↥A) (L2Aux.toResidue ev A hevA) hker
    apply hgood
    have hval : L2Aux.toResidue ev A hevA (TwoChartIntegralModel.jChartFin ↥A₁ _ j₁) =
        IsLocalRing.residue ↥A ⟨P.evalAt (j₁ : ↥(fieldBar q M')), hjA⟩ := by
      rw [L2Aux.toResidue_apply]
      congr 1
      apply Subtype.ext
      show ev (TwoChartIntegralModel.jChartFin ↥A₁ _ j₁) = P.evalAt (j₁ : ↥(fieldBar q M'))
      rw [hev, TwoChartIntegralModel.coe_jChartFin]
    rw [hval]
    exact hresJ
  ·
    rcases TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf ↥A₁ _ j₁ x with hfin' | ⟨y', hy'⟩
    · exact absurd hfin' hfin
    have hjinv : TwoChartIntegralModel.jInvChartInf ↥A₁ _ j₁ ∈ y'.asIdeal :=
      L2Aux.jInvChartInf_mem_of_not_mem_range ↥A₁ _ j₁ y' (by rw [hy']; exact hfin)
    have hone_not : ∀ y₂ : ↥(TwoChartIntegralModel.XInf ↥A₁ _ j₁),
        (1 : ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁)) ∉ y₂.asIdeal := fun y₂ =>
      (Ideal.ne_top_iff_one _).1 y₂.isPrime.ne_top
    have hcoeL : (j₁⁻¹ : _) * ((1 : ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁)) : _) =
        ((TwoChartIntegralModel.jInvChartInf ↥A₁ _ j₁ : ↥(TwoChartIntegralModel.chartAlgInf ↥A₁ _ j₁)) : _) := by
      rw [TwoChartIntegralModel.coe_jInvChartInf, OneMemClass.coe_one, mul_one]
    have hStalk : InStalk x (j₁⁻¹) :=
      ⟨fun y₂ hy₂ => absurd ⟨y₂, hy₂⟩ hfin,
        fun y₂ _ => ⟨TwoChartIntegralModel.jInvChartInf ↥A₁ _ j₁, 1, hone_not y₂, hcoeL⟩⟩
    have hMaxI : InMax x (j₁⁻¹) := by
      refine ⟨fun y₂ hy₂ => absurd ⟨y₂, hy₂⟩ hfin, fun y₂ hy₂ => ?_⟩
      have hyy : y₂ = y' :=
        (TwoChartIntegralModel.ιInf ↥A₁ _ j₁).isOpenEmbedding.injective (hy₂.trans hy'.symm)
      subst hyy
      exact ⟨TwoChartIntegralModel.jInvChartInf ↥A₁ _ j₁, 1, hone_not y₂, hjinv, hcoeL⟩
    obtain ⟨hinvP, hinvA, hinvlt⟩ := hPcen (j₁⁻¹) hStalk
    have hlt := hinvlt.2 hMaxI
    have hcoe : ((j₁⁻¹ : _) : ↥(fieldBar q M')) = (j₁ : ↥(fieldBar q M'))⁻¹ := rfl
    rw [hcoe] at hinvP hinvA hlt
    have hmax : (⟨P.evalAt (j₁ : ↥(fieldBar q M'))⁻¹, hinvA⟩ : ↥A) ∈ maximalIdeal ↥A :=
      (ValuationSubring.valuation_lt_one_iff A _).2 hlt
    have hone : (⟨P.evalAt (j₁ : ↥(fieldBar q M')), hjA⟩ : ↥A) *
        ⟨P.evalAt (j₁ : ↥(fieldBar q M'))⁻¹, hinvA⟩ = 1 := by
      apply Subtype.ext
      show P.evalAt (j₁ : ↥(fieldBar q M')) * P.evalAt (j₁ : ↥(fieldBar q M'))⁻¹ = 1
      rw [← L2Aux.evalAt_mul P hPrat hjP hinvP, mul_inv_cancel₀ hjt0, Place.evalAt_one]
    have h1 : (1 : ↥A) ∈ maximalIdeal ↥A := by
      rw [← hone]; exact Ideal.mul_mem_left _ _ hmax
    exact (Ideal.ne_top_iff_one _).1 (maximalIdeal.isMaximal ↥A).ne_top h1

end S_ModularCurve_FullLevel_not_mem_ssTube_of_centred_twoChartIntegralModel_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_not_mem_ssTube_of_centred_twoChartIntegralModel_of_eq_three (solution)
