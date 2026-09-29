-- Prove2me | solution 1 for ModularCurve.FullLevel.aeval_eq_zero_imp_and_finiteDimensional_closure_descent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/f7171c62-619f-5f2e-a5b5-132f4643b9ab

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_ModularCurve_FullLevel_exists_admissible_smallConstants_botLayer_levelField_ringEquiv_of_descentBase
import Theorems.Thm_ModularCurve_FullLevel_transcendental_and_finiteDimensional_adjoin_levelField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_aeval_eq_zero_imp_and_finiteDimensional_closure_descent
p2m_attr_erase "instance" "DrinfeldCurve.instAlgebraCoordRing DrinfeldCurve.instCommRingCoordRing ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.RegularProlongation.coe_integersEquiv ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 16000000 in

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
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)
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

    (K₀ : Subfield (AlgebraicClosure ℚ)) [Algebra.IsAlgebraic ↥K₀ (AlgebraicClosure ℚ)] (hπK₀ : π ∈ K₀)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [HenselianLocalRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (hιK₀ : Set.range (fun a : A₀ => ((ι a : ↥A) : AlgebraicClosure ℚ)) =
      (A : Set (AlgebraicClosure ℚ)) ∩ (K₀ : Set (AlgebraicClosure ℚ)))
    (hres : Function.Surjective ((IsLocalRing.residue ↥A).comp ι))
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})

    (hϖ₀π : ((ι ϖ₀ : ↥A) : AlgebraicClosure ℚ) = π)

    (F₀ : Subfield ↥(fieldBar q M'))
    (hF₀ : ∀ f : ↥(fieldBar q M'), f ∈ F₀ ↔ ∀ n : ℤ, ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ K₀)

    (hjF₀ : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ F₀)

    [Algebra A₀ ↥F₀]
    (hj₀ : ∀ a : A₀, ((algebraMap A₀ ↥F₀ a : ↥F₀) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ)) :
    (∀ p : Polynomial A₀, Polynomial.aeval ((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀) p = 0 → p = 0) ∧
    FiniteDimensional ↥(Subfield.closure (Set.range (algebraMap A₀ ↥F₀) ∪ {(⟨_, hjF₀⟩ : ↥F₀)})) ↥F₀ := by
  classical
  obtain ⟨k₀, π₀, hπ₀, hk₀, -, -, -, -, -, -, -, -, -, hA₁, hK₁, -, -, ⟨e₀, he₀⟩, F₀', hCHAR, hK1', hSTAB, hLD, hRAT, hF₀eq, Φ, hΦ⟩ :=
    ModularCurve.FullLevel.exists_admissible_smallConstants_botLayer_levelField_ringEquiv_of_descentBase q hq M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀
  letI algk₀ : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra

  have hconstT : ∀ c : ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c : AlgebraicClosure ℚ) ∈ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') := by
    intro c
    apply (le_sup_left : IntermediateField.adjoin ↥k₀ _ ≤ (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀'))
    exact IntermediateField.subset_adjoin _ _ ⟨(c : AlgebraicClosure ℚ), c.2, rfl⟩
  let ρ : ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) →+* ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))).codRestrict (IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') hconstT
  letI algBT : Algebra ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') := ρ.toAlgebra
  have hcompat : ∀ c : ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), ((algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') c : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c : AlgebraicClosure ℚ) := fun _ => rfl
  have hj₁ : (((Φ (⟨_, hjF₀⟩ : ↥F₀) : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) jq := by
    have := hΦ (⟨_, hjF₀⟩ : ↥F₀)
    rw [this]; rfl
  obtain ⟨hTr, hFd⟩ := ModularCurve.FullLevel.transcendental_and_finiteDimensional_adjoin_levelField q M' k₀ ⊥ hK₁
    F₀' hK1' (hLD ⊥ hK₁) hRAT hcompat (Φ (⟨_, hjF₀⟩ : ↥F₀)) hj₁

  have hΦconst : ∀ a : A₀, Φ (algebraMap A₀ ↥F₀ a) = algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') ((e₀ a : ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ)))) : ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))) := by
    intro a
    apply Subtype.ext
    rw [hΦ, hj₀, hcompat, he₀]

  have hL₀A : ∀ a : A₀, algebraMap A₀ ↥F₀ a ∈ (Subfield.closure (Set.range (algebraMap A₀ ↥F₀) ∪ {(⟨_, hjF₀⟩ : ↥F₀)})) := fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
  have hL₀j : ((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀) ∈ (Subfield.closure (Set.range (algebraMap A₀ ↥F₀) ∪ {(⟨_, hjF₀⟩ : ↥F₀)})) := Subfield.subset_closure (Or.inr rfl)
  have hΦsymm_const : ∀ c : ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), Φ.symm (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') c) ∈ (Subfield.closure (Set.range (algebraMap A₀ ↥F₀) ∪ {(⟨_, hjF₀⟩ : ↥F₀)})) := by
    intro c
    rcases (A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))).mem_or_inv_mem c with hc | hc
    · obtain ⟨a, ha⟩ := e₀.surjective ⟨c, hc⟩
      have : algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') c = Φ (algebraMap A₀ ↥F₀ a) := by
        rw [hΦconst, ha]
      rw [this, RingEquiv.symm_apply_apply]; exact hL₀A a
    · obtain ⟨a, ha⟩ := e₀.surjective ⟨c⁻¹, hc⟩
      have : algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') c⁻¹ = Φ (algebraMap A₀ ↥F₀ a) := by
        rw [hΦconst, ha]
      have h2 : Φ.symm (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') c) = (algebraMap A₀ ↥F₀ a)⁻¹ := by
        rw [← RingEquiv.symm_apply_apply Φ (algebraMap A₀ ↥F₀ a), ← this, map_inv₀, map_inv₀, inv_inv]
      rw [h2]; exact inv_mem (hL₀A a)
  refine ⟨?_, ?_⟩
  ·
    intro p hp
    let σ : A₀ →+* ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) := (algebraMap ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))).comp e₀.toRingHom
    have hσinj : Function.Injective σ := fun a b h => e₀.injective (Subtype.ext h)
    have hcomp : (Φ : ↥F₀ →+* ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')).comp (algebraMap A₀ ↥F₀) = (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')).comp σ := by
      refine RingHom.ext (fun a => ?_)
      rw [RingHom.comp_apply, RingHom.comp_apply]
      exact hΦconst a
    have hmap : Polynomial.aeval (Φ (⟨_, hjF₀⟩ : ↥F₀)) (p.map σ) = Φ (Polynomial.aeval ((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀) p) := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hcomp, Polynomial.aeval_def]
      exact (Polynomial.hom_eval₂ p (algebraMap A₀ ↥F₀) (Φ : ↥F₀ →+* ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')) _).symm
    rw [hp, map_zero] at hmap
    have h0 : p.map σ = 0 := (transcendental_iff_injective.mp hTr) (by rw [hmap, map_zero])
    exact (Polynomial.map_injective σ hσinj) (by rw [h0, Polynomial.map_zero])
  ·
    let E := IntermediateField.adjoin ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ({Φ (⟨_, hjF₀⟩ : ↥F₀)} : Set ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀'))
    have hEmem : ∀ x : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀'), x ∈ E ↔ x ∈ Subfield.closure (Set.range (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')) ∪ {Φ (⟨_, hjF₀⟩ : ↥F₀)}) :=
      fun _ => Iff.rfl

    have hE_L₀ : ∀ x : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀'), x ∈ E → Φ.symm x ∈ (Subfield.closure (Set.range (algebraMap A₀ ↥F₀) ∪ {(⟨_, hjF₀⟩ : ↥F₀)})) := by
      intro x hx
      rw [hEmem] at hx
      have : Subfield.closure (Set.range (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')) ∪ {Φ (⟨_, hjF₀⟩ : ↥F₀)}) ≤ (Subfield.closure (Set.range (algebraMap A₀ ↥F₀) ∪ {(⟨_, hjF₀⟩ : ↥F₀)})).comap Φ.symm.toRingHom := by
        rw [Subfield.closure_le]
        rintro y (⟨c, rfl⟩ | hy)
        · exact hΦsymm_const c
        · rw [Set.mem_singleton_iff.mp hy]
          change Φ.symm (Φ (⟨_, hjF₀⟩ : ↥F₀)) ∈ (Subfield.closure (Set.range (algebraMap A₀ ↥F₀) ∪ {(⟨_, hjF₀⟩ : ↥F₀)}))
          rw [RingEquiv.symm_apply_apply]; exact hL₀j
      exact this hx

    have hL₀_E : ∀ y : ↥F₀, y ∈ (Subfield.closure (Set.range (algebraMap A₀ ↥F₀) ∪ {(⟨_, hjF₀⟩ : ↥F₀)})) → Φ y ∈ E := by
      intro y hy
      have : (Subfield.closure (Set.range (algebraMap A₀ ↥F₀) ∪ {(⟨_, hjF₀⟩ : ↥F₀)})) ≤ (E.toSubfield).comap (Φ : ↥F₀ →+* ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀')) := by
        rw [Subfield.closure_le]
        rintro z (⟨a, rfl⟩ | hz)
        · change Φ (algebraMap A₀ ↥F₀ a) ∈ E
          rw [hΦconst]; exact E.algebraMap_mem _
        · rw [Set.mem_singleton_iff.mp hz]
          exact IntermediateField.mem_adjoin_simple_self _ _
      exact this hy
    let f₁ : ↥E →+* ↥(Subfield.closure (Set.range (algebraMap A₀ ↥F₀) ∪ {(⟨_, hjF₀⟩ : ↥F₀)})) :=
      (Φ.symm.toRingHom.comp E.toSubfield.subtype).codRestrict (Subfield.closure (Set.range (algebraMap A₀ ↥F₀) ∪ {(⟨_, hjF₀⟩ : ↥F₀)})) (fun x => hE_L₀ x x.2)
    have hf₁bij : Function.Bijective f₁ := by
      refine ⟨fun a b h => Subtype.ext (Φ.symm.injective (congrArg Subtype.val h)), fun y => ?_⟩
      refine ⟨⟨Φ y, hL₀_E y y.2⟩, Subtype.ext ?_⟩
      change Φ.symm (Φ y) = y
      exact RingEquiv.symm_apply_apply Φ y
    let e₁ : ↥E ≃+* ↥(Subfield.closure (Set.range (algebraMap A₀ ↥F₀) ∪ {(⟨_, hjF₀⟩ : ↥F₀)})) := RingEquiv.ofBijective f₁ hf₁bij
    haveI : Module.Finite ↥E ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀') := hFd
    exact Module.Finite.of_equiv_equiv e₁ Φ.symm (by ext x; rfl)

end S_ModularCurve_FullLevel_aeval_eq_zero_imp_and_finiteDimensional_closure_descent
end P2MW
export P2MW.S_ModularCurve_FullLevel_aeval_eq_zero_imp_and_finiteDimensional_closure_descent (solution)
