-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.muBaseChange_toricLift_degeneracyHom_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/ab9a32bd-02b9-5925-83f7-2f5a06cf47b6

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_GoodReductionJacobian_abelianSchemePropertyBundle_fibreStr
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_comp_of_hom_spec_addMonoidAlgebra_pi_int
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_muBaseChange_toricLift_degeneracyHom_eq_one
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_muBaseChange_toricLift_degeneracyHom_eq_one.ModularCurve ModularCurve.JZeroNeronObjectAtP P2MW.S_ModularCurve_JZeroNeronObjectAtP_muBaseChange_toricLift_degeneracyHom_eq_one.ModularCurve.JZeroNeronObjectAtP"

universe u

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP"
namespace JZeroNeronObjectAtP
p2m_export "ModularCurve.JZeroNeronObjectAtP" "base resPt muStr torusCoord torusStr muToTorus muBaseChange torusPt LevelData toricLift_special toricLift L G degeneracyHom smooth torusFibre degeneracyHom_mul g torusFibre_mul toricRank"
namespace SpecialTriv
p2m_open "ModularCurve.JZeroNeronObjectAtP ModularCurve"

theorem eq_one_of_mul_self {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f)
    (h : G.mul t x x = x) : x = G.one t :=
  calc x = G.mul t (G.one t) x := (G.one_mul t x).symm
    _ = G.mul t (G.mul t (G.inv t x) x) x := by rw [G.inv_mul_cancel]
    _ = G.mul t (G.inv t x) (G.mul t x x) := by rw [G.mul_assoc]
    _ = G.mul t (G.inv t x) x := by rw [h]
    _ = G.one t := G.inv_mul_cancel t x

theorem abelianSchemePropertyBundle_baseChange_field {R : Type u} [CommRing R] {k : Type u} [Field k]
    (ι : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (hX : AbelianSchemePropertyBundle R f) :
    AbelianSchemePropertyBundle k (pullback.snd f ι) where
  smooth := MorphismProperty.pullback_snd (P := @Smooth) f ι hX.smooth
  proper := MorphismProperty.pullback_snd (P := @IsProper) f ι hX.proper
  connectedFibres s := by
    have hGI : GeometricallyIntegral f :=
      (GeometricallyIntegral.iff_geometricallyIntegral_fiber f).2 fun s =>
        (abelianSchemePropertyBundle_fibreStr hX s).geometricallyIntegral
    have hInt : IsIntegral (pullback f ι) :=
      pullback_of_geometrically hGI.geometrically_isIntegral k ι
    have huniv : (pullback.snd f ι).base ⁻¹' {s} = Set.univ :=
      Set.eq_univ_of_forall fun _ => Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [huniv]
    exact (IrreducibleSpace.isIrreducible_univ _).isConnected
  hasGroupLaw := hX.hasGroupLaw.map fun G => G.baseChange ι

end ModularCurve.JZeroNeronObjectAtP.SpecialTriv

open ModularCurve.JZeroNeronObjectAtP.SpecialTriv in

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m) (i : Fin 2) :
    muBaseChange (residue ↥A) O.toricRank m ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA ≫ (O.degeneracyHom i).1 =
      (Λ.L.one (muStr (ResidueField ↥A) O.toricRank m ≫ resPt A ≫ Λ.σA)).1 := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A

  rw [reassoc_of% (O.toricLift_special m hm)]

  have hφ : (O.torusFibre.1 ≫ pullback.fst O.g (resPt A ≫ Λ.σA) ≫ (O.degeneracyHom i).1) ≫ Λ.f =
      torusStr (ResidueField ↥A) O.toricRank ≫ resPt A ≫ Λ.σA := by
    rw [Category.assoc, Category.assoc, (O.degeneracyHom i).2, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ (resPt A ≫ Λ.σA)) O.torusFibre.2

  have hT : NeronModelInfra.schemeHomOverComp
      (torusPt (ResidueField ↥A) O.toricRank
        (1 : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)).ofConv)
      O.torusFibre = (O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) := by
    apply eq_one_of_mul_self
    have h := O.torusFibre_mul 1 1
    rw [mul_one] at h
    exact h.symm

  have hD : NeronModelInfra.schemeHomOverComp (O.L.one (𝟙 _ ≫ resPt A ≫ Λ.σA)) (O.degeneracyHom i) =
      Λ.L.one (𝟙 _ ≫ resPt A ≫ Λ.σA) := by
    apply eq_one_of_mul_self
    have h := O.degeneracyHom_mul i (𝟙 _ ≫ resPt A ≫ Λ.σA) (O.L.one _) (O.L.one _)
    rw [O.L.one_mul] at h
    exact h.symm

  obtain ⟨a, ha, hφa⟩ := AbelianSchemePropertyBundle.exists_eq_comp_of_hom_spec_addMonoidAlgebra_pi_int
    (abelianSchemePropertyBundle_baseChange_field (resPt A ≫ Λ.σA) hΛ.1) O.toricRank
    (pullback.lift (O.torusFibre.1 ≫ pullback.fst O.g (resPt A ≫ Λ.σA) ≫ (O.degeneracyHom i).1)
      (torusStr (ResidueField ↥A) O.toricRank) hφ)
    (pullback.lift_snd _ _ _)

  have ha' : a ≫ pullback.fst Λ.f (resPt A ≫ Λ.σA) = (Λ.L.one (𝟙 _ ≫ resPt A ≫ Λ.σA)).1 := by
    set e₁ := torusPt (ResidueField ↥A) O.toricRank
        (1 : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)).ofConv with he₁
    have h1 : e₁.1 ≫ O.torusFibre.1 = ((O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 := congrArg Subtype.val hT
    have h2 : (O.L.one (𝟙 _ ≫ resPt A ≫ Λ.σA)).1 ≫ (O.degeneracyHom i).1 = (Λ.L.one (𝟙 _ ≫ resPt A ≫ Λ.σA)).1 :=
      congrArg Subtype.val hD
    have h3 : ((O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 ≫ pullback.fst O.g (resPt A ≫ Λ.σA) =
        (O.L.one (𝟙 _ ≫ resPt A ≫ Λ.σA)).1 :=
      congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_one (resPt A ≫ Λ.σA) O.L (𝟙 _))
    have h4 : e₁.1 ≫ torusStr (ResidueField ↥A) O.toricRank = 𝟙 _ := e₁.2
    calc a ≫ pullback.fst Λ.f (resPt A ≫ Λ.σA)
        = (e₁.1 ≫ torusStr (ResidueField ↥A) O.toricRank) ≫ a ≫ pullback.fst Λ.f (resPt A ≫ Λ.σA) := by
          rw [h4, Category.id_comp]
      _ = e₁.1 ≫ (pullback.lift (O.torusFibre.1 ≫ pullback.fst O.g (resPt A ≫ Λ.σA) ≫ (O.degeneracyHom i).1)
            (torusStr (ResidueField ↥A) O.toricRank) hφ) ≫ pullback.fst Λ.f (resPt A ≫ Λ.σA) := by
          rw [hφa]; simp only [Category.assoc]
      _ = e₁.1 ≫ O.torusFibre.1 ≫ pullback.fst O.g (resPt A ≫ Λ.σA) ≫ (O.degeneracyHom i).1 := by
          rw [pullback.lift_fst]
      _ = (Λ.L.one (𝟙 _ ≫ resPt A ≫ Λ.σA)).1 := by
          rw [← Category.assoc, h1, ← Category.assoc, h3, h2]

  have hφ' : O.torusFibre.1 ≫ pullback.fst O.g (resPt A ≫ Λ.σA) ≫ (O.degeneracyHom i).1 =
      torusStr (ResidueField ↥A) O.toricRank ≫ (Λ.L.one (𝟙 _ ≫ resPt A ≫ Λ.σA)).1 := by
    rw [← pullback.lift_fst (O.torusFibre.1 ≫ pullback.fst O.g (resPt A ≫ Λ.σA) ≫ (O.degeneracyHom i).1)
      (torusStr (ResidueField ↥A) O.toricRank) hφ, hφa, Category.assoc, ha']
  rw [hφ']
  have hmu : muToTorus (ResidueField ↥A) O.toricRank m ≫ torusStr (ResidueField ↥A) O.toricRank =
      muStr (ResidueField ↥A) O.toricRank m := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AddMonoidAlgebra.mapDomainRingHom_comp_algebraMap]
  have hψ : (muToTorus (ResidueField ↥A) O.toricRank m ≫ torusStr (ResidueField ↥A) O.toricRank) ≫
      (𝟙 _ ≫ resPt A ≫ Λ.σA) = muStr (ResidueField ↥A) O.toricRank m ≫ resPt A ≫ Λ.σA := by
    rw [Category.id_comp, hmu]
  have h := congrArg Subtype.val
    (Λ.L.one_natural (𝟙 _ ≫ resPt A ≫ Λ.σA) (muStr (ResidueField ↥A) O.toricRank m ≫ resPt A ≫ Λ.σA)
      (muToTorus (ResidueField ↥A) O.toricRank m ≫ torusStr (ResidueField ↥A) O.toricRank) hψ)
  simpa only [GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc] using h

end S_ModularCurve_JZeroNeronObjectAtP_muBaseChange_toricLift_degeneracyHom_eq_one
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_muBaseChange_toricLift_degeneracyHom_eq_one (solution)
