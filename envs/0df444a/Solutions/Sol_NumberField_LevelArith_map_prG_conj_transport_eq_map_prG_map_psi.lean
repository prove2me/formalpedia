-- Prove2me | solution 1 for NumberField.LevelArith.map_prG_conj_transport_eq_map_prG_map_psi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/42bff470-d555-57ca-86d8-90924ecab9c4

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_IdeleLocalInvariant
import Definitions.Def_NumberField_BrauerLocalInvariantChar
import Definitions.Def_NumberField_BrauerLocalInvariantPresentation
import Theorems.Thm_NumberField_LevelArith_levelGal_surjective_and_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_map_prG_conj_transport_eq_map_prG_map_psi

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits groupCohomology ExtCitation NumberField.LevelArith"
open scoped Classical NumberField.LevelArith TensorProduct Pointwise
open scoped NumberField NumberField.PlaceDecomp
open M4aHerbrand
open IsDedekindDomain
open NumberField

set_option maxHeartbeats 3200000 in
theorem solution
    (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [IsGalois ↥L ↥(levelField L F hLF)]

    (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (τ : ↥L ≃ₐ[ℚ] ↥L) (hστ : ∀ y : ↥L, σ (y : AlgebraicClosure ℚ) = ((τ y : ↥L) : AlgebraicClosure ℚ))
    (e : ↥(levelField L F hLF) ≃+* ↥(levelField L F hLF)) (he : ∀ y : ↥(levelField L F hLF), ((e y : ↥(levelField L F hLF)) : AlgebraicClosure ℚ) = σ ((y : ↥(levelField L F hLF)) : AlgebraicClosure ℚ))
    (c : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) ≃* (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) (hc : ∀ (g : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) (y : ↥(levelField L F hLF)), c g (e y) = e (g y))

    (pl : HeightOneSpectrum (𝓞 ↥(levelField L F hLF)) → HeightOneSpectrum (𝓞 ↥(levelField L F hLF))) (hpls : Function.Surjective pl)
    (hpl : ∀ (w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF))) (y : ↥(levelField L F hLF)), (pl w).valuation ↥(levelField L F hLF) (e y) = w.valuation ↥(levelField L F hLF) y)
    (Tc : ∀ w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF)), w.adicCompletion ↥(levelField L F hLF) ≃+* (pl w).adicCompletion ↥(levelField L F hLF))
    (hTc : ∀ (w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF))) (y : ↥(levelField L F hLF)), Tc w (y : w.adicCompletion ↥(levelField L F hLF)) = ((e y : ↥(levelField L F hLF)) : (pl w).adicCompletion ↥(levelField L F hLF)))
    [MulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ]
    (ψ : Rep.res c.symm.toMonoidHom (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) ⟶ Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)
    (hψ : ∀ (w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF))) (z : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ),
      finPart (pl w) (Additive.toMul (ψ.hom (Additive.ofMul z))) = Units.map (Tc w : w.adicCompletion ↥(levelField L F hLF) →* (pl w).adicCompletion ↥(levelField L F hLF)) (finPart w z))

    (ι : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) →* (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (hι : ∀ g : ↥L.fixingSubgroup, ι (levelGal L F hLF g) = (g : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (φ : Rep.res ι ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶ NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))
    (hφval : ∀ x, ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom x) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (j : NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) ⟶ Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)
    (hj : ∀ y, Additive.toMul (j.hom y) =
      Units.map (algebraMap ↥(levelField L F hLF) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) : ↥(levelField L F hLF) →* AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) y))
    (prG : ∀ w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF)),
      Rep.res (NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w).subtype (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w)) (w.adicCompletion ↥(levelField L F hLF))ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF))) (z : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ), (prG w).hom (Additive.ofMul z) = Additive.ofMul (finPart w z))

    (f fσ : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hffσ : ∀ s t s' t' : ↥L.fixingSubgroup, σ⁻¹ * (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = s' → σ⁻¹ * (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = t' →
        sUnitsMaxRep.val S L ((fσ ((s : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)), (t : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)
          = σ • sUnitsMaxRep.val S L ((f ((s' : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)), (t' : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)) :
    ∀ w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF)),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w).subtype (prG w) 2).hom ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ fσ))
        = (groupCohomology.map (NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w).subtype (prG w) 2).hom
            ((groupCohomology.map c.symm.toMonoidHom ψ 2).hom ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ f))) := by
  intro w₀
  obtain ⟨w, rfl⟩ := hpls w₀

  have hmem : ∀ s : ↥L.fixingSubgroup,
      σ⁻¹ * (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * σ ∈ L.fixingSubgroup := by
    intro s
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    have h1 : σ x = ((τ ⟨x, hx⟩ : ↥L) : AlgebraicClosure ℚ) := hστ ⟨x, hx⟩
    rw [h1, (IntermediateField.mem_fixingSubgroup_iff _ _).1 s.2 _ (τ ⟨x, hx⟩).2, ← h1,
      AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]

  have hcs : ∀ s : ↥L.fixingSubgroup, c.symm (levelGal L F hLF s) = levelGal L F hLF ⟨_, hmem s⟩ := by
    intro s
    apply AlgEquiv.ext
    intro y
    apply Subtype.ext
    have h1 := hc (c.symm (levelGal L F hLF s)) y
    rw [MulEquiv.apply_symm_apply] at h1
    have h2 := congrArg (fun z : ↥(levelField L F hLF) => (z : AlgebraicClosure ℚ)) h1
    rw [levelGal_apply_coe, he, he] at h2
    rw [levelGal_apply_coe]
    show _ = (σ⁻¹ * (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * σ) (y : AlgebraicClosure ℚ)
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.eq_symm_apply]
    exact h2.symm
  have hsurj : Function.Surjective (levelGal L F hLF) := (NumberField.LevelArith.levelGal_surjective_and_ker L F hLF).1

  have hlift : ∀ g : ↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF),
      ∃ s : ↥L.fixingSubgroup, ι g = ((s : ↥L.fixingSubgroup) : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)
        ∧ ι (c.symm g) = ((⟨_, hmem s⟩ : ↥L.fixingSubgroup) : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype) := by
    intro g
    refine ⟨(hsurj g).choose, ?_, ?_⟩
    · have h := hι (hsurj g).choose
      rw [(hsurj g).choose_spec] at h
      exact h
    · have h := hι ⟨_, hmem (hsurj g).choose⟩
      rw [← hcs, (hsurj g).choose_spec] at h
      exact h

  simp only [groupCohomology.H2π_comp_map_apply]
  congr 1
  apply Subtype.ext
  funext dd
  obtain ⟨d₁, d₂⟩ := dd
  show (prG (pl w)).hom ((φ ≫ j).hom (fσ (ι d₁, ι d₂)))
    = (prG (pl w)).hom (ψ.hom ((φ ≫ j).hom (f (ι (c.symm d₁), ι (c.symm d₂)))))

  refine (hlift d₁).elim fun s hs => (hlift d₂).elim fun t ht => ?_
  have hval : (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom (fσ (ι d₁, ι d₂))) : ↥(levelField L F hLF))
      = e (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom (f (ι (c.symm d₁), ι (c.symm d₂)))) : ↥(levelField L F hLF)) := by
    apply Subtype.ext
    refine (hφval _).trans ?_
    refine Eq.trans ?_ (he _).symm
    refine Eq.trans ?_ (congrArg σ (hφval _)).symm

    have e1 := congrArg (fun q => ((sUnitsMaxRep.val S L q : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
      (congrArg Subtype.val (congrArg₂ (fun a b => fσ (a, b)) hs.1 ht.1))
    have e2 := congrArg (fun q => σ ((sUnitsMaxRep.val S L q : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
      (congrArg Subtype.val (congrArg₂ (fun a b => f (a, b)) hs.2 ht.2))
    refine e1.trans (Eq.trans ?_ e2.symm)
    exact (congrArg Units.val (hffσ s t ⟨_, hmem s⟩ ⟨_, hmem t⟩ rfl rfl)).trans rfl

  have hL := (ofMul_toMul ((φ ≫ j).hom (fσ (ι d₁, ι d₂)))).symm.trans
    (congrArg Additive.ofMul (hj (φ.hom (fσ (ι d₁, ι d₂)))))
  have hL2 := (congrArg (prG (pl w)).hom hL).trans (hprG (pl w) _)
  have hR := (ofMul_toMul ((φ ≫ j).hom (f (ι (c.symm d₁), ι (c.symm d₂))))).symm.trans
    (congrArg Additive.ofMul (hj (φ.hom (f (ι (c.symm d₁), ι (c.symm d₂))))))
  have hR2 := ((congrArg (fun a => (prG (pl w)).hom (ψ.hom a)) hR).trans
    ((congrArg (prG (pl w)).hom (ofMul_toMul _).symm).trans
      ((hprG (pl w) _).trans (congrArg Additive.ofMul (hψ w _)))))
  refine hL2.trans (Eq.trans ?_ hR2.symm)
  refine congrArg Additive.ofMul (Units.ext ?_)
  simp only [coe_finPart_apply, Units.coe_map, MonoidHom.coe_coe, NumberField.AdeleRing.algebraMap_snd_apply]
  rw [hval]
  exact (hTc w _).symm

end S_NumberField_LevelArith_map_prG_conj_transport_eq_map_prG_map_psi
end P2MW
export P2MW.S_NumberField_LevelArith_map_prG_conj_transport_eq_map_prG_map_psi (solution)
