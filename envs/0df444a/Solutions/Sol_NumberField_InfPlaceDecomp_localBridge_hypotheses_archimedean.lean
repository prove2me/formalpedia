-- Prove2me | solution 1 for NumberField.InfPlaceDecomp.localBridge_hypotheses_archimedean
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7023e539-4598-5ed8-9e62-76afe1ccc431

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousH1
import Theorems.Thm_NumberField_InfinitePlace_exists_pow_eq_of_isTotallyComplex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfPlaceDecomp_localBridge_hypotheses_archimedean
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory groupCohomology NumberField P2MW.S_NumberField_InfPlaceDecomp_localBridge_hypotheses_archimedean.NumberField IsDedekindDomain ExtCitation"
p2m_open_scoped "NumberField.PlaceDecomp NumberField.InfPlaceDecomp P2MW.S_NumberField_InfPlaceDecomp_localBridge_hypotheses_archimedean.NumberField.InfPlaceDecomp"

namespace NumberField
p2m_export "NumberField" "IsTotallyComplex place InfinitePlace InfPlaceDecomp.decomp InfPlaceDecomp.localUnits InfinitePlace.exists_pow_eq_of_isTotallyComplex"
namespace InfPlaceDecomp
p2m_export "NumberField.InfPlaceDecomp" "decomp localUnits"
namespace ArchHyp
p2m_open "NumberField.InfPlaceDecomp NumberField"

lemma eq_one_or_eq_complexConjugation (s : ↥archimedeanDecomposition) :
    (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = 1 ∨ (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = complexConjugation := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 s.2
  rw [← hn]
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
  · left
    rw [zpow_mul, zpow_ofNat, complexConjugation_sq, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_ofNat, complexConjugation_sq, one_zpow, one_mul, zpow_one]

theorem lev (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ ↥F]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσF : σ⁻¹ * complexConjugation * σ ∉ F.fixingSubgroup) :
    ∀ s : ↥archimedeanDecomposition, archimedeanLoc s ∈ F.fixingSubgroup → s = 1 := by
  intro s hs
  rcases eq_one_or_eq_complexConjugation s with h | h
  · exact Subtype.ext h
  · exfalso
    apply hσF
    rw [IntermediateField.mem_fixingSubgroup_iff] at hs ⊢
    intro x hx

    have hσx : σ x ∈ F := by
      have := AlgEquiv.restrictNormal_commutes σ ↥F ⟨x, hx⟩

      convert ((σ.restrictNormal ↥F) ⟨x, hx⟩).2 using 1
      exact this.symm
    have hc : complexConjugation (σ x) = σ x := by
      have := hs (σ x) hσx
      rwa [show (archimedeanLoc s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = complexConjugation from h] at this
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hc, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

@[reducible] noncomputable def divisibleByInt (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (w : InfinitePlace K) :
    DivisibleBy (Additive (w.Completion)ˣ) ℤ :=
  haveI : DivisibleBy (Additive (w.Completion)ˣ) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn a => by
    obtain ⟨v, hv⟩ := NumberField.InfinitePlace.exists_pow_eq_of_isTotallyComplex K w (Additive.toMul a) n
      (Nat.pos_of_ne_zero hn)
    exact ⟨Additive.ofMul v, by change Additive.ofMul (v ^ n) = a; rw [hv]; rfl⟩
  AddGroup.divisibleByIntOfDivisibleByNat _

theorem div (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (w : InfinitePlace K) :
    ∀ (V W : Type) [AddCommGroup V] [AddCommGroup W] [Module.Free ℤ W] [Module.Finite ℤ W]
        (f : V →ₗ[ℤ] W) (_ : Function.Injective f) (φ : V →ₗ[ℤ] Additive (w.Completion)ˣ),
      ∃ ψ : W →ₗ[ℤ] Additive (w.Completion)ˣ, ∀ v : V, ψ (f v) = φ v := by
  intro V W _ _ _ _ f hf φ
  letI := divisibleByInt K w
  haveI : Module.Injective ℤ (Additive (w.Completion)ˣ) := (Module.Baer.of_divisible _).injective
  exact Module.Injective.out f hf φ

theorem h90_abstract {k : Type} [CommRing k] {H G : Type} [Group H] [Group G] (θ : H →* G) (hθ : Function.Injective θ)
    (c : H) (hc : c * c = 1) (hH : ∀ h : H, h = 1 ∨ h = c) (α : Type) (A : Rep k H)
    (u : cocycles₁ ((ihom (Rep.res θ (Rep.free k G α))).obj A)) :
    ∃ χ : (ihom (Rep.res θ (Rep.free k G α))).obj A, (d₀₁ _).hom χ = (u : H → _) := by
  classical
  have hPρ : ∀ (h : H) (a : α) (g : G) (r : k),
      (Rep.res θ (Rep.free k G α)).ρ h (Finsupp.single a (MonoidAlgebra.single g r)) = Finsupp.single a (MonoidAlgebra.single (θ h * g) r) :=
    fun h a g r => Representation.free_single_single (θ h) g a r
  have hu1 : (u : H → _) 1 = 0 := cocycles₁_map_one u
  by_cases hc1 : c = 1
  ·
    refine ⟨0, funext fun h => ?_⟩
    have hh : h = 1 := (hH h).elim id fun e => e.trans hc1
    rw [hh, d₀₁_hom_apply, map_one, Module.End.one_apply, sub_self, hu1]

  have hdd : θ c * θ c = 1 := by rw [← map_mul, hc, map_one]
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have hd1 : θ c ≠ 1 := fun h1 => hc1 (hθ (by rw [h1, map_one]))
  have hne : ∀ g : G, θ c * g ≠ g := fun g h => hd1 (by simpa using congrArg (· * g⁻¹) h)
  letI : LinearOrder G := linearOrderOfSTO WellOrderingRel

  have hcocy : (u : H → _) (c * c) = ((ihom (Rep.res θ (Rep.free k G α))).obj A).ρ c ((u : H → _) c) + (u : H → _) c :=
    (mem_cocycles₁_iff (u : H → _)).1 u.2 c c
  rw [hc, hu1] at hcocy
  set ν : (Rep.res θ (Rep.free k G α)) →ₗ[k] A := (u : H → _) c with hν
  have hνc : ∀ x : (Rep.res θ (Rep.free k G α)), A.ρ c (ν ((Rep.res θ (Rep.free k G α)).ρ c x)) = - ν x := by
    intro x
    have h := congrArg (fun f : (Rep.res θ (Rep.free k G α)) →ₗ[k] A => f x) hcocy
    erw [Rep.ihom_obj_ρ_apply] at h
    change (0 : (Rep.res θ (Rep.free k G α)) →ₗ[k] A) x = (A.ρ c ∘ₗ ν ∘ₗ (Rep.res θ (Rep.free k G α)).ρ c⁻¹ + ν) x at h
    rw [LinearMap.zero_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hcinv] at h
    exact eq_neg_of_add_eq_zero_left h.symm

  let val : α → G → A := fun a g =>
    if g < θ c * g then 0 else A.ρ c (ν (Finsupp.single a (MonoidAlgebra.single (θ c * g) 1)))
  let χ : (Rep.res θ (Rep.free k G α)) →ₗ[k] A := Finsupp.lsum k fun a =>
    (Finsupp.lsum k fun g => LinearMap.toSpanSingleton k A (val a g)) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap
  have hχ : ∀ (a : α) (g : G), χ (Finsupp.single a (MonoidAlgebra.single g 1)) = val a g := by
    intro a g
    change (Finsupp.lsum k fun a =>
      (Finsupp.lsum k fun g => LinearMap.toSpanSingleton k A (val a g)) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)
      (Finsupp.single a (MonoidAlgebra.single g 1)) = val a g
    rw [Finsupp.lsum_single, LinearMap.comp_apply, LinearEquiv.coe_coe, MonoidAlgebra.coeffLinearEquiv_apply,
      MonoidAlgebra.coeff_single, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, one_smul]
  refine ⟨χ, funext fun h => ?_⟩
  rcases hH h with rfl | rfl
  · rw [d₀₁_hom_apply, map_one, Module.End.one_apply, sub_self, hu1]
  · rw [d₀₁_hom_apply]
    erw [Rep.ihom_obj_ρ_apply]
    rw [hcinv]

    refine Finsupp.lhom_ext' fun a => MonoidAlgebra.lhom_ext' fun g => LinearMap.ext_ring ?_
    change A.ρ h (χ ((Rep.res θ (Rep.free k G α)).ρ h (Finsupp.single a (MonoidAlgebra.single g 1)))) - χ (Finsupp.single a (MonoidAlgebra.single g 1)) =
      ν (Finsupp.single a (MonoidAlgebra.single g 1))
    rw [hPρ, hχ, hχ]
    by_cases hlt : g < θ h * g
    ·
      have hlt' : ¬ θ h * g < θ h * (θ h * g) := by rw [← mul_assoc, hdd, one_mul]; exact not_lt.2 hlt.le
      simp only [val, if_pos hlt, if_neg hlt', sub_zero]
      rw [← mul_assoc, hdd, one_mul, ← Module.End.mul_apply, ← map_mul, hc, map_one, Module.End.one_apply]
    ·
      have hlt' : θ h * g < θ h * (θ h * g) := by
        rw [← mul_assoc, hdd, one_mul]
        exact lt_of_le_of_ne (not_lt.1 hlt) (hne g)
      simp only [val, if_neg hlt, if_pos hlt', map_zero, zero_sub]
      rw [← hPρ h a g 1, hνc, neg_neg]

end NumberField.InfPlaceDecomp.ArchHyp

open NumberField.InfPlaceDecomp.ArchHyp CategoryTheory groupCohomology _root_.NumberField _root_.P2MW.S_NumberField_InfPlaceDecomp_localBridge_hypotheses_archimedean.NumberField IsDedekindDomain ExtCitation in

theorem solution
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] [IsTotallyComplex ↥F]
    (w : InfinitePlace ↥F)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (πi : ↥archimedeanDecomposition →* ↥(NumberField.InfPlaceDecomp.decomp ℚ ↥F w))
    (hπ : ∀ h : ↥archimedeanDecomposition,
      ((πi h : ↥(NumberField.InfPlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
        AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * σ))
    (hπbij : Function.Bijective πi)
    (hσF : σ⁻¹ * complexConjugation * σ ∉ F.fixingSubgroup) :

    (∀ s : ↥archimedeanDecomposition, archimedeanLoc s ∈ F.fixingSubgroup → s = 1) ∧

    (∀ (V W : Type) [AddCommGroup V] [AddCommGroup W] [Module.Free ℤ W] [Module.Finite ℤ W]
        (f : V →ₗ[ℤ] W) (_ : Function.Injective f) (φ : V →ₗ[ℤ] Additive (w.Completion)ˣ),
      ∃ ψ : W →ₗ[ℤ] Additive (w.Completion)ˣ, ∀ v : V, ψ (f v) = φ v) ∧

    (∀ (α : Type) [Finite α]
        (u : groupCohomology.cocycles₁ ((ihom (Rep.res πi (Rep.res (NumberField.InfPlaceDecomp.decomp ℚ ↥F w).subtype
          (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) α)))).obj (Rep.res πi (NumberField.InfPlaceDecomp.localUnits ℚ ↥F w)))),
      ∃ χ : (ihom (Rep.res πi (Rep.res (NumberField.InfPlaceDecomp.decomp ℚ ↥F w).subtype (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) α)))).obj
          (Rep.res πi (NumberField.InfPlaceDecomp.localUnits ℚ ↥F w)),
        (groupCohomology.d₀₁ _).hom χ = (u : ↥archimedeanDecomposition → _)) := by
  have _ := hπ
  refine ⟨lev F σ hσF, div ↥F w, fun α _ u => ?_⟩

  have hθ : Function.Injective ((NumberField.InfPlaceDecomp.decomp ℚ ↥F w).subtype.comp πi) :=
    Subtype.val_injective.comp hπbij.1
  have hc : archimedeanGen * archimedeanGen = 1 := Subtype.ext complexConjugation_mul_self
  have hH : ∀ h : ↥archimedeanDecomposition, h = 1 ∨ h = archimedeanGen := fun h =>
    (eq_one_or_eq_complexConjugation h).imp Subtype.ext Subtype.ext
  exact h90_abstract ((NumberField.InfPlaceDecomp.decomp ℚ ↥F w).subtype.comp πi) hθ archimedeanGen hc hH α
    (Rep.res πi (NumberField.InfPlaceDecomp.localUnits ℚ ↥F w)) u

end S_NumberField_InfPlaceDecomp_localBridge_hypotheses_archimedean
end P2MW
export P2MW.S_NumberField_InfPlaceDecomp_localBridge_hypotheses_archimedean (solution)
