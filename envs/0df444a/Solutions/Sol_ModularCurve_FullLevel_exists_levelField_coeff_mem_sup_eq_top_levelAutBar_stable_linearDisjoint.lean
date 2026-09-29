-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_levelField_coeff_mem_sup_eq_top_levelAutBar_stable_linearDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/68a4e98e-fbad-5aba-b70d-741ff3d72117

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Mathlib
import Theorems.Thm_ModularCurve_FullLevel_arithmeticGalois_mul_ofAlgAut_levelAutBar_inv_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_levelField_coeff_mem_sup_eq_top_levelAutBar_stable_linearDisjoint

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace IGFieldAux

open ModularCurve

variable {E : Type*} [Field E] (ψ : E →+* AlgebraicClosure ℚ)
  (Fb : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))

noncomputable def coeffSubfield : Subfield ↥Fb :=
  (coeffMap ψ).fieldRange.comap (algebraMap ↥Fb (LaurentSeries (AlgebraicClosure ℚ)))

theorem mem_coeffSubfield_iff {f : ↥Fb} :
    f ∈ coeffSubfield ψ Fb ↔ ∃ g : LaurentSeries E, coeffMap ψ g = (f : LaurentSeries (AlgebraicClosure ℚ)) := by
  simp only [coeffSubfield, Subfield.mem_comap, RingHom.mem_fieldRange]
  rfl

theorem algebraMap_mem_coeffSubfield (e : E) :
    algebraMap (AlgebraicClosure ℚ) ↥Fb (ψ e) ∈ coeffSubfield ψ Fb := by
  rw [mem_coeffSubfield_iff]
  refine ⟨HahnSeries.single 0 e, ?_⟩
  rw [coeffMap_single, ← algebraMap_laurentSeries_eq_single]
  rfl

theorem forall_coeff_of_mem {f : ↥Fb} (hf : f ∈ coeffSubfield ψ Fb) (n : ℤ) :
    ∃ e : E, ψ e = (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n := by
  obtain ⟨g, hg⟩ := (mem_coeffSubfield_iff ψ Fb).1 hf
  exact ⟨g.coeff n, by rw [← hg, coeffMap_coeff]⟩

theorem mem_of_forall_coeff {f : ↥Fb}
    (hf : ∀ n : ℤ, ∃ e : E, ψ e = (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n) :
    f ∈ coeffSubfield ψ Fb := by
  choose c hc using hf
  rw [mem_coeffSubfield_iff]
  have hsupp : Function.support c = Function.support (f : LaurentSeries (AlgebraicClosure ℚ)).coeff := by
    ext n
    simp only [Function.mem_support, ne_eq]
    rw [← hc n, map_eq_zero_iff ψ ψ.injective]
  refine ⟨⟨c, ?_⟩, ?_⟩
  · rw [hsupp]; exact (f : LaurentSeries (AlgebraicClosure ℚ)).isPWO_support'
  · ext n
    rw [coeffMap_coeff]
    exact hc n

theorem coeffSubfield_mono {E' : Type*} [Field E'] (ψ' : E' →+* AlgebraicClosure ℚ) (χ : E →+* E')
    (h : ψ'.comp χ = ψ) : coeffSubfield ψ Fb ≤ coeffSubfield ψ' Fb := by
  intro f hf
  obtain ⟨g, hg⟩ := (mem_coeffSubfield_iff ψ Fb).1 hf
  rw [mem_coeffSubfield_iff]
  exact ⟨coeffMap χ g, by rw [coeffMap_coeffMap, h, hg]⟩

end IGFieldAux

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (ζq : ↥k₀) (hζq : IsPrimitiveRoot ((ζq : ↥k₀) : AlgebraicClosure ℚ) q) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∃ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),

      (∀ f : ↥(fieldBar q M'), f ∈ F₀ ↔ ∀ n : ℤ, ∃ c : ↥k₀, ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n = ((c : ↥k₀) : AlgebraicClosure ℚ)) ∧

      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) ∧

      (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ γ f ∈ F₀) ∧

      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → (AlgebraicClosure ℚ)) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) := by
  classical
  letI instAlg : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra

  let φ : ↥k₀ →+* AlgebraicClosure ℚ := algebraMap ↥k₀ (AlgebraicClosure ℚ)
  have hφFb : ∀ x : ↥k₀, algebraMap ↥k₀ ↥(fieldBar q M') x =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (φ x) := fun x => rfl

  let F₀ : IntermediateField ↥k₀ ↥(fieldBar q M') :=
    (IGFieldAux.coeffSubfield φ (fieldBar q M')).toIntermediateField (fun x => by
      rw [hφFb]; exact IGFieldAux.algebraMap_mem_coeffSubfield φ (fieldBar q M') x)
  have hmemF₀ : ∀ f : ↥(fieldBar q M'), f ∈ F₀ ↔ f ∈ IGFieldAux.coeffSubfield φ (fieldBar q M') := fun f => Iff.rfl

  have hIdx : ∀ ζ1 : Idx q, ζ1.val ∈ k₀ := by
    intro ζ1
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    obtain ⟨i, -, hi⟩ := hζq.eq_pow_of_pow_eq_one ζ1.isPrimitiveRoot.pow_eq_one
    rw [← hi]
    exact pow_mem ζq.2 i
  refine ⟨F₀, ?_, ?_, ?_, ?_⟩
  ·
    intro f
    rw [hmemF₀]
    constructor
    · intro hf n
      obtain ⟨e, he⟩ := IGFieldAux.forall_coeff_of_mem φ (fieldBar q M') hf n
      exact ⟨e, he.symm⟩
    · intro h
      apply IGFieldAux.mem_of_forall_coeff
      intro n
      obtain ⟨c, hc⟩ := h n
      exact ⟨c, hc.symm⟩
  ·
    rw [eq_top_iff]
    intro f _
    set E : IntermediateField ↥k₀ ↥(fieldBar q M') :=
      IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀
    have hf : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈
        Subfield.closure (Set.range (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) ∪
          (⇑(coeffEmb (AlgebraicClosure ℚ)) '' (xHFunctionField (q ^ 2 * M') (levelH q M') : Set (LaurentSeries ℚ)))) :=
      f.2
    have hle : Subfield.closure (Set.range (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) ∪
          (⇑(coeffEmb (AlgebraicClosure ℚ)) '' (xHFunctionField (q ^ 2 * M') (levelH q M') : Set (LaurentSeries ℚ)))) ≤
        E.toSubfield.map (algebraMap ↥(fieldBar q M') (LaurentSeries (AlgebraicClosure ℚ))) := by
      rw [Subfield.closure_le]
      rintro x (⟨a, rfl⟩ | ⟨z, hz, rfl⟩)
      · refine ⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a, ?_, rfl⟩
        show _ ∈ E
        exact le_sup_left (b := F₀) (IntermediateField.subset_adjoin ↥k₀ _ ⟨a, rfl⟩)
      · refine ⟨⟨coeffEmb (AlgebraicClosure ℚ) z, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hz⟩, ?_, rfl⟩
        show _ ∈ E
        refine le_sup_right (a := IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')))) ?_
        rw [hmemF₀, IGFieldAux.mem_coeffSubfield_iff]
        refine ⟨coeffMap (algebraMap ℚ ↥k₀) z, ?_⟩
        rw [coeffMap_coeffMap]
        exact coeffMap_congr (Subsingleton.elim _ _) z
    obtain ⟨e, he, hef⟩ := Subfield.mem_map.1 (hle hf)
    have : e = f := Subtype.ext hef
    exact this ▸ he
  ·

    intro ζ' γ hγ f hf
    rw [hmemF₀] at hf ⊢
    apply IGFieldAux.mem_of_forall_coeff
    intro n
    suffices hk : ((levelAutBar q M' ζ' γ f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ k₀ from
      ⟨⟨_, hk⟩, rfl⟩
    haveI : IsGalois ℚ (AlgebraicClosure ℚ) := by
      have hinst : (AlgebraicClosure.instAlgebra ℚ : Algebra ℚ (AlgebraicClosure ℚ)) =
          (inferInstance : Algebra ℚ (AlgebraicClosure ℚ)) := Subsingleton.elim _ _
      have h := @IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) inferInstance _
      rw [hinst] at h
      exact h
    rw [← InfiniteGalois.fixedField_fixingSubgroup k₀, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have hσ' : ∀ x : AlgebraicClosure ℚ, x ∈ k₀ → σ x = x := by
      rwa [IntermediateField.mem_fixingSubgroup_iff] at hσ
    have hζfix : σ⁻¹ • ζ' = ζ' := by
      apply Idx.ext
      rw [Idx.val_smul]
      nth_rewrite 1 [← hσ' _ (hIdx ζ')]
      simp
    have hcomm := ModularCurve.FullLevel.arithmeticGalois_mul_ofAlgAut_levelAutBar_inv_smul q M' hqM' σ ζ' γ hγ
    rw [hζfix] at hcomm
    have hAf : arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) σ • f = f := by
      apply Subtype.ext
      rw [coe_arithmeticGalois_smul]
      ext k
      rw [coeffMap_coeff]
      obtain ⟨y, hy⟩ := IGFieldAux.forall_coeff_of_mem _ _ hf k
      rw [← hy]
      exact hσ' _ y.2
    have h1 := congrArg (fun g => g • f) hcomm
    simp only [mul_smul, SemilinearAut.ofAlgAut_smul, hAf] at h1

    have h2 := congrArg (fun g : ↥(fieldBar q M') => (g : LaurentSeries (AlgebraicClosure ℚ)).coeff n) h1
    simp only [coe_arithmeticGalois_smul, coeffMap_coeff] at h2
    exact h2
  ·
    intro K' _ m c a ha hc hsum
    let ψ : ↥K' →+* AlgebraicClosure ℚ := algebraMap ↥K' (AlgebraicClosure ℚ)
    have hψφ : ψ.comp (algebraMap ↥k₀ ↥K') = φ := (IsScalarTower.algebraMap_eq ↥k₀ ↥K' (AlgebraicClosure ℚ)).symm
    let S' : IntermediateField ↥k₀ ↥(fieldBar q M') :=
      (IGFieldAux.coeffSubfield ψ (fieldBar q M')).toIntermediateField (fun x => by
        rw [hφFb, ← hψφ, RingHom.comp_apply]
        exact IGFieldAux.algebraMap_mem_coeffSubfield ψ (fieldBar q M') _)
    have hES : IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀ ≤ S' := by
      refine sup_le (IntermediateField.adjoin_le_iff.2 ?_) ?_
      · rintro x ⟨y, hy, rfl⟩
        exact IGFieldAux.algebraMap_mem_coeffSubfield ψ (fieldBar q M') ⟨y, hy⟩
      · intro f hf
        exact IGFieldAux.coeffSubfield_mono φ (fieldBar q M') ψ (algebraMap ↥k₀ ↥K') hψφ hf
    have hg : ∀ i, ∃ g : LaurentSeries ↥K', coeffMap ψ g = ((a i : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) :=
      fun i => (IGFieldAux.mem_coeffSubfield_iff ψ (fieldBar q M')).1 (hES (ha i))
    choose g hg using hg

    have hcoeff : ∀ n : ℤ, ∑ i, ((g i).coeff n) • c i = 0 := by
      intro n
      have h := congrArg (algebraMap ↥(fieldBar q M') (LaurentSeries (AlgebraicClosure ℚ))) hsum
      rw [map_sum, map_zero] at h
      simp_rw [map_mul, ← IsScalarTower.algebraMap_apply] at h
      have h2 := congrArg (fun x : LaurentSeries (AlgebraicClosure ℚ) => x.coeff n) h
      simp only [HahnSeries.coeff_sum, HahnSeries.coeff_zero] at h2
      simp_rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul] at h2
      have h3 : ∀ i, (algebraMap ↥(fieldBar q M') (LaurentSeries (AlgebraicClosure ℚ)) (a i)).coeff n =
          ψ ((g i).coeff n) := fun i => by
        rw [show algebraMap ↥(fieldBar q M') (LaurentSeries (AlgebraicClosure ℚ)) (a i) =
          ((a i : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) from rfl, ← hg i, coeffMap_coeff]
      simp only [h3] at h2
      simp only [Algebra.smul_def]
      rw [← h2]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    have hg0 : ∀ i, g i = 0 := by
      intro i
      ext n
      have := (Fintype.linearIndependent_iff.1 hc) (fun j => (g j).coeff n) (hcoeff n) i
      simpa using this
    intro i
    apply Subtype.ext
    rw [← hg i, hg0 i, map_zero]
    simp

end S_ModularCurve_FullLevel_exists_levelField_coeff_mem_sup_eq_top_levelAutBar_stable_linearDisjoint
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_levelField_coeff_mem_sup_eq_top_levelAutBar_stable_linearDisjoint (solution)
