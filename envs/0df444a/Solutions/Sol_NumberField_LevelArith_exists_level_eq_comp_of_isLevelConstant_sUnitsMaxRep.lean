-- Prove2me | solution 1 for NumberField.LevelArith.exists_level_eq_comp_of_isLevelConstant_sUnitsMaxRep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a13010e8-56b2-5fde-a670-898cb1334e2f

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Theorems.Thm_IntermediateField_exists_normal_isUnramifiedOutside_of_le
import Theorems.Thm_NumberField_LevelArith_normal_levelField_of_isNormalLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_level_eq_comp_of_isLevelConstant_sUnitsMaxRep

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain NumberField.LevelArith
open scoped NumberField.LevelArith

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (n : ℕ) (u : (Fin n → ↥L.fixingSubgroup) → sUnitsMaxRep S L)
    (hlc : (∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), F₀.IsUnramifiedOutside S ∧
        ∀ g s : Fin n → ↥L.fixingSubgroup,
          (∀ i, ((s i : ↥L.fixingSubgroup) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ F₀.fixingSubgroup) → u (g * s) = u g))
    (F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF₁ : L ≤ F₁) [FiniteDimensional ℚ ↥F₁] (hF₁ : F₁.IsUnramifiedOutside S) :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) (_ : F₁ ≤ F) (_ : FiniteDimensional ℚ ↥F) (_ : Normal ℚ ↥F)
      (_ : IsGalois ↥L ↥(levelField L F hLF)) (_ : F.IsUnramifiedOutside S)
      (f : (Fin n → (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) → ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))),
      ∀ g : Fin n → ↥L.fixingSubgroup, u g = ((f (fun i => (g i : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L) := by
  classical
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
  obtain ⟨F₀, hF₀, hu⟩ := hlc

  obtain ⟨F₂, hle₂, hF₂, hN₂⟩ :=
    IntermediateField.exists_normal_isUnramifiedOutside_of_le S (F₀ ⊔ F₁) (hF₀.sup hF₁)
  haveI := hN₂
  haveI : FiniteDimensional ℚ ↥F₂ := hF₂.1
  have hF₀F₂ : F₀ ≤ F₂ := le_sup_left.trans hle₂
  have hF₁F₂ : F₁ ≤ F₂ := le_sup_right.trans hle₂
  let U₂ : Subgroup ↥L.fixingSubgroup := F₂.fixingSubgroup.comap L.fixingSubgroup.subtype
  have hinv₂ : ∀ g s : Fin n → ↥L.fixingSubgroup, (∀ i, s i ∈ U₂) → u (g * s) = u g :=
    fun g s hs => hu g s fun i => IntermediateField.fixingSubgroup_antitone hF₀F₂ (hs i)

  have hval : ∀ x : sUnitsMaxRep S L, ∃ Fx : IntermediateField ℚ (AlgebraicClosure ℚ),
      Fx.IsUnramifiedOutside S ∧ ((sUnitsMaxRep.val S L x : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ Fx :=
    fun x => (sUnitsMaxStable_le S L x.2).1
  choose Fx hFx hxFx using hval

  haveI : Fintype (↥L.fixingSubgroup ⧸ U₂) := Subgroup.fintypeQuotientOfFiniteIndex
  let vals : Finset (sUnitsMaxRep S L) :=
    Finset.univ.image (fun q : Fin n → (↥L.fixingSubgroup ⧸ U₂) => u (fun i => (q i).out))
  let F₃ : IntermediateField ℚ (AlgebraicClosure ℚ) := F₂ ⊔ vals.sup (fun x => Fx x)
  have hF₃ : F₃.IsUnramifiedOutside S :=
    hF₂.sup (Finset.sup_induction (p := fun K : IntermediateField ℚ (AlgebraicClosure ℚ) => K.IsUnramifiedOutside S)
      (IntermediateField.isUnramifiedOutside_bot S) (fun a ha b hb => ha.sup hb) (fun x _ => hFx x))

  obtain ⟨F, hle, hF, hN⟩ := IntermediateField.exists_normal_isUnramifiedOutside_of_le S F₃ hF₃
  haveI := hN
  haveI : FiniteDimensional ℚ ↥F := hF.1
  have hF₂F : F₂ ≤ F := (le_sup_left : F₂ ≤ F₃).trans hle
  have hLF : L ≤ F := hLF₁.trans (hF₁F₂.trans hF₂F)

  have hnorm : IsNormalLevel L F := fun g _ s hs => by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hs ⊢
    intro x hx
    have hx' : g⁻¹ x ∈ F := (IntermediateField.normal_iff_forall_map_le'.1 hN g⁻¹) ⟨x, hx, rfl⟩
    have := hs _ hx'
    simp only [AlgEquiv.mul_apply]
    rw [this]
    simp
  haveI : Normal ↥L ↥(levelField L F hLF) := NumberField.LevelArith.normal_levelField_of_isNormalLevel L F hLF hnorm
  haveI : IsGalois ↥L ↥(levelField L F hLF) := ⟨⟩
  let UF : Subgroup ↥L.fixingSubgroup := F.fixingSubgroup.comap L.fixingSubgroup.subtype
  have hUF₂ : UF ≤ U₂ := groupCohomology.comap_fixingSubgroup_antitone _ hF₂F

  have hrep₂ : ∀ r : Fin n → ↥L.fixingSubgroup,
      u (fun i => ((r i : ↥L.fixingSubgroup ⧸ U₂)).out) = u r := fun r => by
    have hs : ∀ i, (r i)⁻¹ * ((r i : ↥L.fixingSubgroup ⧸ U₂)).out ∈ U₂ := fun i => by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    have := hinv₂ r (fun i => (r i)⁻¹ * ((r i : ↥L.fixingSubgroup ⧸ U₂)).out) hs
    simpa [Pi.mul_def, mul_inv_cancel_left] using this
  have hrepF : ∀ g : Fin n → ↥L.fixingSubgroup,
      u (fun i => ((g i : ↥L.fixingSubgroup ⧸ UF)).out) = u g := fun g => by
    have hs : ∀ i, (g i)⁻¹ * ((g i : ↥L.fixingSubgroup ⧸ UF)).out ∈ U₂ := fun i => hUF₂ (by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq'])
    have := hinv₂ g (fun i => (g i)⁻¹ * ((g i : ↥L.fixingSubgroup ⧸ UF)).out) hs
    simpa [Pi.mul_def, mul_inv_cancel_left] using this

  have hmemF : ∀ r : Fin n → ↥L.fixingSubgroup,
      ((sUnitsMaxRep.val S L (u r) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ F := fun r => by
    let q : Fin n → ↥L.fixingSubgroup ⧸ U₂ := fun i => (r i : ↥L.fixingSubgroup ⧸ U₂)
    have hq : u (fun i => (q i).out) ∈ vals := Finset.mem_image_of_mem _ (Finset.mem_univ q)
    have h3 : ((sUnitsMaxRep.val S L (u (fun i => (q i).out)) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ F₃ :=
      (le_sup_right : vals.sup (fun x => Fx x) ≤ F₃) (Finset.le_sup (f := fun x => Fx x) hq (hxFx _))
    rw [hrep₂ r] at h3
    exact hle h3
  refine ⟨F, hLF, hF₁F₂.trans hF₂F, inferInstance, hN, inferInstance, hF,
    fun x => ⟨u (fun i => (x i).out), fun γ => ?_⟩, fun g => (hrepF g).symm⟩

  have hγ : ((γ : ↥L.fixingSubgroup) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ F.fixingSubgroup := γ.2
  have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hγ _ (hmemF (fun i => (x i).out))
  have key : sUnitsMaxRep.val S L (((sUnitsMaxRep S L).ρ.comp UF.subtype) γ (u (fun i => (x i).out))) =
      sUnitsMaxRep.val S L (u (fun i => (x i).out)) := by
    rw [MonoidHom.comp_apply, sUnitsMaxRep.val_ρ]
    ext
    simpa using hfix
  exact Subtype.ext (Additive.toMul.injective key)

end S_NumberField_LevelArith_exists_level_eq_comp_of_isLevelConstant_sUnitsMaxRep
end P2MW
export P2MW.S_NumberField_LevelArith_exists_level_eq_comp_of_isLevelConstant_sUnitsMaxRep (solution)
