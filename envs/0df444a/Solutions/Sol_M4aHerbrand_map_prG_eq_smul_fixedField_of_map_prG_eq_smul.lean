-- Prove2me | solution 1 for M4aHerbrand.map_prG_eq_smul_fixedField_of_map_prG_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/92f4b391-9e51-556a-b883-3b212a4de89c

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_exists_map_prG_eq_zsmul_of_map_prG_eq_zsmul_of_under_eq
import Theorems.Thm_ExtCitation_LocalLevel_isLocalFundamentalClass_map_subtype
import Theorems.Thm_ExtCitation_LocalLevel_isSolvable_of_faithfulSMul_of_padic
import Theorems.Thm_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion
import Theorems.Thm_NumberField_PlaceDecomp_faithfulSMul_decomp
import Theorems.Thm_NumberField_PlaceDecomp_mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_M4aHerbrand_map_prG_eq_smul_fixedField_of_map_prG_eq_smul
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_map_prG_eq_smul_fixedField_of_map_prG_eq_smul.M4aHerbrand"
open scoped NumberField.PlaceDecomp

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace M4aHerbrand
p2m_export "M4aHerbrand" "finPart repHomOfMulEquivariant repHomOfMulEquivariant_hom_apply IdeleGaloisDescent exists_map_prG_eq_zsmul_of_map_prG_eq_zsmul_of_under_eq"
namespace SylowReadH
p2m_open "M4aHerbrand"

section A
open scoped Pointwise
variable (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
  (H : Subgroup (F ≃ₐ[E] F))
  (Θ : ↥H ≃* (F ≃ₐ[↥(IntermediateField.fixedField H)] F))
  (hΘ : ∀ (s : ↥H) (y : F), Θ s y = (s : F ≃ₐ[E] F) y)

include hΘ in

theorem mem_decomp_iff (w : HeightOneSpectrum (𝓞 F)) (s : ↥H) :
    Θ s ∈ NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F w ↔ (s : F ≃ₐ[E] F) ∈ NumberField.PlaceDecomp.decomp E F w := by
  have key : (Θ s) • (w.valuation F).valuationSubring = (s : F ≃ₐ[E] F) • (w.valuation F).valuationSubring := by
    ext x
    rw [ValuationSubring.mem_smul_pointwise_iff_exists, ValuationSubring.mem_smul_pointwise_iff_exists]
    simp only [AlgEquiv.smul_def, hΘ]
  show Θ s ∈ MulAction.stabilizer _ _ ↔ (s : F ≃ₐ[E] F) ∈ MulAction.stabilizer _ _
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, key]

noncomputable def decompEquiv (w : HeightOneSpectrum (𝓞 F)) :
    ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F w) ≃* ↥(H.subgroupOf (NumberField.PlaceDecomp.decomp E F w)) where
  toFun t := ⟨⟨((Θ.symm t : ↥H) : F ≃ₐ[E] F), (mem_decomp_iff E F H Θ hΘ w (Θ.symm t)).1 (by rw [MulEquiv.apply_symm_apply]; exact t.2)⟩,
    by rw [Subgroup.mem_subgroupOf]; exact (Θ.symm t).2⟩
  invFun s := ⟨Θ ⟨((s : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F), Subgroup.mem_subgroupOf.1 s.2⟩,
    (mem_decomp_iff E F H Θ hΘ w _).2 (s : ↥(NumberField.PlaceDecomp.decomp E F w)).2⟩
  left_inv t := by
    apply Subtype.ext
    show Θ ⟨((Θ.symm t : ↥H) : F ≃ₐ[E] F), _⟩ = (t : F ≃ₐ[↥(IntermediateField.fixedField H)] F)
    rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
  right_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    show ((Θ.symm (Θ ⟨((s : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F), _⟩) : ↥H) : F ≃ₐ[E] F) = _
    rw [MulEquiv.symm_apply_apply]
  map_mul' t₁ t₂ := by
    apply Subtype.ext
    apply Subtype.ext
    show ((Θ.symm ((t₁ * t₂ : ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F w)) :
        F ≃ₐ[↥(IntermediateField.fixedField H)] F) : ↥H) : F ≃ₐ[E] F) =
      ((Θ.symm (t₁ : F ≃ₐ[↥(IntermediateField.fixedField H)] F) : ↥H) : F ≃ₐ[E] F) * ((Θ.symm (t₂ : F ≃ₐ[↥(IntermediateField.fixedField H)] F) : ↥H) : F ≃ₐ[E] F)
    rw [Subgroup.coe_mul, map_mul, Subgroup.coe_mul]

theorem coe_decompEquiv (w : HeightOneSpectrum (𝓞 F)) (t : ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F w)) :
    (((decompEquiv E F H Θ hΘ w t : ↥(H.subgroupOf (NumberField.PlaceDecomp.decomp E F w))) : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) =
      ((Θ.symm t : ↥H) : F ≃ₐ[E] F) := rfl

include hΘ in

theorem ringEquiv_eq (t : F ≃ₐ[↥(IntermediateField.fixedField H)] F) :
    ((t : F ≃ₐ[↥(IntermediateField.fixedField H)] F) : F ≃+* F) = (((Θ.symm t : ↥H) : F ≃ₐ[E] F) : F ≃+* F) := by
  apply RingEquiv.ext
  intro y
  show t y = ((Θ.symm t : ↥H) : F ≃ₐ[E] F) y
  rw [← hΘ, MulEquiv.apply_symm_apply]

@[elab_as_elim]
private theorem adicCompletion_induction_on {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] {u : IsDedekindDomain.HeightOneSpectrum R}
    {p : u.adicCompletion K → Prop} (x : u.adicCompletion K) (hp : IsClosed {x | p x})
    (ih : ∀ k : WithVal (u.valuation K), p k) : p x := by
  obtain ⟨y, rfl⟩ := IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion_surjective K u x
  exact UniformSpace.Completion.induction_on
    (p := fun y => p (IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion y)) y
    (hp.preimage (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion K u)) ih

theorem smul_adicCompletion_eq (w : HeightOneSpectrum (𝓞 F)) (t : ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F w))
    (y : w.adicCompletion F) :
    t • y = ((decompEquiv E F H Θ hΘ w t : ↥(H.subgroupOf (NumberField.PlaceDecomp.decomp E F w))) : ↥(NumberField.PlaceDecomp.decomp E F w)) • y := by
  rw [NumberField.PlaceDecomp.smul_def, NumberField.PlaceDecomp.smul_def]
  induction y using adicCompletion_induction_on with
  | hp =>
    exact isClosed_eq (NumberField.PlaceDecomp.continuous_actRingEquiv _) (NumberField.PlaceDecomp.continuous_actRingEquiv _)
  | ih a =>
    rw [NumberField.PlaceDecomp.actRingEquiv_coe, NumberField.PlaceDecomp.actRingEquiv_coe, coe_decompEquiv, ringEquiv_eq E F H Θ hΘ]

theorem smul_units_eq (w : HeightOneSpectrum (𝓞 F)) (t : ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F w))
    (y : (w.adicCompletion F)ˣ) :
    t • y = ((decompEquiv E F H Θ hΘ w t : ↥(H.subgroupOf (NumberField.PlaceDecomp.decomp E F w))) : ↥(NumberField.PlaceDecomp.decomp E F w)) • y := by
  apply Units.ext
  rw [NumberField.PlaceDecomp.coe_smul_units, NumberField.PlaceDecomp.coe_smul_units, smul_adicCompletion_eq]

end A

end M4aHerbrand.SylowReadH

namespace M4aHerbrand
p2m_export "M4aHerbrand" "finPart repHomOfMulEquivariant repHomOfMulEquivariant_hom_apply IdeleGaloisDescent exists_map_prG_eq_zsmul_of_map_prG_eq_zsmul_of_under_eq"
namespace SylowReadH
p2m_open "M4aHerbrand"

theorem map_congr {G K : Type} [Group G] [Group K] {A : Rep ℤ K} {B : Rep ℤ G} {f f' : G →* K} (h : f = f')
    (φ : Rep.res f A ⟶ B) (φ' : Rep.res f' A ⟶ B) (hφ : ∀ x, φ.hom x = φ'.hom x) (n : ℕ) :
    groupCohomology.map f φ n = groupCohomology.map f' φ' n := by
  subst h
  have hh : φ = φ' := Rep.hom_ext (DFunLike.ext _ _ hφ)
  rw [hh]

theorem finPart_smul_of_prG (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (H : Subgroup (F ≃ₐ[E] F))
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (prG : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    (w : HeightOneSpectrum (𝓞 F)) (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (t : (AdeleRing (𝓞 F) F)ˣ) :
    finPart w ((g : F ≃ₐ[E] F) • t) = g • finPart w t := by
  have hh := Rep.hom_comm_apply (prG w) g (Additive.ofMul t)
  rw [Rep.coe_res_obj_ρ', Rep.ofMulDistribMulAction_ρ_apply_apply, Rep.ofMulDistribMulAction_ρ_apply_apply] at hh
  erw [hprG, hprG] at hh
  exact Additive.ofMul.injective hh

noncomputable def kappa (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (H : Subgroup (F ≃ₐ[E] F))
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (prG : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    (Θ : ↥H ≃* (F ≃ₐ[↥(IntermediateField.fixedField H)] F))
    (hΘ : ∀ (s : ↥H) (y : F), Θ s y = (s : F ≃ₐ[E] F) y) (w : HeightOneSpectrum (𝓞 F)) :
    Rep.res ((Θ.symm : (F ≃ₐ[↥(IntermediateField.fixedField H)] F) ≃* ↥H).toMonoidHom.comp (NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F w).subtype)
        (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F w)) (w.adicCompletion F)ˣ :=
  Rep.ofHom
    { toLinearMap := (MonoidHom.toAdditive (finPart (R := 𝓞 F) (F := F) w)).toIntLinearMap
      isIntertwining' := fun t => by
        apply LinearMap.ext
        intro z
        obtain ⟨y, rfl⟩ : ∃ y, Additive.ofMul y = z := ⟨Additive.toMul z, rfl⟩
        have key := finPart_smul_of_prG E F H prG hprG w
          ((decompEquiv E F H Θ hΘ w t : ↥(H.subgroupOf (NumberField.PlaceDecomp.decomp E F w))) : ↥(NumberField.PlaceDecomp.decomp E F w)) y
        rw [← smul_units_eq E F H Θ hΘ w t] at key
        simp only [LinearMap.comp_apply]
        exact congrArg Additive.ofMul key }

theorem kappa_hom_apply (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (H : Subgroup (F ≃ₐ[E] F))
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (prG : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    (Θ : ↥H ≃* (F ≃ₐ[↥(IntermediateField.fixedField H)] F))
    (hΘ : ∀ (s : ↥H) (y : F), Θ s y = (s : F ≃ₐ[E] F) y) (w : HeightOneSpectrum (𝓞 F)) (y : (AdeleRing (𝓞 F) F)ˣ) :
    (kappa E F H prG hprG Θ hΘ w).hom (Additive.ofMul y) = Additive.ofMul (finPart w y) := rfl

noncomputable def xi (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (H : Subgroup (F ≃ₐ[E] F))
    (Θ : ↥H ≃* (F ≃ₐ[↥(IntermediateField.fixedField H)] F))
    (hΘ : ∀ (s : ↥H) (y : F), Θ s y = (s : F ≃ₐ[E] F) y) (w : HeightOneSpectrum (𝓞 F)) :
    Rep.res (decompEquiv E F H Θ hΘ w).toMonoidHom
        (Rep.res (H.subgroupOf (NumberField.PlaceDecomp.decomp E F w)).subtype
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F w)) (w.adicCompletion F)ˣ :=
  Rep.ofHom
    { toLinearMap := (AddMonoidHom.id (Additive (w.adicCompletion F)ˣ)).toIntLinearMap
      isIntertwining' := fun t => by
        apply LinearMap.ext
        intro z
        obtain ⟨y, rfl⟩ : ∃ y, Additive.ofMul y = z := ⟨Additive.toMul z, rfl⟩
        have key := (smul_units_eq E F H Θ hΘ w t y).symm
        simp only [LinearMap.comp_apply]
        exact congrArg Additive.ofMul key }

theorem xi_hom_apply (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (H : Subgroup (F ≃ₐ[E] F))
    (Θ : ↥H ≃* (F ≃ₐ[↥(IntermediateField.fixedField H)] F))
    (hΘ : ∀ (s : ↥H) (y : F), Θ s y = (s : F ≃ₐ[E] F) y) (w : HeightOneSpectrum (𝓞 F)) (m) : (xi E F H Θ hΘ w).hom m = m := rfl

theorem coord_fixedField_eq (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (H : Subgroup (F ≃ₐ[E] F))
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (prG : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    [MulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField H)] F) (AdeleRing (𝓞 F) F)ˣ]
    (prG' : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField H)] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F w)) (w.adicCompletion F)ˣ)
    (hprG' : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG' w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    (Θ : ↥H ≃* (F ≃ₐ[↥(IntermediateField.fixedField H)] F))
    (hΘ : ∀ (s : ↥H) (y : F), Θ s y = (s : F ≃ₐ[E] F) y)
    (ψ : Rep.res Θ.toMonoidHom (Rep.ofMulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField H)] F) (AdeleRing (𝓞 F) F)ˣ) ⟶ Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ))
    (hψ : ∀ y, ψ.hom y = y)
    (w : HeightOneSpectrum (𝓞 F))
    (x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2)
    (x' : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField H)] F) (AdeleRing (𝓞 F) F)ˣ) 2)
    (hx' : (groupCohomology.map Θ.toMonoidHom ψ 2).hom x' =
      (groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ))) 2).hom x) :
    (groupCohomology.map (NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F w).subtype (prG' w) 2).hom x' =
      (groupCohomology.map (decompEquiv E F H Θ hΘ w).toMonoidHom (xi E F H Θ hΘ w) 2).hom
        ((groupCohomology.map (H.subgroupOf (NumberField.PlaceDecomp.decomp E F w)).subtype
            (𝟙 (Rep.res (H.subgroupOf (NumberField.PlaceDecomp.decomp E F w)).subtype
              (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ))) 2).hom
          ((groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype (prG w) 2).hom x)) := by

  set j : ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F w) →* ↥H :=
    (Θ.symm : (F ≃ₐ[↥(IntermediateField.fixedField H)] F) ≃* ↥H).toMonoidHom.comp (NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F w).subtype with hj

  have h₁ : (NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F w).subtype = Θ.toMonoidHom.comp j := by
    ext t
    simp [hj]
  have hL := map_congr h₁ (prG' w) ((Rep.resFunctor j).map ψ ≫ kappa E F H prG hprG Θ hΘ w) (fun z => by
    obtain ⟨y, rfl⟩ : ∃ y, Additive.ofMul y = z := ⟨Additive.toMul z, rfl⟩
    rw [hprG', Rep.hom_comp]
    show _ = (kappa E F H prG hprG Θ hΘ w).hom (ψ.hom (Additive.ofMul y))
    rw [hψ]
    rfl) 2
  rw [hL, groupCohomology.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hx', ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
    ← groupCohomology.map_comp]

  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← groupCohomology.map_comp, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
    ← groupCohomology.map_comp]

  refine congrArg (fun T => (ModuleCat.Hom.hom T) x) (map_congr (by ext t; rfl) _ _ (fun z => ?_) 2)
  obtain ⟨y, rfl⟩ : ∃ y, Additive.ofMul y = z := ⟨Additive.toMul z, rfl⟩
  show (kappa E F H prG hprG Θ hΘ w).hom (Additive.ofMul y) = (xi E F H Θ hΘ w).hom ((prG w).hom (Additive.ofMul y))
  rw [kappa_hom_apply, xi_hom_apply, hprG]

end M4aHerbrand.SylowReadH

namespace M4aHerbrand
p2m_export "M4aHerbrand" "finPart repHomOfMulEquivariant repHomOfMulEquivariant_hom_apply IdeleGaloisDescent exists_map_prG_eq_zsmul_of_map_prG_eq_zsmul_of_under_eq"
namespace SylowReadH
p2m_open "M4aHerbrand"

theorem exists_isBase (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [MulSemiringAction G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) :
    ∃ (K : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] K), ExtCitation.LocalLevel.IsBase q L G K := by
  haveI : SMulCommClass G ℚ_[q] L := ⟨fun g c x => by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hG]⟩
  refine ⟨IntermediateField.lift (FixedPoints.intermediateField G : IntermediateField ℚ_[q] L), ?_, ?_⟩
  · exact FiniteDimensional.of_injective
      (IntermediateField.inclusion (IntermediateField.lift_le (FixedPoints.intermediateField G : IntermediateField ℚ_[q] L))).toLinearMap
      (fun a b h => (IntermediateField.inclusion
        (IntermediateField.lift_le (FixedPoints.intermediateField G : IntermediateField ℚ_[q] L))).toRingHom.injective h)
  · refine ⟨IntermediateField.lift_le _, fun x => ?_⟩
    rw [IntermediateField.mem_lift]
    exact Iff.rfl

theorem isBase_of_mulEquiv (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q))
    (G K : Type) [Group G] [Group K] [MulSemiringAction K L] [MulSemiringAction G L]
    (e : G ≃* K) (hGe : ∀ (g : G) (x : L), g • x = e g • x)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) (h : ExtCitation.LocalLevel.IsBase q L K K₀) :
    ExtCitation.LocalLevel.IsBase q L G K₀ := by
  refine ⟨h.le, fun x => ?_⟩
  rw [h.mem_iff]
  constructor
  · intro hx g
    rw [hGe]
    exact hx (e g)
  · intro hx k
    have := hx (e.symm k)
    rwa [hGe, MulEquiv.apply_symm_apply] at this

end M4aHerbrand.SylowReadH

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.IsBase LocalLevel.IsLocalFundamentalClass LocalLevel.isLocalFundamentalClass_map_subtype LocalLevel.isSolvable_of_faithfulSMul_of_padic"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "IsBase IsUnramOverlayerDatum IsLocalFundamentalClass isLocalFundamentalClass_map_subtype isSolvable_of_faithfulSMul_of_padic"
namespace Pullback
p2m_open "ExtCitation.LocalLevel ExtCitation"

variable (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q))
    (G H : Type) [Group G] [Group H] [MulSemiringAction H L] [MulDistribMulAction H (↥L)ˣ]
    [MulSemiringAction G L] [MulDistribMulAction G (↥L)ˣ]
    (e : G ≃* H) (hGe : ∀ (g : G) (x : L), g • x = e g • x) (hGeu : ∀ (g : G) (v : (↥L)ˣ), g • v = e g • v)
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction H (↥L)ˣ)) (hu : IsLocalFundamentalClass q L H K u)
    (φ : Rep.res e.toMonoidHom (Rep.ofMulDistribMulAction H (↥L)ˣ) ⟶ Rep.ofMulDistribMulAction G (↥L)ˣ)
    (hφ : ∀ m, φ.hom m = m)

include hGe hGeu hu hφ in
theorem isLocalFundamentalClass_map :
    IsLocalFundamentalClass q L G K ((groupCohomology.map e.toMonoidHom φ 2).hom u) := by
  intro M _ hLM H' _ _ _ _ _ NL Nn _ _ e' φF π d ι hι hfin hc

  let e'' : H ≃* H' ⧸ NL :=
    { toFun := fun h => e' (e.symm h)
      invFun := fun z => e (e'.symm z)
      left_inv := fun h => by simp
      right_inv := fun z => by simp
      map_mul' := fun a b => by simp [map_mul] }

  have d'' : IsUnramOverlayerDatum q L H K M hLM H' NL Nn e'' φF π :=
    { smul_algebraMap := d.smul_algebraMap
      coe_smul_units := d.coe_smul_units
      mem_base_iff := d.mem_base_iff
      mem_layer_iff := d.mem_layer_iff
      coe_smul_eq := fun h₀ h hh x => by
        have hh' : (QuotientGroup.mk h : H' ⧸ NL) = e' (e.symm h₀) := hh
        have := d.coe_smul_eq (e.symm h₀) h hh' x
        rw [hGe, MulEquiv.apply_symm_apply] at this
        exact this
      card_quotient := d.card_quotient.trans (Nat.card_congr e.toEquiv)
      mem_zpowers := d.mem_zpowers
      frobenius := d.frobenius
      smul_pi := d.smul_pi
      pi_mem := d.pi_mem
      norm_pi_lt := d.norm_pi_lt
      norm_le_norm_pi := d.norm_le_norm_pi }

  let ι'' : Rep.res (e''.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) (Rep.ofMulDistribMulAction H (↥L)ˣ) ⟶
      Rep.ofMulDistribMulAction H' (↥M)ˣ :=
    (Rep.resFunctor (e'.symm.toMonoidHom.comp (QuotientGroup.mk' NL))).map φ ≫ ι
  have hι'' : ∀ v : (↥L)ˣ, (((Additive.toMul (ι''.hom (Additive.ofMul v)) : (↥M)ˣ) : M) : PadicAlgCl q) = ((v : L) : PadicAlgCl q) := by
    intro v
    show (((Additive.toMul (ι.hom (φ.hom (Additive.ofMul v))) : (↥M)ˣ) : M) : PadicAlgCl q) = _
    rw [hφ]
    exact hι v
  have key := hu M hLM H' NL Nn e'' φF π d'' ι'' hι'' hfin hc

  have hcomp := groupCohomology.map_comp (A := Rep.ofMulDistribMulAction H (↥L)ˣ) e.toMonoidHom
    (e'.symm.toMonoidHom.comp (QuotientGroup.mk' NL)) φ ι 2
  have happ := congrArg (fun T => (ModuleCat.Hom.hom T) u) hcomp
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at happ
  rw [← happ]
  exact key

end ExtCitation.LocalLevel.Pullback

open M4aHerbrand.SylowReadH in
theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (H : Subgroup (F ≃ₐ[E] F))
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (prG : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    (D' : IdeleGaloisDescent (𝓞 F) ↥(IntermediateField.fixedField H) F)
    [MulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField H)] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI' : ∀ (g : (F ≃ₐ[↥(IntermediateField.fixedField H)] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D'.unitsAct g x)
    (prG' : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField H)] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F w)) (w.adicCompletion F)ˣ)
    (hprG' : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG' w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    (Θ : ↥H ≃* (F ≃ₐ[↥(IntermediateField.fixedField H)] F))
    (hΘ : ∀ (s : ↥H) (y : F), Θ s y = (s : F ≃ₐ[E] F) y)
    (ψ : Rep.res Θ.toMonoidHom (Rep.ofMulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField H)] F) (AdeleRing (𝓞 F) F)ˣ) ⟶ Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ))
    (hψ : ∀ y, ψ.hom y = y)
    (x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2)
    (x' : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField H)] F) (AdeleRing (𝓞 F) F)ˣ) 2)
    (hx' : (groupCohomology.map Θ.toMonoidHom ψ 2).hom x' =
      (groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ))) 2).hom x)

    (q : HeightOneSpectrum (𝓞 E) → ℕ) (_ : ∀ v, Fact (q v).Prime)
    (L : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
    (_ : ∀ v, FiniteDimensional ℚ_[q v] (L v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (L v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L v))ˣ)
    (Φ : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E F v).adicCompletion F ≃+* L v)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] (L v) y = algebraMap ℚ_[q v] (L v) y)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (↥(L v))ˣ), ((g • y : (↥(L v))ˣ) : L v) = g • (y : L v))
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (NumberField.PlaceAbove.above E F v).adicCompletion F), (Φ v) (g • y) = g • (Φ v) y)
    (K₀ : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
    (_ : ∀ v, FiniteDimensional ℚ_[q v] (K₀ v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsBase (q v) (L v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v))
    (θ : ∀ v : HeightOneSpectrum (𝓞 E), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L v))ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (↥(L v))ˣ),
      ((Additive.toMul ((θ v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above E F v).adicCompletion F) =
        (Φ v).symm (y : L v))
    (u : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L v))ˣ))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v) (u v))
    (n : HeightOneSpectrum (𝓞 E) → ℤ)
    (hn : ∀ v : HeightOneSpectrum (𝓞 E),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG (NumberField.PlaceAbove.above E F v)) 2).hom x =
        n v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u v))

    (q' : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) → ℕ) (_ : ∀ v, Fact (q' v).Prime)
    (L' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), IntermediateField ℚ_[q' v] (PadicAlgCl (q' v)))
    (_ : ∀ v, FiniteDimensional ℚ_[q' v] (L' v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (L' v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (↥(L' v))ˣ)
    (Φ' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F ≃+* L' v)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (g : ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (y : ℚ_[q' v]), g • algebraMap ℚ_[q' v] (L' v) y = algebraMap ℚ_[q' v] (L' v) y)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (g : ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (y : (↥(L' v))ˣ), ((g • y : (↥(L' v))ˣ) : L' v) = g • (y : L' v))
    (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (g : ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (y : (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F), (Φ' v) (g • y) = g • (Φ' v) y)
    (K₀' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), IntermediateField ℚ_[q' v] (PadicAlgCl (q' v)))
    (_ : ∀ v, FiniteDimensional ℚ_[q' v] (K₀' v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), ExtCitation.LocalLevel.IsBase (q' v) (L' v) (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (K₀' v))
    (θ' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (↥(L' v))ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F)ˣ)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (y : (↥(L' v))ˣ),
      ((Additive.toMul ((θ' v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F) =
        (Φ' v).symm (y : L' v))
    (u' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (↥(L' v))ˣ))
    (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), ExtCitation.LocalLevel.IsLocalFundamentalClass (q' v) (L' v) (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (K₀' v) (u' v)) :
    ∀ v' : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')).subtype (prG' (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) 2).hom x' =
        n (v'.under (𝓞 E)) • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))) (θ' v') 2).hom (u' v') := by
  rename_i hq_ hfdL hactL hactUL hΦ1 hΦ2 hΦ3 hfdK hbase hθ hu hq'_ hfdL' hactL' hactUL' hΦ1' hΦ2' hΦ3' hfdK' hbase' hθ' hu'
  intro v'
  classical
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  haveI : Finite (F ≃ₐ[E] F) := inferInstance

  set v : HeightOneSpectrum (𝓞 E) := v'.under (𝓞 E) with hv
  have hwv : (NumberField.PlaceAbove.above E F v).under (𝓞 E) = v := HeightOneSpectrum.ext (NumberField.PlaceAbove.comap_above E F v)
  have hw'v' : (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v').under (𝓞 ↥(IntermediateField.fixedField H)) = v' := HeightOneSpectrum.ext (NumberField.PlaceAbove.comap_above ↥(IntermediateField.fixedField H) F v')
  have hw'v : (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v').under (𝓞 E) = v := by
    apply HeightOneSpectrum.ext
    rw [HeightOneSpectrum.under_asIdeal, ← Ideal.under_under (B := 𝓞 ↥(IntermediateField.fixedField H)), ← HeightOneSpectrum.under_asIdeal,
      ← HeightOneSpectrum.under_asIdeal, hw'v']

  haveI := hq_ v; haveI := hfdL v; letI := hactL v; letI := hactUL v; haveI := hfdK v
  haveI := hq'_ v'; haveI := hfdL' v'; letI := hactL' v'; letI := hactUL' v'; haveI := hfdK' v'

  obtain ⟨-, act₁, actU₁, Φ₁, θ₁, u₁, h1₁, h2₁, h3₁, base₁, hθ₁, hu₁, hcoord₁⟩ :=
    M4aHerbrand.exists_map_prG_eq_zsmul_of_map_prG_eq_zsmul_of_under_eq E F D hactI prG hprG x
      (NumberField.PlaceAbove.above E F v) (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v') (hw'v.trans hwv.symm)
      (q v) (L v) (Φ v) (hΦ1 v) (hΦ2 v) (hΦ3 v) (K₀ v) (hbase v) (θ v) (hθ v) (u v) (hu v) (n v) (hn v)
  letI := act₁
  letI := actU₁

  haveI : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v').adicCompletion F) := NumberField.PlaceDecomp.faithfulSMul_decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')
  haveI hfaith₁ : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) ↥(L v) := ⟨fun {g₁ g₂} h =>
    FaithfulSMul.eq_of_smul_eq_smul (α := (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v').adicCompletion F) fun y => Φ₁.injective (by rw [h3₁ g₁ y, h3₁ g₂ y]; exact h _)⟩
  have hsolv₁ : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) := ExtCitation.LocalLevel.isSolvable_of_faithfulSMul_of_padic (q v) (L v) ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) h1₁
  obtain ⟨KS, fdKS, baseS⟩ := exists_isBase (q v) (L v) ↥(H.subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))) (fun s y => h1₁ (s : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))) y)
  haveI := fdKS
  have hres := ExtCitation.LocalLevel.isLocalFundamentalClass_map_subtype (q v) (L v) ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) h1₁ h2₁ hsolv₁ (K₀ v) base₁ u₁ hu₁ (H.subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))) KS baseS

  let e := decompEquiv E F H Θ hΘ (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')
  letI actG₂ : MulSemiringAction ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) ↥(L v) := MulSemiringAction.compHom ↥(L v) ((H.subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))).subtype.comp e.toMonoidHom)
  letI actUG₂ : MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) (↥(L v))ˣ := MulDistribMulAction.compHom (↥(L v))ˣ ((H.subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))).subtype.comp e.toMonoidHom)
  have hGe : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))) (y : ↥(L v)), g • y = e g • y := fun g y => rfl
  have hGeu : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))) (y : (↥(L v))ˣ), g • y = e g • y := fun g y => rfl
  let φpull : Rep.res e.toMonoidHom (Rep.ofMulDistribMulAction ↥(H.subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))) (↥(L v))ˣ) ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) (↥(L v))ˣ :=
    Rep.ofHom
      { toLinearMap := (AddMonoidHom.id (Additive (↥(L v))ˣ)).toIntLinearMap
        isIntertwining' := fun t => by
          apply LinearMap.ext
          intro z
          rfl }
  have hφpull : ∀ m, φpull.hom m = m := fun m => rfl
  have hpull := ExtCitation.LocalLevel.Pullback.isLocalFundamentalClass_map (q v) (L v) ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) ↥(H.subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))) e hGe hGeu KS _ hres φpull hφpull

  haveI hfaith₂ : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) ↥(L v) := ⟨fun {g₁ g₂} h => by
    apply e.injective
    apply Subtype.ext
    exact FaithfulSMul.eq_of_smul_eq_smul (M := ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))) (α := ↥(L v)) fun y => by
      have := h y
      rw [hGe, hGe] at this
      exact this⟩
  have h1₂ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] ↥(L v) y = algebraMap ℚ_[q v] ↥(L v) y := fun g y => h1₁ _ y
  have h2₂ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))) (y : (↥(L v))ˣ), ((g • y : (↥(L v))ˣ) : ↥(L v)) = g • (y : ↥(L v)) := fun g y => h2₁ _ y
  have h3₂ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))) (y : (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v').adicCompletion F), Φ₁ (g • y) = g • Φ₁ y := fun g y => by
    rw [smul_adicCompletion_eq E F H Θ hΘ (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v') g y, h3₁]
    rfl
  have base₂ : ExtCitation.LocalLevel.IsBase (q v) (L v) ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) KS := isBase_of_mulEquiv (q v) (L v) ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) ↥(H.subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))) e hGe KS baseS

  let ΦM : (↥(L v))ˣ →* ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v').adicCompletion F)ˣ := Units.map Φ₁.symm.toRingHom.toMonoidHom
  have hΦM : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))) (y : (↥(L v))ˣ), ΦM (g • y) = g • ΦM y := by
    intro g y
    apply Units.ext
    show Φ₁.symm ((g • y : (↥(L v))ˣ) : ↥(L v)) = ((g • ΦM y : ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v').adicCompletion F)ˣ) : (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v').adicCompletion F)
    rw [h2₂ g y, NumberField.PlaceDecomp.coe_smul_units]
    apply Φ₁.injective
    rw [h3₂ g, RingEquiv.apply_symm_apply]
    congr 1
    show (y : ↥(L v)) = Φ₁ (Φ₁.symm (y : ↥(L v)))
    exact (Φ₁.apply_symm_apply _).symm
  let θ₂ := M4aHerbrand.repHomOfMulEquivariant ΦM hΦM
  have hθ₂ : ∀ y : (↥(L v))ˣ, ((Additive.toMul (θ₂.hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v').adicCompletion F)ˣ) : (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v').adicCompletion F) = Φ₁.symm (y : ↥(L v)) :=
    fun y => rfl
  obtain ⟨-, hq₁w⟩ := NumberField.PlaceDecomp.mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v') (q v) (L v) Φ₁
  obtain ⟨-, hq'w⟩ := NumberField.PlaceDecomp.mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v') (q' v') (L' v') (Φ' v')
  haveI : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v').adicCompletion F) := NumberField.PlaceDecomp.faithfulSMul_decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')
  haveI hfaith' : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) ↥(L' v') := ⟨fun {g₁ g₂} h =>
    FaithfulSMul.eq_of_smul_eq_smul (α := (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v').adicCompletion F) fun y => (Φ' v').injective (by rw [hΦ3' v' g₁ y, hΦ3' v' g₂ y]; exact h _)⟩
  have h92 := NumberField.PlaceDecomp.map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')
    (q v) hq₁w (L v) Φ₁ h1₂ h2₂ h3₂ KS base₂ θ₂ hθ₂ _ hpull
    (q' v') hq'w (L' v') (Φ' v') (hΦ1' v') (hΦ2' v') (hΦ3' v') (K₀' v') (hbase' v') (θ' v') (hθ' v') (u' v') (hu' v')

  have hA := groupCohomology.map_comp (A := (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) (↥(L v))ˣ)) (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))) (H.subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))).subtype θ₁
    (𝟙 (Rep.res (H.subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))).subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v').adicCompletion F)ˣ))) 2
  have hB := groupCohomology.map_comp (A := (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) (↥(L v))ˣ)) ((MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))).comp (H.subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))).subtype) e.toMonoidHom
    ((Rep.resFunctor (H.subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))).subtype).map θ₁ ≫ 𝟙 (Rep.res (H.subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))).subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v').adicCompletion F)ˣ))) (xi E F H Θ hΘ (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) 2
  have hC := groupCohomology.map_comp (A := (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) (↥(L v))ˣ)) (H.subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))).subtype e.toMonoidHom
    (𝟙 (Rep.res (H.subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))).subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) (↥(L v))ˣ))) φpull 2
  have hD := groupCohomology.map_comp (A := (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) (↥(L v))ˣ)) ((H.subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))).subtype.comp e.toMonoidHom) (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')))
    ((Rep.resFunctor e.toMonoidHom).map (𝟙 (Rep.res (H.subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))).subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) (↥(L v))ˣ))) ≫ φpull) θ₂ 2
  have hE : groupCohomology.map (((MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))).comp (H.subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))).subtype).comp e.toMonoidHom)
      ((Rep.resFunctor e.toMonoidHom).map ((Rep.resFunctor (H.subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))).subtype).map θ₁ ≫ 𝟙 (Rep.res (H.subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))).subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v').adicCompletion F)ˣ))) ≫ xi E F H Θ hΘ (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) 2 =
      groupCohomology.map (((H.subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))).subtype.comp e.toMonoidHom).comp (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))))
      ((Rep.resFunctor (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')))).map ((Rep.resFunctor e.toMonoidHom).map (𝟙 (Rep.res (H.subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))).subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) (↥(L v))ˣ))) ≫ φpull) ≫ θ₂) 2 := by
    refine map_congr (by ext t; rfl) _ _ (fun z => ?_) 2
    obtain ⟨y, rfl⟩ : ∃ y, Additive.ofMul y = z := ⟨Additive.toMul z, rfl⟩
    show (xi E F H Θ hΘ (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')).hom (θ₁.hom (Additive.ofMul y)) = θ₂.hom (φpull.hom (Additive.ofMul y))
    rw [xi_hom_apply, hφpull, M4aHerbrand.repHomOfMulEquivariant_hom_apply]
    have hval : Additive.toMul (θ₁.hom (Additive.ofMul y)) = ΦM y := Units.ext (hθ₁ y)
    exact ((Additive.ofMul).apply_symm_apply _).symm.trans (congrArg Additive.ofMul hval)
  have hmaps : groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))) θ₁ 2 ≫ groupCohomology.map (H.subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))).subtype (𝟙 (Rep.res (H.subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))).subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v').adicCompletion F)ˣ))) 2 ≫
        groupCohomology.map e.toMonoidHom (xi E F H Θ hΘ (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) 2 =
      groupCohomology.map (H.subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))).subtype (𝟙 (Rep.res (H.subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))).subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) (↥(L v))ˣ))) 2 ≫ groupCohomology.map e.toMonoidHom φpull 2 ≫
        groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField H) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))) θ₂ 2 := by
    rw [← Category.assoc, ← hA, ← hB, hE, hD, hC, Category.assoc]
    rfl
  have happ := congrArg (fun T => (ModuleCat.Hom.hom T) u₁) hmaps
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at happ
  rw [coord_fixedField_eq E F H prG hprG prG' hprG' Θ hΘ ψ hψ (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v') x x' hx', hcoord₁, ← h92, map_zsmul, map_zsmul, happ]
  rfl

end S_M4aHerbrand_map_prG_eq_smul_fixedField_of_map_prG_eq_smul
end P2MW
export P2MW.S_M4aHerbrand_map_prG_eq_smul_fixedField_of_map_prG_eq_smul (solution)
