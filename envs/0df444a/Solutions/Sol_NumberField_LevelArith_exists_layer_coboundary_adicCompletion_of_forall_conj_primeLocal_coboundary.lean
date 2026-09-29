-- Prove2me | solution 1 for NumberField.LevelArith.exists_layer_coboundary_adicCompletion_of_forall_conj_primeLocal_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/3902ef1f-b02f-559d-be9d-c316d17af1d1

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Definitions.Def_GaloisRep_CompletionBridge
import Theorems.Thm_NumberField_existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one
import Theorems.Thm_ValuationSubring_decompositionSubgroup_padicPlace_le_closure_range_localGaloisToGlobal
import Theorems.Thm_ValuationSubring_map_restrictNormalHom_decompositionSubgroup_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_layer_coboundary_adicCompletion_of_forall_conj_primeLocal_coboundary

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits groupCohomology ExtCitation NumberField.LevelArith"
open scoped Classical NumberField.LevelArith TensorProduct Pointwise

section

open IsDedekindDomain NumberField NumberField.LevelArith ExtCitation

namespace HasseLevelFurniture

private theorem levelField_le (E F L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hEF : E ≤ F) (hEL : E ≤ L) (hFL : F ≤ L) :
    levelField E F hEF ≤ levelField E L hEL :=
  (IntermediateField.extendScalars_le_extendScalars_iff hEF hEL).2 hFL

private noncomputable abbrev levelAlgebra (E F L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hEF : E ≤ F) (hEL : E ≤ L) (hFL : F ≤ L) :
    Algebra ↥(levelField E F hEF) ↥(levelField E L hEL) :=
  (IntermediateField.inclusion (levelField_le E F L hEF hEL hFL)).toRingHom.toAlgebra

private theorem levelAlgebra_isScalarTower (E F L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hEF : E ≤ F) (hEL : E ≤ L) (hFL : F ≤ L) :
    letI := levelAlgebra E F L hEF hEL hFL
    IsScalarTower ↥E ↥(levelField E F hEF) ↥(levelField E L hEL) :=
  letI := levelAlgebra E F L hEF hEL hFL
  IsScalarTower.of_algebraMap_eq fun x =>
    ((IntermediateField.inclusion (levelField_le E F L hEF hEL hFL)).commutes x).symm

private theorem coe_levelAlgebraMap (E F L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hEF : E ≤ F) (hEL : E ≤ L) (hFL : F ≤ L) (x : ↥(levelField E F hEF)) :
    letI := levelAlgebra E F L hEF hEL hFL
    ((algebraMap ↥(levelField E F hEF) ↥(levelField E L hEL) x : ↥(levelField E L hEL)) : AlgebraicClosure ℚ) =
      (x : AlgebraicClosure ℚ) :=
  rfl

private theorem isGalois_levelField (E L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hEL : E ≤ L)
    [FiniteDimensional ℚ ↥L] [Normal ℚ ↥L] : IsGalois ↥E ↥(levelField E L hEL) := by
  haveI : IsGalois ℚ ↥L := ⟨⟩
  haveI : IsGalois ℚ ↥(levelField E L hEL) :=
    IsGalois.of_algEquiv
      (AlgEquiv.ofRingEquiv (f := levelFieldEquiv E L hEL) fun q =>
        (levelFieldEquiv E L hEL).toRingHom.map_rat_algebraMap q)
  haveI : IsScalarTower ℚ ↥E ↥(levelField E L hEL) := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  exact IsGalois.tower_top_of_isGalois ℚ ↥E ↥(levelField E L hEL)

private theorem coe_restrictNormalHom_apply (E F L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hEF : E ≤ F) (hEL : E ≤ L) (hFL : F ≤ L) [Normal ↥E ↥(levelField E F hEF)]
    (σ : ↥(levelField E L hEL) ≃ₐ[↥E] ↥(levelField E L hEL)) (x : ↥(levelField E F hEF)) :
    letI := levelAlgebra E F L hEF hEL hFL
    haveI := levelAlgebra_isScalarTower E F L hEF hEL hFL
    ((AlgEquiv.restrictNormalHom ↥(levelField E F hEF) σ x : ↥(levelField E F hEF)) : AlgebraicClosure ℚ) =
      ((σ (algebraMap ↥(levelField E F hEF) ↥(levelField E L hEL) x) : ↥(levelField E L hEL)) :
        AlgebraicClosure ℚ) := by
  letI := levelAlgebra E F L hEF hEL hFL
  haveI := levelAlgebra_isScalarTower E F L hEF hEL hFL
  exact congrArg Subtype.val (AlgEquiv.restrictNormal_commutes σ ↥(levelField E F hEF) x)

private theorem mem_decomp_iff_restrictScalars_mem (E K : Type) [Field E] [Field K] [NumberField K] [Algebra E K]
    [Algebra ℚ E] [Algebra ℚ K] [IsScalarTower ℚ E K] (w : HeightOneSpectrum (𝓞 K)) (σ : K ≃ₐ[E] K) :
    σ ∈ PlaceDecomp.decomp E K w ↔ σ.restrictScalars ℚ ∈ PlaceDecomp.decomp ℚ K w :=
  Iff.rfl

private theorem restrictScalars_levelGal (E L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hEL : E ≤ L)
    [Normal ↥E ↥(levelField E L hEL)] [Algebra ℚ ↥(levelField E L hEL)]
    [@IsScalarTower ℚ ↥E ↥(levelField E L hEL)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    [@IsScalarTower ℚ ↥(levelField E L hEL) (AlgebraicClosure ℚ)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    [Normal ℚ ↥(levelField E L hEL)]
    (γ : ↥E.fixingSubgroup) :
    (levelGal E L hEL γ).restrictScalars ℚ =
      AlgEquiv.restrictNormalHom ↥(levelField E L hEL)
        (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := by
  ext x
  exact (levelGal_apply_coe E L hEL γ x).trans
    (AlgEquiv.restrictNormal_commutes (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      ↥(levelField E L hEL) x).symm

private theorem normal_rat_levelField (E L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hEL : E ≤ L)
    [Algebra ℚ ↥(levelField E L hEL)] [Normal ℚ ↥L] : Normal ℚ ↥(levelField E L hEL) :=
  Normal.of_algEquiv
    (AlgEquiv.ofRingEquiv (f := levelFieldEquiv E L hEL) fun q =>
      (levelFieldEquiv E L hEL).toRingHom.map_rat_algebraMap q)

private theorem isScalarTower_rat_levelField_algClosure (E L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hEL : E ≤ L)
    [Algebra ℚ ↥(levelField E L hEL)] :
    @IsScalarTower ℚ ↥(levelField E L hEL) (AlgebraicClosure ℚ)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

private theorem isScalarTower_rat_base_levelField (E L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hEL : E ≤ L)
    [Algebra ℚ ↥(levelField E L hEL)] :
    @IsScalarTower ℚ ↥E ↥(levelField E L hEL) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

private theorem levelAlgebra_isScalarTower_algClosure (E F L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hEF : E ≤ F) (hEL : E ≤ L) (hFL : F ≤ L) :
    letI := levelAlgebra E F L hEF hEL hFL
    IsScalarTower ↥(levelField E F hEF) ↥(levelField E L hEL) (AlgebraicClosure ℚ) :=
  letI := levelAlgebra E F L hEF hEL hFL
  IsScalarTower.of_algebraMap_eq fun x => (coe_levelAlgebraMap E F L hEF hEL hFL x).symm

private theorem restrictNormalHom_levelGal (E F L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hEF : E ≤ F)
    (hEL : E ≤ L) (hFL : F ≤ L) [Normal ↥E ↥(levelField E F hEF)] [Normal ↥E ↥(levelField E L hEL)]
    (γ : ↥E.fixingSubgroup) :
    letI := levelAlgebra E F L hEF hEL hFL
    haveI := levelAlgebra_isScalarTower E F L hEF hEL hFL
    AlgEquiv.restrictNormalHom ↥(levelField E F hEF) (levelGal E L hEL γ) = levelGal E F hEF γ := by
  letI := levelAlgebra E F L hEF hEL hFL
  haveI := levelAlgebra_isScalarTower E F L hEF hEL hFL
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  rw [coe_restrictNormalHom_apply E F L hEF hEL hFL (levelGal E L hEL γ) x, levelGal_apply_coe, levelGal_apply_coe]
  rfl

private noncomputable abbrev lamE (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (q : Nat.Primes)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ↥(E.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))) →* ↥E.fixingSubgroup :=
  ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q)).subgroupComap E.fixingSubgroup

private noncomputable def resHom (E Kbig : IntermediateField ℚ (AlgebraicClosure ℚ)) (hEK : E ≤ Kbig)
    [FiniteDimensional ℚ ↥Kbig]
    [Normal ↥E ↥(levelField E Kbig hEK)] [Algebra ℚ ↥(levelField E Kbig hEK)]
    [@IsScalarTower ℚ ↥(levelField E Kbig hEK) (AlgebraicClosure ℚ)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    [Normal ℚ ↥(levelField E Kbig hEK)]
    (q : Nat.Primes) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (w : HeightOneSpectrum (𝓞 ↥(levelField E Kbig hEK)))
    (hrange : ((AlgEquiv.restrictNormalHom ↥(levelField E Kbig hEK)).comp
        ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))).range =
      PlaceDecomp.decomp ℚ ↥(levelField E Kbig hEK) w) :
    ↥(E.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))) →*
      ↥(PlaceDecomp.decomp ↥E ↥(levelField E Kbig hEK) w) :=
  ((levelGal E Kbig hEK).comp (lamE E q σ)).codRestrict (PlaceDecomp.decomp ↥E ↥(levelField E Kbig hEK) w)
    fun d => by
    haveI := isScalarTower_rat_base_levelField E Kbig hEK
    rw [mem_decomp_iff_restrictScalars_mem ↥E ↥(levelField E Kbig hEK) w, MonoidHom.comp_apply,
      restrictScalars_levelGal E Kbig hEK, ← hrange]
    exact MonoidHom.mem_range.2 ⟨(d : primeLocalGaloisGroup q), rfl⟩

private theorem coe_resHom (E Kbig : IntermediateField ℚ (AlgebraicClosure ℚ)) (hEK : E ≤ Kbig)
    [FiniteDimensional ℚ ↥Kbig]
    [Normal ↥E ↥(levelField E Kbig hEK)] [Algebra ℚ ↥(levelField E Kbig hEK)]
    [@IsScalarTower ℚ ↥(levelField E Kbig hEK) (AlgebraicClosure ℚ)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    [Normal ℚ ↥(levelField E Kbig hEK)]
    (q : Nat.Primes) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (w : HeightOneSpectrum (𝓞 ↥(levelField E Kbig hEK)))
    (hrange : ((AlgEquiv.restrictNormalHom ↥(levelField E Kbig hEK)).comp
        ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))).range =
      PlaceDecomp.decomp ℚ ↥(levelField E Kbig hEK) w)
    (d : ↥(E.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q)))) :
    ((resHom E Kbig hEK q σ w hrange d : ↥(PlaceDecomp.decomp ↥E ↥(levelField E Kbig hEK) w)) :
        ↥(levelField E Kbig hEK) ≃ₐ[↥E] ↥(levelField E Kbig hEK)) =
      levelGal E Kbig hEK (lamE E q σ d) :=
  rfl

private theorem resHom_surjective (E Kbig : IntermediateField ℚ (AlgebraicClosure ℚ)) (hEK : E ≤ Kbig)
    [FiniteDimensional ℚ ↥Kbig]
    [Normal ↥E ↥(levelField E Kbig hEK)] [Algebra ℚ ↥(levelField E Kbig hEK)]
    [@IsScalarTower ℚ ↥(levelField E Kbig hEK) (AlgebraicClosure ℚ)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    [Normal ℚ ↥(levelField E Kbig hEK)]
    (q : Nat.Primes) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (w : HeightOneSpectrum (𝓞 ↥(levelField E Kbig hEK)))
    (hrange : ((AlgEquiv.restrictNormalHom ↥(levelField E Kbig hEK)).comp
        ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))).range =
      PlaceDecomp.decomp ℚ ↥(levelField E Kbig hEK) w)
    (hmap : (E.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))).map
          ((AlgEquiv.restrictNormalHom ↥(levelField E Kbig hEK)).comp
            ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))) =
        PlaceDecomp.decomp ℚ ↥(levelField E Kbig hEK) w ⊓
          (E.comap (IsScalarTower.toAlgHom ℚ ↥(levelField E Kbig hEK) (AlgebraicClosure ℚ))).fixingSubgroup) :
    Function.Surjective (resHom E Kbig hEK q σ w hrange) := by
  haveI := isScalarTower_rat_base_levelField E Kbig hEK
  rintro ⟨τ, hτ⟩
  have hτ' : τ.restrictScalars ℚ ∈
      (E.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))).map
        ((AlgEquiv.restrictNormalHom ↥(levelField E Kbig hEK)).comp
          ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))) := by
    rw [hmap]
    refine Subgroup.mem_inf.2 ⟨(mem_decomp_iff_restrictScalars_mem ↥E ↥(levelField E Kbig hEK) w τ).1 hτ, ?_⟩
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_
    have hxE : IsScalarTower.toAlgHom ℚ ↥(levelField E Kbig hEK) (AlgebraicClosure ℚ) x ∈ E := hx
    rw [IsScalarTower.toAlgHom_apply] at hxE
    have hxe : x = algebraMap ↥E ↥(levelField E Kbig hEK) ⟨_, hxE⟩ := Subtype.ext rfl
    show τ x = x
    rw [hxe]
    exact τ.commutes _
  obtain ⟨d, hd, hdτ⟩ := Subgroup.mem_map.1 hτ'
  refine ⟨⟨d, hd⟩, Subtype.ext ?_⟩
  rw [coe_resHom]
  refine AlgEquiv.restrictScalars_injective (R := ℚ) ?_
  rw [restrictScalars_levelGal E Kbig hEK]
  exact hdτ

private theorem mem_fixingSubgroup_of_resHom_eq_one (E Kbig : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hEK : E ≤ Kbig) [FiniteDimensional ℚ ↥Kbig]
    [Normal ↥E ↥(levelField E Kbig hEK)] [Algebra ℚ ↥(levelField E Kbig hEK)]
    [@IsScalarTower ℚ ↥(levelField E Kbig hEK) (AlgebraicClosure ℚ)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    [Normal ℚ ↥(levelField E Kbig hEK)]
    (q : Nat.Primes) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (w : HeightOneSpectrum (𝓞 ↥(levelField E Kbig hEK)))
    (hrange : ((AlgEquiv.restrictNormalHom ↥(levelField E Kbig hEK)).comp
        ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))).range =
      PlaceDecomp.decomp ℚ ↥(levelField E Kbig hEK) w)
    (d : ↥(E.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))))
    (hd : resHom E Kbig hEK q σ w hrange d = 1) :
    ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q)) (d : primeLocalGaloisGroup q) ∈
      Kbig.fixingSubgroup := by
  have h0 := congrArg Subtype.val hd
  have h1 : levelGal E Kbig hEK (lamE E q σ d) = 1 := h0
  refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => ?_
  have h2 := levelGal_apply_coe E Kbig hEK (lamE E q σ d) ⟨y, (IntermediateField.mem_extendScalars hEK).2 hy⟩
  rw [h1, AlgEquiv.one_apply] at h2
  exact h2.symm

end HasseLevelFurniture
end

section

open NumberField IsDedekindDomain
open scoped Pointwise

open MulAction

namespace DecompositionAssembly

variable {Γ : Type*} [Group Γ]

private theorem map_topologicalClosure_le [TopologicalSpace Γ] [IsTopologicalGroup Γ] {Δ : Type*} [Group Δ]
    (r : Γ →* Δ) (U : Subgroup Γ) (hU : IsOpen (U : Set Γ)) (hUr : U ≤ r.ker) (R : Subgroup Γ) :
    R.topologicalClosure.map r ≤ R.map r := by
  rintro _ ⟨g, hg, rfl⟩
  have hg' : g ∈ closure (R : Set Γ) := hg
  have hopen : IsOpen ((fun x : Γ => g⁻¹ * x) ⁻¹' (U : Set Γ)) := hU.preimage (continuous_const_mul g⁻¹)
  have hmem : g ∈ (fun x : Γ => g⁻¹ * x) ⁻¹' (U : Set Γ) := by
    simp [U.one_mem]
  obtain ⟨x, hxU, hxR⟩ := mem_closure_iff.1 hg' _ hopen hmem
  refine ⟨x, hxR, ?_⟩
  have hker : r (g⁻¹ * x) = 1 := MonoidHom.mem_ker.1 (hUr hxU)
  calc r x = r g * r (g⁻¹ * x) := by rw [map_mul, map_inv, mul_inv_cancel_left]
    _ = r g := by rw [hker, mul_one]

private theorem comp_conj {Δ : Type*} [Group Δ] (r : Γ →* Δ) (σ : Γ) :
    r.comp (MulAut.conj σ).toMonoidHom = (MulAut.conj (r σ)).toMonoidHom.comp r := by
  ext x
  simp

private theorem range_comp_conj_comp_eq [TopologicalSpace Γ] [IsTopologicalGroup Γ] {Δ G α : Type*} [Group Δ]
    [Group G] [MulAction Γ α] (r : Γ →* Δ) (U : Subgroup Γ) (hU : IsOpen (U : Set Γ)) (hUr : U ≤ r.ker) (ℓ : G →* Γ)
    (A : α)
    (hℓ : ℓ.range ≤ stabilizer Γ A) (hdense : stabilizer Γ A ≤ ℓ.range.topologicalClosure) (σ : Γ)
    (D : Subgroup Δ) (hD : (stabilizer Γ (σ • A)).map r = D) :
    (r.comp ((MulAut.conj σ).toMonoidHom.comp ℓ)).range = D := by
  subst hD
  rw [stabilizer_smul_eq_stabilizer_map_conj, Subgroup.map_map, comp_conj, ← Subgroup.map_map,
    MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.map_map, comp_conj, ← Subgroup.map_map]
  apply le_antisymm
  · exact Subgroup.map_mono (Subgroup.map_mono hℓ)
  · exact Subgroup.map_mono ((Subgroup.map_mono hdense).trans (map_topologicalClosure_le r U hU hUr _))

private theorem map_comap_eq_inf {Δ G : Type*} [Group Δ] [Group G] (r : Γ →* Δ) (g : G →* Γ) (D : Subgroup Δ)
    (hmain : (r.comp g).range = D) (Φ : Subgroup Γ) (Φ' : Subgroup Δ) (hΦ : ∀ γ, γ ∈ Φ ↔ r γ ∈ Φ') :
    (Φ.comap g).map (r.comp g) = D ⊓ Φ' := by
  ext δ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨?_, (hΦ (g τ)).1 (Subgroup.mem_comap.1 hτ)⟩
    rw [← hmain]
    exact ⟨τ, rfl⟩
  · rintro ⟨hδD, hδΦ'⟩
    have hδ : δ ∈ (r.comp g).range := by rw [hmain]; exact hδD
    obtain ⟨τ, rfl⟩ := MonoidHom.mem_range.1 hδ
    exact ⟨τ, Subgroup.mem_comap.2 ((hΦ (g τ)).2 hδΦ'), rfl⟩

end DecompositionAssembly

namespace PlaceConjugate

private theorem mem_asIdeal_iff_of_ne_zero {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {y : 𝓞 K} (hy : y ≠ 0) :
    y ∈ v.asIdeal ↔ v.valuation K (y : K) ≤ 1 ∧ ¬ v.valuation K ((y : K)⁻¹) ≤ 1 := by
  have hlt : v.valuation K (y : K) < 1 ↔ y ∈ v.asIdeal := v.valuation_lt_one_iff_mem y
  have h0 : 0 < v.valuation K (y : K) := by
    rw [zero_lt_iff, ne_eq, map_eq_zero]
    exact_mod_cast hy
  rw [← hlt, map_inv₀]
  constructor
  · intro h
    exact ⟨h.le, not_le.2 ((one_lt_inv₀ h0).2 h)⟩
  · rintro ⟨-, h2⟩
    exact (one_lt_inv₀ h0).1 (not_le.1 h2)

private theorem liesOver_span_of_mem {K : Type*} [Field K] [NumberField K] (P : Ideal (𝓞 K)) [P.IsPrime] {q : ℕ}
    (hq : q.Prime) (hqP : (q : 𝓞 K) ∈ P) : P.LiesOver (Ideal.span {(q : ℤ)}) := by
  have hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hq).irreducible
  have hle : Ideal.span {(q : ℤ)} ≤ P.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change algebraMap ℤ (𝓞 K) (q : ℤ) ∈ P
    rw [map_natCast]
    exact hqP
  have hne : P.under ℤ ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  have heq : Ideal.span {(q : ℤ)} = P.under ℤ := hmax.eq_of_le hne hle
  exact ⟨heq⟩

private theorem exists_smul_eq_of_liesOver (N : Type*) [Field N] [NumberField N] [IsGalois ℚ N]
    (p : Ideal ℤ) (P Q : Ideal (𝓞 N)) [P.IsPrime] [P.LiesOver p] [Q.IsPrime] [Q.LiesOver p] :
    ∃ σ : N ≃ₐ[ℚ] N, σ • P = Q :=
  Ideal.exists_smul_eq_of_isGaloisGroup p P Q (N ≃ₐ[ℚ] N)

private theorem under_eq_of_forall_mem_iff (A : ValuationSubring (AlgebraicClosure ℚ)) (K₁ K₂ : Type*) [Field K₁]
    [Field K₂] [NumberField K₁] [NumberField K₂] [Algebra K₁ (AlgebraicClosure ℚ)] [Algebra K₂ (AlgebraicClosure ℚ)]
    [Algebra K₁ K₂] [IsScalarTower K₁ K₂ (AlgebraicClosure ℚ)] (w₁ : HeightOneSpectrum (𝓞 K₁))
    (h₁ : ∀ x : K₁, algebraMap K₁ (AlgebraicClosure ℚ) x ∈ A ↔ w₁.valuation K₁ x ≤ 1)
    (w₂ : HeightOneSpectrum (𝓞 K₂))
    (h₂ : ∀ x : K₂, algebraMap K₂ (AlgebraicClosure ℚ) x ∈ A ↔ w₂.valuation K₂ x ≤ 1) :
    HeightOneSpectrum.under (𝓞 K₁) w₂ = w₁ := by
  apply HeightOneSpectrum.ext
  ext y
  change algebraMap (𝓞 K₁) (𝓞 K₂) y ∈ w₂.asIdeal ↔ y ∈ w₁.asIdeal
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hy₂ : algebraMap (𝓞 K₁) (𝓞 K₂) y ≠ 0 := by
    intro h0
    apply hy
    have h1 : algebraMap K₁ K₂ (y : K₁) = 0 := by
      change ((algebraMap (𝓞 K₁) (𝓞 K₂) y : 𝓞 K₂) : K₂) = 0
      rw [h0]
      rfl
    have hzero : (y : K₁) = 0 := (algebraMap K₁ K₂).injective (h1.trans (map_zero _).symm)
    exact RingOfIntegers.coe_eq_zero_iff.1 hzero
  have hcoe : algebraMap K₂ (AlgebraicClosure ℚ) ((algebraMap (𝓞 K₁) (𝓞 K₂) y : 𝓞 K₂) : K₂) =
      algebraMap K₁ (AlgebraicClosure ℚ) (y : K₁) := by
    change algebraMap K₂ (AlgebraicClosure ℚ) (algebraMap K₁ K₂ (y : K₁)) = _
    rw [← IsScalarTower.algebraMap_apply]
  rw [mem_asIdeal_iff_of_ne_zero w₂ hy₂, mem_asIdeal_iff_of_ne_zero w₁ hy, ← h₂, ← h₂, ← h₁, ← h₁, map_inv₀,
    map_inv₀, hcoe]

variable (q : ℕ) [Fact q.Prime]

private theorem inv_natCast_notMem_padicPlace : ((q : AlgebraicClosure ℚ))⁻¹ ∉ padicPlace q := by
  rw [mem_padicPlace_iff, map_inv₀, map_natCast, nnnorm_inv, ← PadicAlgCl.valuation_def,
    PadicAlgCl.valuation_p, one_div, inv_inv, not_le]
  exact_mod_cast (Fact.out : q.Prime).one_lt

private theorem algebraMap_inv_natCast_notMem_smul_padicPlace (L : Type*) [Field L] [Algebra L (AlgebraicClosure ℚ)]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    algebraMap L (AlgebraicClosure ℚ) (q : L)⁻¹ ∉ σ • padicPlace q := by
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, map_inv₀, map_natCast, map_inv₀,
    map_natCast]
  exact inv_natCast_notMem_padicPlace q

private theorem exists_forall_mem_iff_of_fixed (L : Type) [Field L] [NumberField L] [Algebra L (AlgebraicClosure ℚ)]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ v : HeightOneSpectrum (𝓞 L),
      ∀ x : L, algebraMap L (AlgebraicClosure ℚ) x ∈ σ • padicPlace q ↔ v.valuation L x ≤ 1 := by
  obtain ⟨v, hv, -⟩ := NumberField.existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one L
    (algebraMap L (AlgebraicClosure ℚ)) (σ • padicPlace q) ⟨_, algebraMap_inv_natCast_notMem_smul_padicPlace q L σ⟩
  exact ⟨v, hv⟩

private theorem exists_forall_mem_iff (K : Type) [Field K] [NumberField K] [Algebra K (AlgebraicClosure ℚ)]
    [IsScalarTower ℚ K (AlgebraicClosure ℚ)] [IsGalois ℚ K] (w : HeightOneSpectrum (𝓞 K))
    (hw : (q : 𝓞 K) ∈ w.asIdeal) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∀ x : K, algebraMap K (AlgebraicClosure ℚ) x ∈ σ • padicPlace q ↔ w.valuation K x ≤ 1 := by
  have hq : q.Prime := Fact.out

  obtain ⟨v, hv⟩ := exists_forall_mem_iff_of_fixed q K 1
  simp only [one_smul] at hv
  have hqinv : algebraMap K (AlgebraicClosure ℚ) (q : K)⁻¹ ∉ padicPlace q := by
    have h := algebraMap_inv_natCast_notMem_smul_padicPlace q K 1
    rwa [one_smul] at h
  have hqv : (q : 𝓞 K) ∈ v.asIdeal := by
    have hq0 : (q : 𝓞 K) ≠ 0 := by exact_mod_cast hq.ne_zero
    have hle : v.valuation K ((q : 𝓞 K) : K) ≤ 1 := v.valuation_le_one (q : 𝓞 K)
    have hcast : ((q : 𝓞 K) : K) = (q : K) := map_natCast (algebraMap (𝓞 K) K) q
    refine (mem_asIdeal_iff_of_ne_zero v hq0).2 ⟨hle, fun h => hqinv ?_⟩
    rw [hcast] at h
    exact (hv _).2 h

  haveI := liesOver_span_of_mem v.asIdeal hq hqv
  haveI := liesOver_span_of_mem w.asIdeal hq hw
  obtain ⟨τ, hτ⟩ := exists_smul_eq_of_liesOver K (Ideal.span {(q : ℤ)}) v.asIdeal w.asIdeal
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := K) (E := AlgebraicClosure ℚ) τ
  refine ⟨σ, ?_⟩
  have hres : AlgEquiv.restrictNormal σ⁻¹ K = τ⁻¹ := by
    rw [← hσ, ← map_inv]
    rfl
  have hσinv : ∀ x : K, σ⁻¹ (algebraMap K (AlgebraicClosure ℚ) x) = algebraMap K (AlgebraicClosure ℚ) (τ⁻¹ x) := by
    intro x
    rw [← hres]
    exact (AlgEquiv.restrictNormal_commutes σ⁻¹ K x).symm
  have hmem : ∀ x : K, algebraMap K (AlgebraicClosure ℚ) x ∈ σ • padicPlace q ↔ v.valuation K (τ⁻¹ x) ≤ 1 := by
    intro x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, hσinv, hv]

  obtain ⟨u, hu⟩ := exists_forall_mem_iff_of_fixed q K σ
  suffices huw : u = w by
    intro x
    rw [hu, huw]
  apply HeightOneSpectrum.ext
  ext y
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hy' : τ⁻¹ • y ≠ 0 := fun h => hy ((smul_eq_zero_iff_eq τ⁻¹).1 h)
  rw [← hτ, Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_asIdeal_iff_of_ne_zero u hy,
    mem_asIdeal_iff_of_ne_zero v hy', ← hu, ← hu, hmem, hmem]
  simp only [map_inv₀]
  rfl

end PlaceConjugate

namespace PlaceConjugate

open DecompositionAssembly

section Transport

variable (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] (K : Type*) [Field K] [Algebra F K] [Algebra K Ω]
  [IsScalarTower F K Ω]

private noncomputable def toImage : K ≃ₐ[F] (IsScalarTower.toAlgHom F K Ω).fieldRange :=
  AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F K Ω)

private theorem coe_toImage (x : K) : (toImage F Ω K x : Ω) = algebraMap K Ω x :=
  rfl

private noncomputable def autEquiv :
    ((IsScalarTower.toAlgHom F K Ω).fieldRange ≃ₐ[F] (IsScalarTower.toAlgHom F K Ω).fieldRange) ≃* (K ≃ₐ[F] K) :=
  AlgEquiv.autCongr (toImage F Ω K).symm

private theorem autEquiv_apply
    (ψ : (IsScalarTower.toAlgHom F K Ω).fieldRange ≃ₐ[F] (IsScalarTower.toAlgHom F K Ω).fieldRange) (x : K) :
    autEquiv F Ω K ψ x = (toImage F Ω K).symm (ψ (toImage F Ω K x)) :=
  rfl

private theorem map_decompositionSubgroup_autEquiv (B : ValuationSubring Ω) :
    ((B.comap (algebraMap (IsScalarTower.toAlgHom F K Ω).fieldRange Ω)).decompositionSubgroup F).map
        (autEquiv F Ω K).toMonoidHom =
      (B.comap (algebraMap K Ω)).decompositionSubgroup F := by
  have key0 : ∀ x : K, toImage F Ω K x ∈ B.comap (algebraMap (IsScalarTower.toAlgHom F K Ω).fieldRange Ω) ↔
      x ∈ B.comap (algebraMap K Ω) := by
    intro x
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, IntermediateField.algebraMap_apply, coe_toImage]
  ext δ
  obtain ⟨ψ, rfl⟩ := (autEquiv F Ω K).surjective δ
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  have key : ∀ x : K, x ∈ autEquiv F Ω K ψ • B.comap (algebraMap K Ω) ↔
      toImage F Ω K x ∈ ψ • B.comap (algebraMap (IsScalarTower.toAlgHom F K Ω).fieldRange Ω) := by
    intro x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      AlgEquiv.smul_def, AlgEquiv.smul_def, ← map_inv, autEquiv_apply, ValuationSubring.mem_comap,
      ValuationSubring.mem_comap, IntermediateField.algebraMap_apply, ← coe_toImage F Ω K, AlgEquiv.apply_symm_apply]
  constructor
  · intro h
    refine ValuationSubring.ext _ _ fun x => ?_
    rw [key, h, key0]
  · intro h
    refine ValuationSubring.ext _ _ fun z => ?_
    obtain ⟨x, rfl⟩ := (toImage F Ω K).surjective z
    rw [← key, h, key0]

variable [Normal F K]

private scoped instance : Normal F (IsScalarTower.toAlgHom F K Ω).fieldRange :=
  Normal.of_algEquiv (toImage F Ω K)

private theorem restrictNormalHom_eq :
    (AlgEquiv.restrictNormalHom K : (Ω ≃ₐ[F] Ω) →* (K ≃ₐ[F] K)) =
      (autEquiv F Ω K).toMonoidHom.comp (AlgEquiv.restrictNormalHom (IsScalarTower.toAlgHom F K Ω).fieldRange) := by
  ext γ x
  change AlgEquiv.restrictNormalHom K γ x =
    autEquiv F Ω K (AlgEquiv.restrictNormalHom (IsScalarTower.toAlgHom F K Ω).fieldRange γ) x
  rw [autEquiv_apply]
  apply (toImage F Ω K).injective
  rw [AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  have h1 : algebraMap K Ω (AlgEquiv.restrictNormalHom K γ x) = γ (algebraMap K Ω x) :=
    AlgEquiv.restrictNormal_commutes γ K x
  have h2 : ((AlgEquiv.restrictNormalHom (IsScalarTower.toAlgHom F K Ω).fieldRange γ (toImage F Ω K x) :
      (IsScalarTower.toAlgHom F K Ω).fieldRange) : Ω) = γ (toImage F Ω K x : Ω) :=
    AlgEquiv.restrictNormal_commutes γ (IsScalarTower.toAlgHom F K Ω).fieldRange (toImage F Ω K x)
  rw [coe_toImage, h1, h2, coe_toImage]

private theorem map_restrictNormalHom_decompositionSubgroup_eq_of_forall
    (h : ∀ (L : IntermediateField F Ω) [Normal F L] (A : ValuationSubring Ω),
      (A.decompositionSubgroup F).map (AlgEquiv.restrictNormalHom L) =
        (A.comap (algebraMap L Ω)).decompositionSubgroup F)
    (A : ValuationSubring Ω) :
    (A.decompositionSubgroup F).map (AlgEquiv.restrictNormalHom K) =
      (A.comap (algebraMap K Ω)).decompositionSubgroup F := by
  rw [restrictNormalHom_eq F Ω K, ← Subgroup.map_map, h _ A, map_decompositionSubgroup_autEquiv F Ω K]

private theorem fixingSubgroup_le_ker :
    (IsScalarTower.toAlgHom F K Ω).fieldRange.fixingSubgroup ≤
      (AlgEquiv.restrictNormalHom K : (Ω ≃ₐ[F] Ω) →* (K ≃ₐ[F] K)).ker := by
  intro γ hγ
  rw [IntermediateField.mem_fixingSubgroup_iff] at hγ
  rw [MonoidHom.mem_ker]
  refine AlgEquiv.ext fun x => (algebraMap K Ω).injective ?_
  have h1 : algebraMap K Ω (AlgEquiv.restrictNormalHom K γ x) = γ (algebraMap K Ω x) :=
    AlgEquiv.restrictNormal_commutes γ K x
  rw [h1, AlgEquiv.one_apply]
  exact hγ _ ⟨x, rfl⟩

private theorem mem_fixingSubgroup_iff_restrictNormalHom_mem {E : IntermediateField F Ω}
    (hE : E ≤ (IsScalarTower.toAlgHom F K Ω).fieldRange) (γ : Ω ≃ₐ[F] Ω) :
    γ ∈ E.fixingSubgroup ↔
      AlgEquiv.restrictNormalHom K γ ∈ (E.comap (IsScalarTower.toAlgHom F K Ω)).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h y hy
    have h1 : algebraMap K Ω (AlgEquiv.restrictNormalHom K γ y) = γ (algebraMap K Ω y) :=
      AlgEquiv.restrictNormal_commutes γ K y
    apply (algebraMap K Ω).injective
    rw [h1]
    exact h _ hy
  · intro h x hx
    obtain ⟨y, rfl⟩ := hE hx
    have h1 : algebraMap K Ω (AlgEquiv.restrictNormalHom K γ y) = γ (algebraMap K Ω y) :=
      AlgEquiv.restrictNormal_commutes γ K y
    have h2 : AlgEquiv.restrictNormalHom K γ y = y := h y hx
    change γ (algebraMap K Ω y) = algebraMap K Ω y
    rw [← h1, h2]

end Transport

variable (q : ℕ) [Fact q.Prime] (K : Type) [Field K] [NumberField K] [Algebra K (AlgebraicClosure ℚ)]
  [IsScalarTower ℚ K (AlgebraicClosure ℚ)] [Normal ℚ K] (w : HeightOneSpectrum (𝓞 K))

private theorem range_eq_decomp_of_forall_mem_iff (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : ∀ x : K, algebraMap K (AlgebraicClosure ℚ) x ∈ σ • padicPlace q ↔ w.valuation K x ≤ 1) :
    ((AlgEquiv.restrictNormalHom K).comp ((MulAut.conj σ).toMonoidHom.comp (localGaloisToGlobal q))).range =
      PlaceDecomp.decomp ℚ K w := by
  have hW : (σ • padicPlace q).comap (algebraMap K (AlgebraicClosure ℚ)) = (w.valuation K).valuationSubring :=
    ValuationSubring.ext _ _ fun x => by
      rw [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff]
      exact hσ x
  have hD : ((σ • padicPlace q).decompositionSubgroup ℚ).map (AlgEquiv.restrictNormalHom K) =
      PlaceDecomp.decomp ℚ K w := by
    have h := map_restrictNormalHom_decompositionSubgroup_eq_of_forall ℚ (AlgebraicClosure ℚ) K
      (fun L _ A => ValuationSubring.map_restrictNormalHom_decompositionSubgroup_eq L A) (σ • padicPlace q)
    rw [hW] at h
    exact h
  haveI : FiniteDimensional ℚ (IsScalarTower.toAlgHom ℚ K (AlgebraicClosure ℚ)).fieldRange :=
    (IsScalarTower.toAlgHom ℚ K (AlgebraicClosure ℚ)).toLinearMap.finiteDimensional_range
  refine range_comp_conj_comp_eq (AlgEquiv.restrictNormalHom K) _
    (IsScalarTower.toAlgHom ℚ K (AlgebraicClosure ℚ)).fieldRange.fixingSubgroup_isOpen
    (fixingSubgroup_le_ker ℚ (AlgebraicClosure ℚ) K)
    (localGaloisToGlobal q) (padicPlace q) ?_
    (ValuationSubring.decompositionSubgroup_padicPlace_le_closure_range_localGaloisToGlobal q) σ _ hD
  rintro _ ⟨t, rfl⟩
  exact localGaloisToGlobal_mem_decompositionSubgroup q t

private theorem map_comap_fixingSubgroup_eq_of_forall_mem_iff (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : ∀ x : K, algebraMap K (AlgebraicClosure ℚ) x ∈ σ • padicPlace q ↔ w.valuation K x ≤ 1)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hE : E ≤ (IsScalarTower.toAlgHom ℚ K (AlgebraicClosure ℚ)).fieldRange) :
    (E.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (localGaloisToGlobal q))).map
        ((AlgEquiv.restrictNormalHom K).comp ((MulAut.conj σ).toMonoidHom.comp (localGaloisToGlobal q))) =
      PlaceDecomp.decomp ℚ K w ⊓ (E.comap (IsScalarTower.toAlgHom ℚ K (AlgebraicClosure ℚ))).fixingSubgroup :=
  map_comap_eq_inf (AlgEquiv.restrictNormalHom K) _ _ (range_eq_decomp_of_forall_mem_iff q K w σ hσ)
    E.fixingSubgroup _ (mem_fixingSubgroup_iff_restrictNormalHom_mem ℚ (AlgebraicClosure ℚ) K hE)

end PlaceConjugate
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_layer_coboundary_adicCompletion_of_forall_conj_primeLocal_coboundary.PlaceConjugate"

namespace PlaceConjugate

open ExtCitation

variable (q : Nat.Primes) [Fact (q : ℕ).Prime] (K : Type) [Field K] [NumberField K] [Algebra K (AlgebraicClosure ℚ)]
  [IsScalarTower ℚ K (AlgebraicClosure ℚ)] (w : HeightOneSpectrum (𝓞 K))

private theorem range_eq_decomp_of_forall_mem_iff' [Normal ℚ K] (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : ∀ x : K, algebraMap K (AlgebraicClosure ℚ) x ∈ σ • padicPlace q ↔ w.valuation K x ≤ 1) :
    ((AlgEquiv.restrictNormalHom K).comp ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))).range =
      PlaceDecomp.decomp ℚ K w :=
  range_eq_decomp_of_forall_mem_iff (q : ℕ) K w σ hσ

private theorem map_comap_fixingSubgroup_eq_of_forall_mem_iff' [Normal ℚ K]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : ∀ x : K, algebraMap K (AlgebraicClosure ℚ) x ∈ σ • padicPlace q ↔ w.valuation K x ≤ 1)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hE : E ≤ (IsScalarTower.toAlgHom ℚ K (AlgebraicClosure ℚ)).fieldRange) :
    (E.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))).map
        ((AlgEquiv.restrictNormalHom K).comp ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))) =
      PlaceDecomp.decomp ℚ K w ⊓ (E.comap (IsScalarTower.toAlgHom ℚ K (AlgebraicClosure ℚ))).fixingSubgroup :=
  map_comap_fixingSubgroup_eq_of_forall_mem_iff (q : ℕ) K w σ hσ E hE

private theorem exists_forall_mem_iff_of_fixed' (L : Type) [Field L] [NumberField L] [Algebra L (AlgebraicClosure ℚ)]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ v : HeightOneSpectrum (𝓞 L),
      ∀ x : L, algebraMap L (AlgebraicClosure ℚ) x ∈ σ • padicPlace q ↔ v.valuation L x ≤ 1 :=
  exists_forall_mem_iff_of_fixed (q : ℕ) L σ

private theorem exists_forall_mem_iff' [IsGalois ℚ K] (hw : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∀ x : K, algebraMap K (AlgebraicClosure ℚ) x ∈ σ • padicPlace q ↔ w.valuation K x ≤ 1 :=
  exists_forall_mem_iff (q : ℕ) K w hw

end PlaceConjugate
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_layer_coboundary_adicCompletion_of_forall_conj_primeLocal_coboundary.PlaceConjugate"
end
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_layer_coboundary_adicCompletion_of_forall_conj_primeLocal_coboundary.PlaceConjugate"

section

open groupCohomology IntermediateField

namespace HasseGlue

private theorem exists_normal_of_isLevelConstant₁
    {Gq : Type} [Group Gq] (ρ : Gq →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (c : Gq → AlgebraicClosure ℚ) (hc : IsLevelConstant₁ ρ c) :
    ∃ N : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ N ∧ Normal ℚ N ∧
      ∀ g s : Gq, ρ s ∈ N.fixingSubgroup → c (g * s) = c g := by
  haveI hnormal : Normal ℚ (AlgebraicClosure ℚ) := inferInstance
  obtain ⟨F', hF'fin, hF'⟩ := hc
  haveI : FiniteDimensional ℚ F' := hF'fin
  exact ⟨normalClosure ℚ F' (AlgebraicClosure ℚ), normalClosure.is_finiteDimensional ℚ F' (AlgebraicClosure ℚ),
    normalClosure.normal ℚ F' (AlgebraicClosure ℚ),
    fun g s hs => hF' g s (fixingSubgroup_antitone (le_normalClosure F') hs)⟩

private theorem finite_range_of_forall_mem_fixingSubgroup
    {Gq : Type} [Group Gq] (ρ : Gq →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (c : Gq → AlgebraicClosure ℚ) (N : IntermediateField ℚ (AlgebraicClosure ℚ)) (hNfin : FiniteDimensional ℚ N)
    (hNnormal : Normal ℚ N) (hcN : ∀ g s : Gq, ρ s ∈ N.fixingSubgroup → c (g * s) = c g) :
    (Set.range c).Finite := by
  classical
  haveI : FiniteDimensional ℚ N := hNfin
  haveI : Normal ℚ N := hNnormal
  let π : Gq → (N ≃ₐ[ℚ] N) := fun g => AlgEquiv.restrictNormalHom N (ρ g)
  have hπ : ∀ g g' : Gq, π g = π g' → c g' = c g := by
    intro g g' h
    have hmem : ρ (g⁻¹ * g') ∈ N.fixingSubgroup := by
      rw [← @IntermediateField.restrictNormalHom_ker ℚ (AlgebraicClosure ℚ) _ _ _ N hNnormal, MonoidHom.mem_ker,
        map_mul, map_inv, map_mul, map_inv]
      exact inv_mul_eq_one.mpr h
    simpa only [mul_inv_cancel_left] using hcN g (g⁻¹ * g') hmem
  refine (Set.finite_range fun τ : N ≃ₐ[ℚ] N => c (Function.invFun π τ)).subset ?_
  rintro _ ⟨g, rfl⟩
  exact ⟨π g, hπ g (Function.invFun π (π g)) (Function.invFun_eq (f := π) ⟨g, rfl⟩).symm⟩

private theorem exists_normal_level_of_isLevelConstant₁
    {Gq : Type} [Group Gq] (ρ : Gq →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F₀]
    (c : Gq → AlgebraicClosure ℚ) (hc : IsLevelConstant₁ ρ c) :
    ∃ K : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K ∧ Normal ℚ K ∧ F₀ ≤ K ∧
      (∀ g, c g ∈ K) ∧ ∀ g s : Gq, ρ s ∈ K.fixingSubgroup → c (g * s) = c g := by
  haveI hnormal : Normal ℚ (AlgebraicClosure ℚ) := inferInstance
  obtain ⟨N, hNfin, hNnormal, hcN⟩ := exists_normal_of_isLevelConstant₁ ρ c hc
  haveI : FiniteDimensional ℚ N := hNfin
  have hV : (Set.range c).Finite := finite_range_of_forall_mem_fixingSubgroup ρ c N hNfin hNnormal hcN
  haveI : Finite (Set.range c) := hV.to_subtype
  haveI : FiniteDimensional ℚ (adjoin ℚ (Set.range c)) := finiteDimensional_adjoin fun x _ => hnormal.isIntegral x
  obtain ⟨K₀, hK₀fin, hF₀K₀, hNK₀, hcK₀⟩ : ∃ K₀ : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ K₀ ∧ F₀ ≤ K₀ ∧ N ≤ K₀ ∧ ∀ g, c g ∈ K₀ :=
    ⟨F₀ ⊔ N ⊔ adjoin ℚ (Set.range c), inferInstance, le_sup_left.trans le_sup_left, le_sup_right.trans le_sup_left,
      fun g => SetLike.le_def.mp le_sup_right (subset_adjoin ℚ (Set.range c) ⟨g, rfl⟩)⟩
  haveI : FiniteDimensional ℚ K₀ := hK₀fin
  refine ⟨normalClosure ℚ K₀ (AlgebraicClosure ℚ), normalClosure.is_finiteDimensional ℚ K₀ (AlgebraicClosure ℚ),
    normalClosure.normal ℚ K₀ (AlgebraicClosure ℚ), hF₀K₀.trans (le_normalClosure K₀),
    fun g => SetLike.le_def.mp (le_normalClosure K₀) (hcK₀ g), fun g s hs => ?_⟩
  exact hcN g s (fixingSubgroup_antitone (hNK₀.trans (le_normalClosure K₀)) hs)

end HasseGlue
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_layer_coboundary_adicCompletion_of_forall_conj_primeLocal_coboundary.PlaceConjugate"
end
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_layer_coboundary_adicCompletion_of_forall_conj_primeLocal_coboundary.PlaceConjugate"

section

open IsDedekindDomain NumberField NumberField.PlaceDecomp
open scoped NumberField.PlaceDecomp

namespace HasseGlue

variable {E K : Type} [Field E] [Field K] [NumberField K] [Algebra E K] {w : HeightOneSpectrum (𝓞 K)}

private theorem decomp_smul_algebraMap (σ : decomp E K w) (x : K) :
    σ • algebraMap K (w.adicCompletion K) x = algebraMap K (w.adicCompletion K) ((σ : K ≃ₐ[E] K) x) := by
  rw [smul_def]
  exact actRingEquiv_coe σ (WithVal.toVal (w.valuation K) x)

private theorem ofMulDistribMulAction_ρ_ofMul_map_algebraMap (σ : decomp E K w) (u : Kˣ) :
    (Rep.ofMulDistribMulAction (decomp E K w) (w.adicCompletion K)ˣ).ρ σ
        (Additive.ofMul (Units.map (algebraMap K (w.adicCompletion K)).toMonoidHom u)) =
      Additive.ofMul (Units.map (algebraMap K (w.adicCompletion K)).toMonoidHom
        (Units.map (MonoidHomClass.toMonoidHom (σ : K ≃ₐ[E] K)) u)) := by
  rw [Rep.ofMulDistribMulAction_ρ_apply_apply]
  congr 1
  refine Units.ext ?_
  rw [coe_smul_units]
  exact decomp_smul_algebraMap σ u

private theorem exists_forall_eq_smul_sub_add_of_surjective
    {Gq D A : Type} [Group Gq] [Group D] [AddCommGroup A] (act : D → A → A)
    (res : Gq →* D) (hres : Function.Surjective res) (c : Gq → A)
    (hc : ∀ g s : Gq, res s = 1 → c (g * s) = c g) (F : D × D → A)
    (hF : ∀ g h : Gq, F (res g, res h) = act (res g) (c h) - c (g * h) + c g) :
    ∃ y : D → A, ∀ δ ε : D, F (δ, ε) = act δ (y ε) - y (δ * ε) + y δ := by
  have key : ∀ g g' : Gq, res g = res g' → c g = c g' := by
    intro g g' h
    have hs : res (g⁻¹ * g') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    simpa only [mul_inv_cancel_left] using (hc g (g⁻¹ * g') hs).symm
  refine ⟨fun δ => c (Function.surjInv hres δ), fun δ ε => ?_⟩
  obtain ⟨g, rfl⟩ := hres δ
  obtain ⟨h, rfl⟩ := hres ε
  rw [hF g h, key h (Function.surjInv hres (res h)) (Function.surjInv_eq hres (res h)).symm,
    key g (Function.surjInv hres (res g)) (Function.surjInv_eq hres (res g)).symm,
    key (g * h) (Function.surjInv hres (res g * res h)) (by rw [Function.surjInv_eq hres, map_mul])]

private theorem ofMul_mul_inv_mul {α : Type} [Group α] (a b c : α) :
    Additive.ofMul (a * b⁻¹ * c) = Additive.ofMul a - Additive.ofMul b + Additive.ofMul c := by
  rw [ofMul_mul, ofMul_mul, ofMul_inv, sub_eq_add_neg]

private theorem exists_forall_ofMul_map_eq_ρ_sub_add_of_surjective
    {E K K'' : Type} [Field E] [Field K] [Field K''] [NumberField K''] [Algebra E K''] [Algebra K K'']
    (w'' : IsDedekindDomain.HeightOneSpectrum (𝓞 K'')) {Gq : Type} [Group Gq]
    (res : Gq →* decomp E K'' w'') (hres : Function.Surjective res) (c₁ : Gq → K''ˣ)
    (hc : ∀ g s : Gq, res s = 1 → c₁ (g * s) = c₁ g) (F₀ : decomp E K'' w'' × decomp E K'' w'' → Kˣ)
    (hF : ∀ g h : Gq, Units.map (algebraMap K K'').toMonoidHom (F₀ (res g, res h)) =
      Units.map (MonoidHomClass.toMonoidHom ((res g : decomp E K'' w'') : K'' ≃ₐ[E] K'')) (c₁ h) *
        (c₁ (g * h))⁻¹ * c₁ g) :
    ∃ y : decomp E K'' w'' →
        Rep.ofMulDistribMulAction (decomp E K'' w'') (w''.adicCompletion K'')ˣ,
      ∀ g h : decomp E K'' w'',
        Additive.ofMul (Units.map (algebraMap K'' (w''.adicCompletion K'')).toMonoidHom
            (Units.map (algebraMap K K'').toMonoidHom (F₀ (g, h)))) =
          (Rep.ofMulDistribMulAction (decomp E K'' w'') (w''.adicCompletion K'')ˣ).ρ g (y h) - y (g * h) + y g := by
  refine exists_forall_eq_smul_sub_add_of_surjective
    (fun δ a => (Rep.ofMulDistribMulAction (decomp E K'' w'') (w''.adicCompletion K'')ˣ).ρ δ a) res hres
    (fun g => Additive.ofMul (Units.map (algebraMap K'' (w''.adicCompletion K'')).toMonoidHom (c₁ g)))
    (fun g s hs => by simp only [hc g s hs])
    (fun p => Additive.ofMul (Units.map (algebraMap K'' (w''.adicCompletion K'')).toMonoidHom
      (Units.map (algebraMap K K'').toMonoidHom (F₀ p)))) (fun g h => ?_)
  rw [hF g h, map_mul, map_mul, map_inv, ofMulDistribMulAction_ρ_ofMul_map_algebraMap]
  exact ofMul_mul_inv_mul (α := (w''.adicCompletion K'')ˣ) _ _ _

end HasseGlue
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_layer_coboundary_adicCompletion_of_forall_conj_primeLocal_coboundary.PlaceConjugate"
end
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_layer_coboundary_adicCompletion_of_forall_conj_primeLocal_coboundary.PlaceConjugate"

namespace HasseAsm

private theorem val_ρ_sub_add (S : Finset Nat.Primes) (L' : IntermediateField ℚ (AlgebraicClosure ℚ))
    (g : ↥L'.fixingSubgroup) (u v w : sUnitsMaxRep S L') :
    sUnitsMaxRep.val S L' ((sUnitsMaxRep S L').ρ g u - v + w) =
      (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • sUnitsMaxRep.val S L' u * (sUnitsMaxRep.val S L' v)⁻¹ *
        sUnitsMaxRep.val S L' w := by
  rw [← sUnitsMaxRep.val_ρ]
  rfl

end HasseAsm
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_layer_coboundary_adicCompletion_of_forall_conj_primeLocal_coboundary.PlaceConjugate"

section
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

set_option maxHeartbeats 4000000 in
theorem solution
    (S : Finset Nat.Primes) (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [Normal ↥L ↥(levelField L F hLF)]
    (ι : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) →*
      (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (hιg : ∀ g : ↥L.fixingSubgroup,
      ι (levelGal L F hLF g) = (g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (φ : Rep.res ι ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
      NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))
    (hφval : ∀ x,
      ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom x) :
          ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hloc : ∀ (q : ↥S) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      ∃ c : ↥(L.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes)))) →
          sUnitsMaxRep S L,
        IsLevelConstant₁
            ((((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes))).comp
              (L.fixingSubgroup.comap
                ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes)))).subtype)) c ∧
          ∀ g h : ↥(L.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes)))),
            ((f (((((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes))).subgroupComap
                      L.fixingSubgroup g : ↥L.fixingSubgroup) :
                    ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype),
                  ((((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes))).subgroupComap
                      L.fixingSubgroup h : ↥L.fixingSubgroup) :
                    ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
                (sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
              sUnitsMaxRep S L) =
              (sUnitsMaxRep S L).ρ
                  (((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes))).subgroupComap
                    L.fixingSubgroup g) (c h) - c (g * h) + c g)
    (v : {v // v ∈ placesOverPrimesFinset ↥L S}) :
    ∃ (K'' : Type) (_ : Field K'') (_ : NumberField K'') (_ : Algebra ↥L K'')
      (_ : Algebra ↥(levelField L F hLF) K'')
      (_ : IsScalarTower ↥L ↥(levelField L F hLF) K'') (_ : IsGalois ↥L K'') (w'' : HeightOneSpectrum (𝓞 K''))
      (_ : HeightOneSpectrum.under (𝓞 ↥(levelField L F hLF)) w'' = PlaceAbove.above ↥L ↥(levelField L F hLF) v.1)
      (y : PlaceDecomp.decomp ↥L K'' w'' →
        Rep.ofMulDistribMulAction (PlaceDecomp.decomp ↥L K'' w'') (w''.adicCompletion K'')ˣ),
      ∀ g h : PlaceDecomp.decomp ↥L K'' w'',
        Additive.ofMul (Units.map (algebraMap K'' (w''.adicCompletion K'')).toMonoidHom
            (Units.map (algebraMap ↥(levelField L F hLF) K'').toMonoidHom
              (SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)
                ((mapCocycles₂ ι φ f)
                  (AlgEquiv.restrictNormalHom ↥(levelField L F hLF) (g : K'' ≃ₐ[↥L] K''),
                    AlgEquiv.restrictNormalHom ↥(levelField L F hLF) (h : K'' ≃ₐ[↥L] K'')))))) =
          (Rep.ofMulDistribMulAction (PlaceDecomp.decomp ↥L K'' w'') (w''.adicCompletion K'')ˣ).ρ g (y h) -
            y (g * h) + y g := by

  obtain ⟨q, hqS, hqv⟩ : ∃ q ∈ S, ((q : ℕ) : 𝓞 ↥L) ∈ v.1.asIdeal := (mem_placesOverPrimesFinset ↥L S v.1).1 v.2
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  letI : Algebra ℚ ↥(levelField L F hLF) := DivisionRing.toRatAlgebra
  haveI := HasseLevelFurniture.isScalarTower_rat_levelField_algClosure L F hLF
  haveI := HasseLevelFurniture.normal_rat_levelField L F hLF
  haveI : IsGalois ℚ ↥(levelField L F hLF) := ⟨⟩
  have hw : ((q : ℕ) : 𝓞 ↥(levelField L F hLF)) ∈ (PlaceAbove.above ↥L ↥(levelField L F hLF) v.1).asIdeal := by
    rw [← PlaceAbove.comap_above ↥L ↥(levelField L F hLF) v.1, Ideal.mem_comap, map_natCast] at hqv
    exact hqv
  have hσex := PlaceConjugate.exists_forall_mem_iff' q ↥(levelField L F hLF)
    (PlaceAbove.above ↥L ↥(levelField L F hLF) v.1) hw
  obtain ⟨σ, hσK⟩ := hσex

  obtain ⟨c, hc, hcf⟩ := hloc ⟨q, hqS⟩ σ

  have hcval : IsLevelConstant₁
      ((((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes))).comp
        (L.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes)))).subtype))
      (fun g => ((sUnitsMaxRep.val S L (c g) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) :=
    hc.imp fun N hN => ⟨hN.1, fun g s hs =>
      congrArg (fun m => ((sUnitsMaxRep.val S L m : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) (hN.2 g s hs)⟩
  have hKex := HasseGlue.exists_normal_level_of_isLevelConstant₁ _ F _ hcval
  obtain ⟨Kbig, hKfin, hKnormal, hFK, hcmem, hcconst⟩ := hKex
  haveI := hKfin
  haveI := hKnormal
  have hLK : L ≤ Kbig := hLF.trans hFK

  letI : Algebra ℚ ↥(levelField L Kbig hLK) := DivisionRing.toRatAlgebra
  haveI := HasseLevelFurniture.isScalarTower_rat_levelField_algClosure L Kbig hLK
  haveI := HasseLevelFurniture.normal_rat_levelField L Kbig hLK
  haveI := HasseLevelFurniture.isScalarTower_rat_base_levelField L Kbig hLK
  haveI hGalK'' : IsGalois ↥L ↥(levelField L Kbig hLK) := HasseLevelFurniture.isGalois_levelField L Kbig hLK
  letI := HasseLevelFurniture.levelAlgebra L F Kbig hLF hLK hFK
  haveI := HasseLevelFurniture.levelAlgebra_isScalarTower L F Kbig hLF hLK hFK
  haveI := HasseLevelFurniture.levelAlgebra_isScalarTower_algClosure L F Kbig hLF hLK hFK

  have hwex := PlaceConjugate.exists_forall_mem_iff_of_fixed' q ↥(levelField L Kbig hLK) σ
  obtain ⟨w'', hσ''⟩ := hwex
  have hunder : HeightOneSpectrum.under (𝓞 ↥(levelField L F hLF)) w'' =
      PlaceAbove.above ↥L ↥(levelField L F hLF) v.1 := by
    exact PlaceConjugate.under_eq_of_forall_mem_iff _ _ _ _ hσK w'' hσ''

  have hrange : ((AlgEquiv.restrictNormalHom ↥(levelField L Kbig hLK)).comp
        ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))).range =
      PlaceDecomp.decomp ℚ ↥(levelField L Kbig hLK) w'' := by
    exact PlaceConjugate.range_eq_decomp_of_forall_mem_iff' q ↥(levelField L Kbig hLK) w'' σ hσ''
  have hE : L ≤ (IsScalarTower.toAlgHom ℚ ↥(levelField L Kbig hLK) (AlgebraicClosure ℚ)).fieldRange := by
    intro x hx
    exact ⟨levelFieldEquiv L Kbig hLK ⟨x, hLK hx⟩, rfl⟩
  have hmap : (L.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))).map
        ((AlgEquiv.restrictNormalHom ↥(levelField L Kbig hLK)).comp
          ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))) =
      PlaceDecomp.decomp ℚ ↥(levelField L Kbig hLK) w'' ⊓
        (L.comap (IsScalarTower.toAlgHom ℚ ↥(levelField L Kbig hLK) (AlgebraicClosure ℚ))).fixingSubgroup := by
    exact PlaceConjugate.map_comap_fixingSubgroup_eq_of_forall_mem_iff' q ↥(levelField L Kbig hLK) w'' σ hσ'' L hE
  have hsurj : Function.Surjective (HasseLevelFurniture.resHom L Kbig hLK q σ w'' hrange) := by
    exact HasseLevelFurniture.resHom_surjective L Kbig hLK q σ w'' hrange hmap

  let c₁ : ↥(L.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q))) →
      (↥(levelField L Kbig hLK))ˣ := fun d =>
    Units.mk0 (levelFieldEquiv L Kbig hLK ⟨_, hcmem d⟩) (by
      intro h0
      apply (sUnitsMaxRep.val S L (c d)).ne_zero
      have h1 := congrArg (fun z : ↥(levelField L Kbig hLK) => (z : AlgebraicClosure ℚ)) h0
      simp only [coe_levelFieldEquiv, ZeroMemClass.coe_zero] at h1
      exact h1)

  have hc₁ : ∀ g s, HasseLevelFurniture.resHom L Kbig hLK q σ w'' hrange s = 1 → c₁ (g * s) = c₁ g := by
    intro g s hs
    have hfix := HasseLevelFurniture.mem_fixingSubgroup_of_resHom_eq_one L Kbig hLK q σ w'' hrange s hs
    apply Units.ext
    apply Subtype.ext
    simp only [c₁, Units.val_mk0, coe_levelFieldEquiv, map_mul]
    exact hcconst g s hfix

  have hF : ∀ g h, Units.map (algebraMap ↥(levelField L F hLF) ↥(levelField L Kbig hLK)).toMonoidHom
        (SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)
          ((mapCocycles₂ ι φ f)
            (AlgEquiv.restrictNormalHom ↥(levelField L F hLF)
                (HasseLevelFurniture.resHom L Kbig hLK q σ w'' hrange g :
                  ↥(levelField L Kbig hLK) ≃ₐ[↥L] ↥(levelField L Kbig hLK)),
              AlgEquiv.restrictNormalHom ↥(levelField L F hLF)
                (HasseLevelFurniture.resHom L Kbig hLK q σ w'' hrange h :
                  ↥(levelField L Kbig hLK) ≃ₐ[↥L] ↥(levelField L Kbig hLK))))) =
      Units.map (MonoidHomClass.toMonoidHom
          (HasseLevelFurniture.resHom L Kbig hLK q σ w'' hrange g :
            ↥(levelField L Kbig hLK) ≃ₐ[↥L] ↥(levelField L Kbig hLK))) (c₁ h) *
        (c₁ (g * h))⁻¹ * c₁ g := by
    intro g h
    have h1 := congrArg (fun m => ((sUnitsMaxRep.val S L m : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
      (hcf g h)
    have h2 := HasseAsm.val_ρ_sub_add S L
      ((((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal q)).subgroupComap L.fixingSubgroup) g)
      (c h) (c (g * h)) (c g)
    have h3 := h1.trans (congrArg Units.val h2)
    simp only [Units.val_mul, Units.val_inv_eq_inv_val] at h3
    have h5 : ∀ a b : ↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF),
        (mapCocycles₂ ι φ f) (a, b) =
          φ.hom (f (ι a, ι b)) :=
      fun _ _ => rfl
    apply Units.ext
    apply Subtype.ext
    simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_mul, Units.val_inv_eq_inv_val, c₁, Units.val_mk0,
      HasseLevelFurniture.coe_resHom, HasseLevelFurniture.restrictNormalHom_levelGal, map_mul]
    rw [h5, hιg, hιg]
    push_cast
    simp only [levelGal_apply_coe, coe_levelFieldEquiv]
    exact (hφval (f
      ((HasseLevelFurniture.lamE L q σ g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype),
        (HasseLevelFurniture.lamE L q σ h :
          ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)))).trans h3
  refine ⟨↥(levelField L Kbig hLK), inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hGalK'', w'', hunder, ?_⟩
  exact HasseGlue.exists_forall_ofMul_map_eq_ρ_sub_add_of_surjective w''
    (HasseLevelFurniture.resHom L Kbig hLK q σ w'' hrange) hsurj c₁ hc₁
    (fun gh => SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)
      ((mapCocycles₂ ι φ f)
        (AlgEquiv.restrictNormalHom ↥(levelField L F hLF)
            (gh.1 : ↥(levelField L Kbig hLK) ≃ₐ[↥L] ↥(levelField L Kbig hLK)),
          AlgEquiv.restrictNormalHom ↥(levelField L F hLF)
            (gh.2 : ↥(levelField L Kbig hLK) ≃ₐ[↥L] ↥(levelField L Kbig hLK)))))
    hF

end
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_layer_coboundary_adicCompletion_of_forall_conj_primeLocal_coboundary.PlaceConjugate"

end S_NumberField_LevelArith_exists_layer_coboundary_adicCompletion_of_forall_conj_primeLocal_coboundary
end P2MW
export P2MW.S_NumberField_LevelArith_exists_layer_coboundary_adicCompletion_of_forall_conj_primeLocal_coboundary (solution)
