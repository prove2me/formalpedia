-- Prove2me | solution 1 for M4aHerbrand.exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/32bf012b-cf6d-596a-afb6-02282b094142

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_unitsMap_beta_mem_principalIdeles_iff
import Theorems.Thm_M4aHerbrand_GenuineDescent_injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm
import Theorems.Thm_M4aHerbrand_Bridge_genuineBeta_comp_of_tower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower.M4aHerbrand"

namespace M4aHerbrand
p2m_export "M4aHerbrand" "principalIdeles IdeleClassGroup IdeleGaloisDescent GenuineDescent.genuineBaseChange subsingleton_ideleGaloisDescent GenuineDescent.unitsMap_beta_mem_principalIdeles_iff GenuineDescent.injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm Bridge.genuineBeta_comp_of_tower"
namespace TowerPkgProof
p2m_open "M4aHerbrand"

noncomputable section

open TensorProduct M4aHerbrand.Bridge M4aHerbrand.GenuineDescent
open scoped TensorProduct

section Galois

variable {E F M : Type} [Field E] [Field F] [Field M] [Algebra E F] [Algebra E M] [Algebra F M] [IsScalarTower E F M]

variable (E F M) in

def resHom : (M ≃ₐ[F] M) →* (M ≃ₐ[E] M) where
  toFun g := g.restrictScalars E
  map_one' := rfl
  map_mul' _ _ := rfl

@[scoped simp] theorem resHom_apply (g : M ≃ₐ[F] M) (x : M) : resHom E F M g x = g x := rfl

variable (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (F ≃ₐ[E] F))
  (hι : ∀ (g : M ≃ₐ[E] M) (x : F), algebraMap F M (ι (QuotientGroup.mk g) x) = g (algebraMap F M x))
omit [Algebra F M] [IsScalarTower E F M] in
theorem ι_mk_eq_one_of_mem (s : M ≃ₐ[E] M) (hs : s ∈ S) : ι (QuotientGroup.mk s) = 1 := by
  rw [(QuotientGroup.eq_one_iff s).mpr hs, map_one]

include hι

omit [IsScalarTower E F M] in

theorem mem_iff_forall_apply_algebraMap (g : M ≃ₐ[E] M) :
    g ∈ S ↔ ∀ x : F, g (algebraMap F M x) = algebraMap F M x := by
  constructor
  · intro hg x
    have h1 : (QuotientGroup.mk g : (M ≃ₐ[E] M) ⧸ S) = 1 := (QuotientGroup.eq_one_iff g).mpr hg
    rw [← hι g x, h1, map_one, AlgEquiv.one_apply]
  · intro hg
    have h1 : ι (QuotientGroup.mk g) = 1 := by
      ext x
      apply (algebraMap F M).injective
      rw [hι, AlgEquiv.one_apply]
      exact hg x
    exact (QuotientGroup.eq_one_iff g).mp ((map_eq_one_iff ι ι.injective).mp h1)

theorem resHom_mem (τ : M ≃ₐ[F] M) : resHom E F M τ ∈ S :=
  (mem_iff_forall_apply_algebraMap S ι hι _).mpr fun x => τ.commutes x

end Galois

section Descent

variable {E F M : Type} [Field E] [Field F] [Field M] [NumberField M] [Algebra E F] [Algebra E M] [Algebra F M]
  [IsScalarTower E F M]

def descentMF (DM : IdeleGaloisDescent (𝓞 M) E M) : IdeleGaloisDescent (𝓞 M) F M where
  act := DM.act.comp (resHom E F M)
  compat g x := DM.compat (resHom E F M g) x
  continuous_act g := DM.continuous_act (resHom E F M g)

theorem descentMF_unitsAct (DM : IdeleGaloisDescent (𝓞 M) E M) (g : M ≃ₐ[F] M) (u : (AdeleRing (𝓞 M) M)ˣ) :
    (descentMF DM).unitsAct g u = DM.unitsAct (resHom E F M g) u := rfl

end Descent

section ClassAct

variable {R E F : Type*} [CommRing R] [IsDedekindDomain R] [Field E] [Field F] [Algebra R F] [IsFractionRing R F]
  [Algebra E F]

theorem classAct_mk (D : IdeleGaloisDescent R E F) (g : F ≃ₐ[E] F) (x : (AdeleRing R F)ˣ) :
    D.classAct g (QuotientGroup.mk x) = QuotientGroup.mk (D.unitsAct g x) := rfl

end ClassAct

section Beta

variable (E F M : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field M] [NumberField M]
  [Algebra E F] [Algebra E M] [Algebra F M] [IsScalarTower E F M]

theorem genuineβ_tower_apply (a : AdeleRing (𝓞 E) E) : genuineβ F M (genuineβ E F a) = genuineβ E M a := by
  rw [← RingHom.comp_apply, M4aHerbrand.Bridge.genuineBeta_comp_of_tower E F M]

omit [NumberField E] in
theorem genuineRingEquiv_tmul (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (a : AdeleRing (𝓞 K) K) (l : L) :
    genuineRingEquiv K L (a ⊗ₜ[K] l) = genuineβ K L a * algebraMap L (AdeleRing (𝓞 L) L) l := by
  have h : a ⊗ₜ[K] l = (a ⊗ₜ[K] (1 : L)) * ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] l) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h, map_mul, genuineRingEquiv_tmul_one, genuineRingEquiv_one_tmul]

theorem genuineβ_genuineRingEquiv (z : (AdeleRing (𝓞 E) E) ⊗[E] F) :
    genuineβ F M (genuineRingEquiv E F z) =
      genuineRingEquiv E M (LinearMap.lTensor (AdeleRing (𝓞 E) E) (IsScalarTower.toAlgHom E F M).toLinearMap z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    rw [LinearMap.lTensor_tmul, genuineRingEquiv_tmul, genuineRingEquiv_tmul, map_mul, genuineβ_tower_apply,
      AlgHom.toLinearMap_apply, IsScalarTower.toAlgHom_apply, genuineβ_compat]
  | add x y hx hy => simp only [map_add, hx, hy]

omit [NumberField F] [NumberField M] in

theorem lTensor_congr (γ : F ≃ₐ[E] F) (g : M ≃ₐ[E] M) (hγ : ∀ x : F, algebraMap F M (γ x) = g (algebraMap F M x))
    (z : (AdeleRing (𝓞 E) E) ⊗[E] F) :
    LinearMap.lTensor (AdeleRing (𝓞 E) E) (IsScalarTower.toAlgHom E F M).toLinearMap
        (Algebra.TensorProduct.congr (AlgEquiv.refl : AdeleRing (𝓞 E) E ≃ₐ[AdeleRing (𝓞 E) E] _) γ z) =
      Algebra.TensorProduct.congr (AlgEquiv.refl : AdeleRing (𝓞 E) E ≃ₐ[AdeleRing (𝓞 E) E] _) g
        (LinearMap.lTensor (AdeleRing (𝓞 E) E) (IsScalarTower.toAlgHom E F M).toLinearMap z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
      Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    simp only [AlgHom.toLinearMap_apply, IsScalarTower.toAlgHom_apply]
    congr 1
    exact hγ b
  | add x y hx hy => simp only [map_add, hx, hy]

theorem genuineβ_act (γ : F ≃ₐ[E] F) (g : M ≃ₐ[E] M) (hγ : ∀ x : F, algebraMap F M (γ x) = g (algebraMap F M x))
    (a : AdeleRing (𝓞 F) F) :
    genuineβ F M ((genuineDescentDatum E F).act γ a) = (genuineDescentDatum E M).act g (genuineβ F M a) := by
  obtain ⟨z, rfl⟩ : ∃ z, genuineRingEquiv E F z = a := ⟨(genuineRingEquiv E F).symm a, RingEquiv.apply_symm_apply _ _⟩
  change genuineβ F M (genuineRingEquiv E F (Algebra.TensorProduct.congr AlgEquiv.refl γ
      ((genuineRingEquiv E F).symm (genuineRingEquiv E F z)))) =
    genuineRingEquiv E M (Algebra.TensorProduct.congr AlgEquiv.refl g
      ((genuineRingEquiv E M).symm (genuineβ F M (genuineRingEquiv E F z))))
  rw [RingEquiv.symm_apply_apply, genuineβ_genuineRingEquiv, genuineβ_genuineRingEquiv, RingEquiv.symm_apply_apply,
    lTensor_congr E F M γ g hγ]

abbrev βU : (AdeleRing (𝓞 F) F)ˣ →* (AdeleRing (𝓞 M) M)ˣ := Units.map (genuineBaseChange F M).β.toMonoidHom

theorem βU_unitsAct (γ : F ≃ₐ[E] F) (g : M ≃ₐ[E] M) (hγ : ∀ x : F, algebraMap F M (γ x) = g (algebraMap F M x))
    (x : (AdeleRing (𝓞 F) F)ˣ) :
    βU F M ((genuineDescentDatum E F).unitsAct γ x) = (genuineDescentDatum E M).unitsAct g (βU F M x) := by
  apply Units.ext
  exact genuineβ_act E F M γ g hγ (x : AdeleRing (𝓞 F) F)

theorem principalIdeles_le_comap_βU :
    principalIdeles (𝓞 F) F ≤ (principalIdeles (𝓞 M) M).comap (βU F M) := by
  rintro _ ⟨u, rfl⟩
  exact ⟨Units.map (algebraMap F M : F →* M) u, Units.ext ((genuineBaseChange F M).β_compat (u : F)).symm⟩

def jHom : IdeleClassGroup (𝓞 F) F →* IdeleClassGroup (𝓞 M) M :=
  QuotientGroup.map _ _ (βU F M) (principalIdeles_le_comap_βU F M)

theorem jHom_mk (x : (AdeleRing (𝓞 F) F)ˣ) :
    jHom F M (QuotientGroup.mk x) = QuotientGroup.mk (βU F M x) := rfl

theorem jHom_classAct (γ : F ≃ₐ[E] F) (g : M ≃ₐ[E] M) (hγ : ∀ x : F, algebraMap F M (γ x) = g (algebraMap F M x))
    (c : IdeleClassGroup (𝓞 F) F) :
    jHom F M ((genuineDescentDatum E F).classAct γ c) = (genuineDescentDatum E M).classAct g (jHom F M c) := by
  induction c using QuotientGroup.induction_on with
  | H x => rw [classAct_mk, jHom_mk, jHom_mk, classAct_mk, βU_unitsAct E F M γ g hγ]

theorem jHom_injective [IsGalois F M] : Function.Injective (jHom F M) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  induction c using QuotientGroup.induction_on with
  | H x =>
    rw [jHom_mk, QuotientGroup.eq_one_iff] at hc
    exact (QuotientGroup.eq_one_iff x).mpr
      ((M4aHerbrand.GenuineDescent.unitsMap_beta_mem_principalIdeles_iff F M x).mp hc)

omit [NumberField E] in

theorem mk_mem_range_jHom [IsGalois F M] (DM : IdeleGaloisDescent (𝓞 M) E M) (u : (AdeleRing (𝓞 M) M)ˣ)
    (hu : ∀ τ : M ≃ₐ[F] M, (DM.unitsAct (resHom E F M τ) u)⁻¹ * u ∈ principalIdeles (𝓞 M) M) :
    (QuotientGroup.mk u : IdeleClassGroup (𝓞 M) M) ∈ (jHom F M).range := by
  obtain ⟨_, h90, _⟩ :=
    (M4aHerbrand.GenuineDescent.injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm F M (descentMF DM)).2
  obtain ⟨y, ⟨x, rfl⟩, p, hp, hxp⟩ := Subgroup.mem_sup.mp (h90 u hu)
  refine ⟨QuotientGroup.mk x, ?_⟩
  rw [jHom_mk, ← hxp, QuotientGroup.mk_mul_of_mem _ hp]

end Beta

section Reps

variable (E F M : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra E F] [Algebra E M] [Algebra F M] [IsScalarTower E F M]
    (D : IdeleGaloisDescent (𝓞 F) E F) (DM : IdeleGaloisDescent (𝓞 M) E M)
    (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (F ≃ₐ[E] F))
    (hι : ∀ (g : M ≃ₐ[E] M) (x : F), algebraMap F M (ι (QuotientGroup.mk g) x) = g (algebraMap F M x))

noncomputable def JRep
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ]
    (hactIM : ∀ (g : (M ≃ₐ[E] M)) (x : (AdeleRing (𝓞 M) M)ˣ), g • x = DM.unitsAct g x) :
    Rep.res (ι.toMonoidHom.comp (QuotientGroup.mk' S)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
      Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (βU F M)).toIntLinearMap, fun g => LinearMap.ext fun a => by
    haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 F) E F
    haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 M) E M
    obtain rfl : D = genuineDescentDatum E F := Subsingleton.elim _ _
    obtain rfl : DM = genuineDescentDatum E M := Subsingleton.elim _ _
    change Additive.ofMul (βU F M (((ι.toMonoidHom.comp (QuotientGroup.mk' S)) g)
        • (Additive.toMul : Additive (AdeleRing (𝓞 F) F)ˣ ≃ (AdeleRing (𝓞 F) F)ˣ) a))
      = Additive.ofMul (g • βU F M ((Additive.toMul : Additive (AdeleRing (𝓞 F) F)ˣ ≃ (AdeleRing (𝓞 F) F)ˣ) a))
    rw [hactI, hactIM]
    exact congrArg Additive.ofMul (βU_unitsAct E F M (ι (QuotientGroup.mk g)) g (hι g) _)⟩

theorem JRep_hom_apply
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ]
    (hactIM : ∀ (g : (M ≃ₐ[E] M)) (x : (AdeleRing (𝓞 M) M)ˣ), g • x = DM.unitsAct g x)
    (x : (AdeleRing (𝓞 F) F)ˣ) :
    (JRep E F M D DM S ι hι hactI hactIM).hom (Additive.ofMul x) = Additive.ofMul (βU F M x) := rfl

noncomputable def jRep
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : (F ≃ₐ[E] F)) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    [MulDistribMulAction (M ≃ₐ[E] M) (IdeleClassGroup (𝓞 M) M)]
    (hactM : ∀ (g : (M ≃ₐ[E] M)) (c : IdeleClassGroup (𝓞 M) M), g • c = DM.classAct g c) :
    Rep.res (ι.toMonoidHom.comp (QuotientGroup.mk' S)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) ⟶
      Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (IdeleClassGroup (𝓞 M) M) :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (jHom F M)).toIntLinearMap, fun g => LinearMap.ext fun a => by
    haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 F) E F
    haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 M) E M
    obtain rfl : D = genuineDescentDatum E F := Subsingleton.elim _ _
    obtain rfl : DM = genuineDescentDatum E M := Subsingleton.elim _ _
    change Additive.ofMul (jHom F M (((ι.toMonoidHom.comp (QuotientGroup.mk' S)) g)
        • (Additive.toMul : Additive (IdeleClassGroup (𝓞 F) F) ≃ IdeleClassGroup (𝓞 F) F) a))
      = Additive.ofMul (g • jHom F M ((Additive.toMul : Additive (IdeleClassGroup (𝓞 F) F) ≃ IdeleClassGroup (𝓞 F) F) a))
    rw [hact, hactM]
    exact congrArg Additive.ofMul (jHom_classAct E F M (ι (QuotientGroup.mk g)) g (hι g) _)⟩

theorem jRep_hom_apply
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : (F ≃ₐ[E] F)) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    [MulDistribMulAction (M ≃ₐ[E] M) (IdeleClassGroup (𝓞 M) M)]
    (hactM : ∀ (g : (M ≃ₐ[E] M)) (c : IdeleClassGroup (𝓞 M) M), g • c = DM.classAct g c)
    (c : IdeleClassGroup (𝓞 F) F) :
    (jRep E F M D DM S ι hι hact hactM).hom (Additive.ofMul c) = Additive.ofMul (jHom F M c) := rfl

end Reps

end

end M4aHerbrand.TowerPkgProof
p2m_reactivate "P2MW.S_M4aHerbrand_exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower.M4aHerbrand P2MW.S_M4aHerbrand_exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower.M4aHerbrand.TowerPkgProof"
p2m_reactivate "P2MW.S_M4aHerbrand_exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower.M4aHerbrand"

open M4aHerbrand.TowerPkgProof M4aHerbrand.GenuineDescent in

theorem solution
    (E F M : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra E F] [Algebra E M] [Algebra F M] [IsScalarTower E F M] [IsGalois E F] [IsGalois E M]
    (D : IdeleGaloisDescent (𝓞 F) E F) (DM : IdeleGaloisDescent (𝓞 M) E M)

    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : (F ≃ₐ[E] F)) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    [MulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ]
    (hactIM : ∀ (g : (M ≃ₐ[E] M)) (x : (AdeleRing (𝓞 M) M)ˣ), g • x = DM.unitsAct g x)
    [MulDistribMulAction (M ≃ₐ[E] M) (IdeleClassGroup (𝓞 M) M)]
    (hactM : ∀ (g : (M ≃ₐ[E] M)) (c : IdeleClassGroup (𝓞 M) M), g • c = DM.classAct g c)

    (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (F ≃ₐ[E] F))
    (hι : ∀ (g : M ≃ₐ[E] M) (x : F), algebraMap F M (ι (QuotientGroup.mk g) x) = g (algebraMap F M x)) :
    ∃ (J : Rep.res (ι.toMonoidHom.comp (QuotientGroup.mk' S)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
          Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ)
      (j : Rep.res (ι.toMonoidHom.comp (QuotientGroup.mk' S)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) ⟶
          Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (IdeleClassGroup (𝓞 M) M)),

      (∀ x : (AdeleRing (𝓞 F) F)ˣ, J.hom (Additive.ofMul x) =
        Additive.ofMul (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange F M).β.toMonoidHom x)) ∧
      (∀ x : (AdeleRing (𝓞 F) F)ˣ, j.hom (Additive.ofMul (QuotientGroup.mk x : IdeleClassGroup (𝓞 F) F)) =
        Additive.ofMul (QuotientGroup.mk (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange F M).β.toMonoidHom x) : IdeleClassGroup (𝓞 M) M)) ∧

      Function.Injective j.hom ∧
      (∀ c : IdeleClassGroup (𝓞 M) M,
        Additive.ofMul c ∈ Set.range j.hom ↔ ∀ s : M ≃ₐ[E] M, s ∈ S → s • c = c) := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 F) E F
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 M) E M
  haveI : IsGalois F M := IsGalois.tower_top_of_isGalois E F M
  refine ⟨JRep E F M D DM S ι hι hactI hactIM, jRep E F M D DM S ι hι hact hactM, fun x => rfl, fun x => rfl, ?_, ?_⟩
  ·
    intro a b h
    change Additive.ofMul (jHom F M (Additive.toMul a)) = Additive.ofMul (jHom F M (Additive.toMul b)) at h
    exact Additive.toMul.injective (jHom_injective F M (Additive.ofMul.injective h))
  ·
    intro c
    constructor
    · rintro ⟨a, ha⟩ s hs
      change Additive.ofMul (jHom F M (Additive.toMul a)) = Additive.ofMul c at ha
      have hc : c = jHom F M (Additive.toMul a) := (Additive.ofMul.injective ha).symm
      obtain rfl : D = genuineDescentDatum E F := Subsingleton.elim _ _
      obtain rfl : DM = genuineDescentDatum E M := Subsingleton.elim _ _
      rw [hc, hactM, ← jHom_classAct E F M (ι (QuotientGroup.mk s)) s (hι s), ← hact,
        ι_mk_eq_one_of_mem S ι s hs, one_smul]
    · intro hfix
      induction c using QuotientGroup.induction_on with
      | H u =>
        have hu : ∀ τ : M ≃ₐ[F] M, (DM.unitsAct (resHom E F M τ) u)⁻¹ * u ∈ principalIdeles (𝓞 M) M := by
          intro τ
          have h := hfix (resHom E F M τ) (resHom_mem S ι hι τ)
          rw [hactM, classAct_mk] at h
          exact QuotientGroup.eq.mp h
        obtain ⟨c', hc'⟩ := mk_mem_range_jHom E F M DM u hu
        exact ⟨Additive.ofMul c', congrArg Additive.ofMul hc'⟩

end S_M4aHerbrand_exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower
end P2MW
export P2MW.S_M4aHerbrand_exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower (solution)
