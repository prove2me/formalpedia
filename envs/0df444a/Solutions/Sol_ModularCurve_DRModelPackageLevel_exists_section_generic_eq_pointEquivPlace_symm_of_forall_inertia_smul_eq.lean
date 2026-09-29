-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.exists_section_generic_eq_pointEquivPlace_symm_of_forall_inertia_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/e2eb5562-77c4-58d8-b674-74fd543b3af8

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_exists_section_generic_eq_pointEquivPlace_symm_of_forall_inertia_smul_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve
open IsLocalRing

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

private theorem descent_fixedField
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (Γ : Subgroup (Ω ≃ₐ[k] Ω))
    {X : Scheme.{0}} (P : Spec (CommRingCat.of Ω) ⟶ X)
    (hP : ∀ g ∈ Γ, Spec.map (CommRingCat.ofHom (g : Ω →+* Ω)) ≫ P = P) :
    ∃ P₁ : Spec (CommRingCat.of ↥(IntermediateField.fixedField Γ)) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap ↥(IntermediateField.fixedField Γ) Ω)) ≫ P₁ = P := by
  classical

  set x₀ : ↥X := P.base (IsLocalRing.closedPoint Ω) with hx₀
  obtain ⟨_, ⟨U', hU', rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x₀) isOpen_univ
  set U : X.Opens := U' with hUdef
  have hU : IsAffineOpen U := hU'

  have hrange : Set.range P.base ⊆ Set.range U.ι.base := by
    rintro _ ⟨z, rfl⟩
    obtain rfl : z = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
    rw [Scheme.Opens.range_ι]
    exact hxU
  set Q : Spec (CommRingCat.of Ω) ⟶ ↑U := IsOpenImmersion.lift U.ι P hrange with hQ
  have hQfac : Q ≫ U.ι = P := IsOpenImmersion.lift_fac U.ι P hrange

  set φ : Γ(X, U) ⟶ CommRingCat.of Ω := Spec.preimage (Q ≫ hU.isoSpec.hom) with hφ
  have hφQ : Spec.map φ = Q ≫ hU.isoSpec.hom := Spec.map_preimage _
  have hφP : Spec.map φ ≫ hU.isoSpec.inv ≫ U.ι = P := by
    rw [hφQ, Category.assoc, Iso.hom_inv_id_assoc, hQfac]

  have hφinv : ∀ g ∈ Γ, φ ≫ CommRingCat.ofHom (g : Ω →+* Ω) = φ := by
    intro g hg
    apply Spec.map_injective
    rw [Spec.map_comp]

    have hmono : Mono (hU.isoSpec.inv ≫ U.ι) := inferInstance
    rw [← cancel_mono (hU.isoSpec.inv ≫ U.ι), Category.assoc, hφP]
    exact hP g hg
  have hmem : ∀ r : Γ(X, U), φ.hom r ∈ IntermediateField.fixedField Γ := by
    intro r
    rw [IntermediateField.mem_fixedField_iff]
    intro g hg
    have := congrArg (fun ψ => ψ.hom r) (hφinv g hg)
    simpa using this

  let φ₁ : Γ(X, U) →+* ↥(IntermediateField.fixedField Γ) :=
    { toFun := fun r => ⟨φ.hom r, hmem r⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hφ₁ : (algebraMap ↥(IntermediateField.fixedField Γ) Ω).comp φ₁ = φ.hom := RingHom.ext fun r => rfl
  refine ⟨Spec.map (CommRingCat.ofHom φ₁) ≫ hU.isoSpec.inv ≫ U.ι, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ₁, CommRingCat.ofHom_hom]
  exact hφP

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    {A : ValuationSubring (AlgebraicClosure ℚ)}

    (O : Type) [CommRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (ρO : DRLevel.R q →+* O)
    (hρO : ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
        (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))).comp ρO =
      algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))

    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * q)))
    (hV : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N₀ * q)) σ • V = V) :
    ∃ s : Spec (CommRingCat.of O) ⟶ pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)),
      s ≫ pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
          (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ s ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) =
        ((𝔓.Meta.pointEquivPlace).symm (V)).1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ q) _ := by
  classical

  set x := (𝔓.Meta.pointEquivPlace).symm V with hxdef
  have hxV : 𝔓.Meta.pointEquivPlace x = V := by rw [hxdef, Equiv.apply_symm_apply]
  let Kf := ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))
  let R' : ValuationSubring Kf := A.comap (algebraMap Kf (AlgebraicClosure ℚ))
  let jO : O →+* Kf := R'.subtype.comp eO.toRingHom

  have halgR : ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp (algebraMap (DRLevel.R q) (AlgebraicClosure ℚ)) =
        algebraMap (DRLevel.R q) (AlgebraicClosure ℚ) := by
    intro g
    ext r
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
    rw [IsScalarTower.algebraMap_apply (DRLevel.R q) ℚ (AlgebraicClosure ℚ)]
    exact g.commutes _

  have hPbase : (x.1 ≫ 𝔓.eeta ≫ pullback.fst (DRLevel.toBase N₀ q) _) ≫ DRLevel.toBase N₀ q =
      Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))) := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc 𝔓.eeta, 𝔓.heeta, ← Category.assoc, x.2,
      Category.id_comp]

  have hinv : ∀ g ∈ A.inertiaSubgroupIn ℚ,
      Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ x.1 ≫ 𝔓.eeta ≫ pullback.fst _ _ =
        x.1 ≫ 𝔓.eeta ≫ pullback.fst _ _ := by
    intro g hg
    haveI := 𝔓.eeta_iso
    have hw : (Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ x.1 ≫ 𝔓.eeta ≫
        pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))))) ≫ DRLevel.toBase N₀ q =
        𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))) := by
      rw [Category.assoc, hPbase, Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, halgR g]
    let x'' := pullback.lift _ _ hw
    have hx''snd : x'' ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have hx''fst : x'' ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ x.1 ≫ 𝔓.eeta ≫ pullback.fst _ _ :=
      pullback.lift_fst _ _ _
    let x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // s ≫ 𝔓.Meta.toBase = 𝟙 _} :=
      ⟨x'' ≫ inv 𝔓.eeta, by rw [← 𝔓.heeta, Category.assoc, IsIso.inv_hom_id_assoc, hx''snd]⟩
    have hx' : x'.1 ≫ 𝔓.eeta ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ x.1 ≫ 𝔓.eeta ≫ pullback.fst _ _ := by
      show (x'' ≫ inv 𝔓.eeta) ≫ 𝔓.eeta ≫ pullback.fst _ _ = _
      rw [Category.assoc, IsIso.inv_hom_id_assoc, hx''fst]
    have hgal := 𝔓.hgal g x x' hx'
    rw [hxV, hV g hg, ← hxV] at hgal
    have hxx : x' = x := 𝔓.Meta.pointEquivPlace.injective hgal
    rw [← hx', hxx]

  obtain ⟨P₁, hP₁⟩ := descent_fixedField (A.inertiaSubgroupIn ℚ) (x.1 ≫ 𝔓.eeta ≫ pullback.fst _ _) (fun g hg => by
      simpa only [Category.assoc] using hinv g hg)

  have hwC : P₁ ≫ DRLevel.toBase N₀ q = Spec.map (CommRingCat.ofHom jO) ≫ Spec.map (CommRingCat.ofHom ρO) := by

    obtain ⟨φ, hφ⟩ : ∃ φ, P₁ ≫ DRLevel.toBase N₀ q = Spec.map φ := ⟨Spec.preimage _, (Spec.map_preimage _).symm⟩
    have hR : (CommRingCat.ofHom ρO ≫ CommRingCat.ofHom jO) ≫ CommRingCat.ofHom (algebraMap Kf (AlgebraicClosure ℚ)) =
        CommRingCat.ofHom (algebraMap (DRLevel.R q) (AlgebraicClosure ℚ)) := by
      rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← hρO]
    have h1 : Spec.map (φ ≫ CommRingCat.ofHom (algebraMap Kf (AlgebraicClosure ℚ))) =
        Spec.map ((CommRingCat.ofHom ρO ≫ CommRingCat.ofHom jO) ≫ CommRingCat.ofHom (algebraMap Kf (AlgebraicClosure ℚ))) := by
      rw [hR, Spec.map_comp, ← hφ, ← Category.assoc, hP₁, hPbase]
    have h2 := Spec.map_injective h1
    rw [hφ, ← Spec.map_comp]
    congr 1
    ext r
    have := congrArg (fun t : CommRingCat.of (DRLevel.R q) ⟶ CommRingCat.of (AlgebraicClosure ℚ) => t.hom r) h2
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at this ⊢
    first
      | exact this
      | exact_mod_cast this
      | exact congrArg Subtype.val ((algebraMap Kf (AlgebraicClosure ℚ)).injective this)
      | (apply (algebraMap Kf (AlgebraicClosure ℚ)).injective; simpa using this)
  let y₀ := pullback.lift _ _ hwC
  have hy₀fst : y₀ ≫ pullback.fst _ _ = P₁ := pullback.lift_fst _ _ _
  have hy₀snd : y₀ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom jO) := pullback.lift_snd _ _ _

  haveI := 𝔓.isProper
  haveI : IsProper (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) := inferInstance
  have hex : ValuativeCriterion.Existence (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) :=
    (IsProper.eq_valuativeCriterion ▸
      (inferInstance : IsProper (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))))).1.1.1.existence
  have hsq : CommSq y₀ (Spec.map (CommRingCat.ofHom (algebraMap R' Kf)))
      (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) (Spec.map (CommRingCat.ofHom eO.toRingHom)) := by
    constructor
    rw [hy₀snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let S : ValuativeCommSq (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))) :=
    { R := R', K := Kf, i₁ := y₀, i₂ := Spec.map (CommRingCat.ofHom eO.toRingHom), commSq := hsq }
  haveI : S.commSq.HasLift := hex S
  let ℓ := S.commSq.lift
  have hℓ₁ : Spec.map (CommRingCat.ofHom (algebraMap R' Kf)) ≫ ℓ = y₀ := S.commSq.fac_left
  have hℓ₂ : ℓ ≫ pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) =
      Spec.map (CommRingCat.ofHom eO.toRingHom) := S.commSq.fac_right

  refine ⟨Spec.map (CommRingCat.ofHom eO.symm.toRingHom) ≫ ℓ, ?_, ?_⟩
  · rw [Category.assoc, hℓ₂, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : eO.symm.toRingHom.comp eO.toRingHom = RingHom.id O := by
      ext a; simp
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
  · show Spec.map (CommRingCat.ofHom ((algebraMap Kf (AlgebraicClosure ℚ)).comp jO)) ≫
        (Spec.map (CommRingCat.ofHom eO.symm.toRingHom) ≫ ℓ) ≫ pullback.fst _ _ = x.1 ≫ 𝔓.eeta ≫ pullback.fst _ _
    have h1 : Spec.map (CommRingCat.ofHom ((algebraMap Kf (AlgebraicClosure ℚ)).comp jO)) ≫
        Spec.map (CommRingCat.ofHom eO.symm.toRingHom) =
        Spec.map (CommRingCat.ofHom (algebraMap Kf (AlgebraicClosure ℚ))) ≫ Spec.map (CommRingCat.ofHom (algebraMap R' Kf)) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext r
      simp [jO]
    rw [Category.assoc, ← Category.assoc (Spec.map _) (Spec.map _), h1, Category.assoc,
      ← Category.assoc (Spec.map (CommRingCat.ofHom (algebraMap (↥R') Kf))), hℓ₁, hy₀fst, hP₁]

end S_ModularCurve_DRModelPackageLevel_exists_section_generic_eq_pointEquivPlace_symm_of_forall_inertia_smul_eq
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_exists_section_generic_eq_pointEquivPlace_symm_of_forall_inertia_smul_eq (solution)
