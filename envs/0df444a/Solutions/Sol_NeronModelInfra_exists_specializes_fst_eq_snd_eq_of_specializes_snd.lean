-- Prove2me | solution 1 for NeronModelInfra.exists_specializes_fst_eq_snd_eq_of_specializes_snd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/02fe3407-4711-5090-bc07-b8295312740e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_specializes_fst_eq_snd_eq_of_specializes_snd

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

universe u

namespace P2mSliceGoingDown

theorem flat_SpecMap_of_field {k L : Type u} [Field k] [Field L] (φ : CommRingCat.of k ⟶ CommRingCat.of L) :
    Flat (Spec.map φ) := by
  rw [Flat.SpecMap_iff]
  letI := φ.hom.toAlgebra
  change Module.Flat k L
  infer_instance

theorem main
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (θ : ↑(pullback f f)) (hθ : f.base ((pullback.fst f f).base θ) = IsLocalRing.closedPoint R)
    (y : X) (hy : y ⤳ (pullback.snd f f).base θ) (hys : f.base y = IsLocalRing.closedPoint R) :
    ∃ θ' : ↑(pullback f f), θ' ⤳ θ ∧ (pullback.fst f f).base θ' = (pullback.fst f f).base θ ∧
      (pullback.snd f f).base θ' = y := by
  set a : X := (pullback.fst f f).base θ with ha
  set s : ↑(Spec (CommRingCat.of R)) := f.base a with hs

  let ιa : Spec (X.residueField a) ⟶ X := X.fromSpecResidueField a
  let ιs : Spec ((Spec (CommRingCat.of R)).residueField s) ⟶ Spec (CommRingCat.of R) :=
    (Spec (CommRingCat.of R)).fromSpecResidueField s
  let r := f.residueFieldMap a
  have hr : Spec.map r ≫ ιs = ιa ≫ f := f.SpecMap_residueFieldMap_fromSpecResidueField a
  haveI : Flat (Spec.map r) := flat_SpecMap_of_field r

  let jXs : pullback ιs f ⟶ X := pullback.snd ιs f
  let E := pullback (Spec.map r) (pullback.fst ιs f)
  let g₂ : E ⟶ pullback ιs f := pullback.snd (Spec.map r) (pullback.fst ιs f)
  haveI : Flat g₂ := inferInstance
  let iso : E ≅ pullback (Spec.map r ≫ ιs) f := pullbackRightPullbackFstIso ιs f (Spec.map r)
  let ψ₀ : pullback (Spec.map r ≫ ιs) f ⟶ pullback f f :=
    pullback.map (Spec.map r ≫ ιs) f f f ιa (𝟙 X) (𝟙 _) (by rw [hr, Category.comp_id])
      (by rw [Category.comp_id, Category.id_comp])
  let ψ : E ⟶ pullback f f := iso.hom ≫ ψ₀
  have hψsnd : ψ ≫ pullback.snd f f = g₂ ≫ jXs := by
    simp only [ψ, ψ₀, Category.assoc, pullback.lift_snd, Category.comp_id]
    exact pullbackRightPullbackFstIso_hom_snd ιs f (Spec.map r)
  have hψfst : ψ ≫ pullback.fst f f = (iso.hom ≫ pullback.fst _ _) ≫ ιa := by
    simp only [ψ, ψ₀, Category.assoc, pullback.lift_fst]
  have hrangeψ₀ : Set.range ψ₀.base = {q | (pullback.fst f f).base q = a} := by
    have h := Scheme.Pullback.range_map (Spec.map r ≫ ιs) f f f ιa (𝟙 X) (𝟙 _)
      (by rw [hr, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])
    rw [h]
    ext q
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, ιa, Scheme.range_fromSpecResidueField,
      Set.mem_singleton_iff]
    constructor
    · exact fun h => h.1
    · intro hq; exact ⟨hq, ⟨(pullback.snd f f).base q, by simp⟩⟩
  have hrangeψ : Set.range ψ.base = {q | (pullback.fst f f).base q = a} := by
    rw [← hrangeψ₀]
    change Set.range ((iso.hom ≫ ψ₀).base) = _
    have : Set.range ((iso.hom ≫ ψ₀).base) = ψ₀.base '' Set.range iso.hom.base := by
      rw [← Set.range_comp]; rfl
    rw [this, (show Function.Surjective iso.hom.base from (Scheme.homeoOfIso iso).surjective).range_eq,
      Set.image_univ]

  obtain ⟨θ₁, hθ₁⟩ : θ ∈ Set.range ψ.base := by rw [hrangeψ]; exact ha.symm

  have hrange_jXs : Set.range jXs.base = {x | f.base x = s} := by
    change Set.range (pullback.snd ιs f).base = _
    rw [Scheme.Pullback.range_snd]
    ext x
    simp only [ιs, Set.mem_preimage, Scheme.range_fromSpecResidueField, Set.mem_singleton_iff, Set.mem_setOf_eq]
  have hys' : f.base y = s := by rw [hys]; exact hθ.symm
  obtain ⟨y₁, rfl⟩ : y ∈ Set.range jXs.base := by rw [hrange_jXs]; exact hys'

  have hsndθ : (pullback.snd f f).base θ = jXs.base (g₂.base θ₁) := by
    rw [← hθ₁, ← Scheme.Hom.comp_apply, hψsnd, Scheme.Hom.comp_apply]
  have hy₁ : y₁ ⤳ g₂.base θ₁ := by
    rw [← jXs.isEmbedding.isInducing.specializes_iff, ← hsndθ]
    exact hy

  obtain ⟨ε, hεθ₁, hεy⟩ := Flat.generalizingMap g₂ hy₁
  refine ⟨ψ.base ε, ?_, ?_, ?_⟩
  · rw [← hθ₁]; exact hεθ₁.map ψ.continuous
  · have h1 : ψ.base ε ∈ Set.range ψ.base := ⟨ε, rfl⟩
    rw [hrangeψ] at h1
    exact h1
  · rw [← Scheme.Hom.comp_apply, hψsnd, Scheme.Hom.comp_apply, hεy]

end P2mSliceGoingDown

theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (θ : ↑(pullback f f)) (hθ : f.base ((pullback.fst f f).base θ) = IsLocalRing.closedPoint R)
    (y : X) (hy : y ⤳ (pullback.snd f f).base θ) (hys : f.base y = IsLocalRing.closedPoint R) :
    ∃ θ' : ↑(pullback f f), θ' ⤳ θ ∧ (pullback.fst f f).base θ' = (pullback.fst f f).base θ ∧
      (pullback.snd f f).base θ' = y :=
  P2mSliceGoingDown.main f θ hθ y hy hys

end
end S_NeronModelInfra_exists_specializes_fst_eq_snd_eq_of_specializes_snd
end P2MW
export P2MW.S_NeronModelInfra_exists_specializes_fst_eq_snd_eq_of_specializes_snd (solution)
