-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.isClosed_setOf_forall_comp_eq_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/dfb77b2a-d3ed-532a-a29e-09714239f04f

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_isClosed_setOf_forall_comp_eq_comp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace P2mWs30ClosedLocus

theorem epi_specMap_of_field {K L : Type} [Field K] [Field L] (φ : K →+* L) :
    Epi (Spec.map (CommRingCat.ofHom φ)) := by
  letI : Algebra K L := φ.toAlgebra
  haveI : Flat (Spec.map (CommRingCat.ofHom φ)) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  haveI : Surjective (Spec.map (CommRingCat.ofHom φ)) :=
    ⟨fun x => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_geometric_point {X : Scheme.{0}} (a : X) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : Spec (CommRingCat.of K) ⟶ X),
      x.base (IsLocalRing.closedPoint K) = a := by
  let k := X.residueField a
  let K := AlgebraicClosure k
  refine ⟨K, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ X.fromSpecResidueField a, ?_⟩
  exact X.fromSpecResidueField_apply a _

theorem comp_eq_iff_of_field {X Y : Scheme.{0}} (τ σ : X ⟶ Y) {K : Type} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ X) :
    x ≫ τ = x ≫ σ ↔
      X.fromSpecResidueField (x.base (IsLocalRing.closedPoint K)) ≫ τ =
        X.fromSpecResidueField (x.base (IsLocalRing.closedPoint K)) ≫ σ := by
  have hx := X.descResidueField_stalkClosedPointTo_fromSpecResidueField K x
  constructor
  · intro h
    haveI := epi_specMap_of_field (Scheme.descResidueField (Scheme.stalkClosedPointTo x)).hom
    rw [← cancel_epi (Spec.map (CommRingCat.ofHom (Scheme.descResidueField (Scheme.stalkClosedPointTo x)).hom)),
      CommRingCat.ofHom_hom, ← Category.assoc, ← Category.assoc, hx]
    exact h
  · intro h
    rw [← hx, Category.assoc, Category.assoc, h]

end P2mWs30ClosedLocus

open P2mWs30ClosedLocus in
theorem solution
    {S : Type} [CommRing S] {A Y : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (hA : AbelianSchemePropertyBundle S f)
    (g : Y ⟶ Spec (CommRingCat.of S)) [IsSeparated g] (τ : A ⟶ Y) (hτ : τ ≫ g = f)
    (c : Spec (CommRingCat.of S) ⟶ Y) (hc : c ≫ g = 𝟙 _) :
    IsClosed {s : ↥(Spec (CommRingCat.of S)) |
      ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ A),
        f.base (x.base (IsLocalRing.closedPoint K)) = s → x ≫ τ = x ≫ f ≫ c} := by
  classical
  haveI := hA.smooth

  let B := Spec (CommRingCat.of S)
  let X' : Over B := Over.mk f
  let Y' : Over B := Over.mk g
  let τ' : X' ⟶ Y' := Over.homMk τ hτ
  let σ' : X' ⟶ Y' := Over.homMk (f ≫ c) (by show f ≫ c ≫ g = f; rw [hc, Category.comp_id])
  haveI : IsSeparated Y'.hom := ‹IsSeparated g›
  let ι : (equalizer τ' σ').left ⟶ A := (equalizer.ι τ' σ').left
  haveI : IsClosedImmersion ι := isClosedImmersion_equalizer_ι_left τ' σ'
  let E : Set A := Set.range ι.base
  have hE : IsClosed E := ι.isClosedEmbedding.isClosed_range
  have hιc : ι ≫ τ = ι ≫ f ≫ c := by
    have := equalizer.condition τ' σ'
    have h2 := congrArg CommaMorphism.left this
    simp only [Over.comp_left] at h2
    exact h2

  let P : A → Prop := fun a => A.fromSpecResidueField a ≫ τ = A.fromSpecResidueField a ≫ f ≫ c
  have L1 : ∀ a, P a → a ∈ E := by
    intro a ha
    let W' : Over B := Over.mk (A.fromSpecResidueField a ≫ f)
    let k : W' ⟶ X' := Over.homMk (A.fromSpecResidueField a) rfl
    have hk : k ≫ τ' = k ≫ σ' := by
      ext
      simp only [Over.comp_left, Over.homMk_left, k, τ', σ']
      exact ha
    let l := equalizer.lift k hk
    have hl : l.left ≫ ι = A.fromSpecResidueField a := by
      have := equalizer.lift_ι k hk
      have h2 := congrArg CommaMorphism.left this
      simp only [Over.comp_left] at h2
      exact h2
    refine ⟨l.left.base (IsLocalRing.closedPoint _), ?_⟩
    change (l.left ≫ ι).base _ = a
    rw [hl]
    exact A.fromSpecResidueField_apply a _
  have L2 : ∀ a, a ∈ E → P a := by
    rintro _ ⟨b, rfl⟩
    have nat := ι.SpecMap_residueFieldMap_fromSpecResidueField b
    haveI := epi_specMap_of_field (ι.residueFieldMap b).hom
    show A.fromSpecResidueField (ι.base b) ≫ τ = A.fromSpecResidueField (ι.base b) ≫ f ≫ c
    rw [← cancel_epi (Spec.map (CommRingCat.ofHom (ι.residueFieldMap b).hom)), CommRingCat.ofHom_hom,
      ← Category.assoc, nat, ← Category.assoc (Spec.map _), nat, Category.assoc, Category.assoc, hιc]

  have hZ : {s : ↥(Spec (CommRingCat.of S)) |
      ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ A),
        f.base (x.base (IsLocalRing.closedPoint K)) = s → x ≫ τ = x ≫ f ≫ c} = (f.base '' Eᶜ)ᶜ := by
    ext s
    constructor
    · intro hs
      rintro ⟨a, haE, rfl⟩
      apply haE
      obtain ⟨K, _, _, x, hx⟩ := exists_geometric_point a
      have hconst := hs K x (by rw [hx])
      apply L1
      have := (comp_eq_iff_of_field τ (f ≫ c) x).mp hconst
      rwa [hx] at this
    · intro hs K _ _ x hx
      have haE : x.base (IsLocalRing.closedPoint K) ∈ E := by
        by_contra h
        exact hs ⟨_, h, hx⟩
      exact (comp_eq_iff_of_field τ (f ≫ c) x).mpr (L2 _ haE)
  rw [hZ]
  exact (f.isOpenMap _ hE.isOpen_compl).isClosed_compl

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_isClosed_setOf_forall_comp_eq_comp
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_isClosed_setOf_forall_comp_eq_comp (solution)
