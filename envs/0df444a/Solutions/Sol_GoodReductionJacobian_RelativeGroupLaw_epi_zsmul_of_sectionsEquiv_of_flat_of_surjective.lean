-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.epi_zsmul_of_sectionsEquiv_of_flat_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/f8222551-2fb8-5585-ab96-825e6cb416ce

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_epi_zsmul_of_sectionsEquiv_of_flat_of_surjective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open GoodReductionJacobian NeronModelInfra

universe u

namespace P3Fppf

example {R : Type u} [CommRing R] :
    (smallFppfTopology (Spec (CommRingCat.of R))).HasSheafCompose (forget Ab.{u + 1}) := inferInstance

theorem isLocallySurjective_zsmul
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f)
    (𝒢 : Sheaf (smallFppfTopology (Spec (CommRingCat.of R))) Ab.{u + 1})
    (e : ∀ U : (Spec (CommRingCat.of R)).Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom f)
    (he : ∀ {U V : (Spec (CommRingCat.of R)).Fppf} (k : U ⟶ V) (s : 𝒢.1.obj (op V)),
        e U (𝒢.1.map k.op s) = schemeHomOverComp k.left (MorphismProperty.Over.w k) (e V s))
    (n : ℕ)
    (hn : ∀ (U : (Spec (CommRingCat.of R)).Fppf) (s : 𝒢.1.obj (op U)),
        (e U (((n : ℤ) • 𝟙 𝒢 : 𝒢 ⟶ 𝒢).1.app (op U) s)).1 = (e U s).1 ≫ G.schemeNsmul n)
    [Flat (G.schemeNsmul n)] [Surjective (G.schemeNsmul n)] [LocallyOfFinitePresentation (G.schemeNsmul n)] :
    Sheaf.IsLocallySurjective ((n : ℤ) • 𝟙 𝒢 : 𝒢 ⟶ 𝒢) := by
  constructor
  intro U s

  let σ : U.left ⟶ A := (e U s).1
  have hσ : σ ≫ f = U.hom := (e U s).2
  let N : A ⟶ A := G.schemeNsmul n
  let p1 : pullback σ N ⟶ U.left := pullback.fst σ N
  let p2 : pullback σ N ⟶ A := pullback.snd σ N
  haveI : Flat p1 := MorphismProperty.pullback_fst (P := @Flat) _ _ ‹_›
  haveI : LocallyOfFinitePresentation p1 :=
    MorphismProperty.pullback_fst (P := @LocallyOfFinitePresentation) _ _ ‹_›
  haveI : Surjective p1 := MorphismProperty.pullback_fst (P := @Surjective) _ _ ‹_›
  have hV : fppfProperty (p1 ≫ U.hom) := fppfProperty.comp_mem _ _ ⟨‹_›, ‹_›⟩ U.prop
  let V : (Spec (CommRingCat.of R)).Fppf := MorphismProperty.Over.mk ⊤ (p1 ≫ U.hom) hV
  let g : V ⟶ U := MorphismProperty.Over.homMk p1 rfl trivial
  have hg : g.left = p1 := rfl

  have hp2 : p2 ≫ f = V.hom := by
    change p2 ≫ f = p1 ≫ U.hom
    rw [← G.schemeNsmul_over n, ← Category.assoc, ← hσ, Category.assoc]
    exact (pullback.condition_assoc (f := σ) (g := N) f).symm
  have himg : (Presheaf.imageSieve ((n : ℤ) • 𝟙 𝒢 : 𝒢 ⟶ 𝒢).1 s) g := by
    refine ⟨(e V).symm ⟨p2, hp2⟩, ?_⟩
    apply (e V).injective
    apply Subtype.ext
    rw [hn V, Equiv.apply_symm_apply, he g s, schemeHomOverComp_coe, hg]
    exact (pullback.condition (f := σ) (g := N)).symm

  refine (Functor.mem_restrictedTopology_iff (G := Scheme.Fppf.forget _)
    (K := fppfTopology.over _)).mpr ?_
  refine (GrothendieckTopology.mem_over_iff _ _).mpr ?_
  change Sieve.overEquiv ((Scheme.Fppf.forget _).obj U)
      ((Presheaf.imageSieve ((n : ℤ) • 𝟙 𝒢 : 𝒢 ⟶ 𝒢).1 s).functorPushforward
        (Scheme.Fppf.forget _)) ∈ Scheme.grothendieckTopology fppfProperty U.left
  refine GrothendieckTopology.superset_covering _ ?_
    (Precoverage.generate_mem_toGrothendieck (Scheme.Hom.singleton_mem_fppfPrecoverage p1))
  rw [Sieve.generate_le_iff]
  rintro Z h ⟨⟩
  rw [Sieve.overEquiv_iff]
  refine ⟨V, g, 𝟙 _, himg, ?_⟩
  apply Over.OverMorphism.ext
  exact (Category.id_comp p1).symm

end P3Fppf

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f)
    (𝒢 : Sheaf (smallFppfTopology (Spec (CommRingCat.of R))) Ab.{u + 1})
    (e : ∀ U : (Spec (CommRingCat.of R)).Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom f)
    (he : ∀ {U V : (Spec (CommRingCat.of R)).Fppf} (k : U ⟶ V) (s : 𝒢.1.obj (op V)),
        e U (𝒢.1.map k.op s) = schemeHomOverComp k.left (MorphismProperty.Over.w k) (e V s))
    (n : ℕ)
    (hn : ∀ (U : (Spec (CommRingCat.of R)).Fppf) (s : 𝒢.1.obj (op U)),
        (e U (((n : ℤ) • 𝟙 𝒢 : 𝒢 ⟶ 𝒢).1.app (op U) s)).1 = (e U s).1 ≫ G.schemeNsmul n)
    [Flat (G.schemeNsmul n)] [Surjective (G.schemeNsmul n)] [LocallyOfFinitePresentation (G.schemeNsmul n)] :
    Epi ((n : ℤ) • 𝟙 𝒢 : 𝒢 ⟶ 𝒢) := by
  haveI := P3Fppf.isLocallySurjective_zsmul G 𝒢 e he n hn
  infer_instance

end S_GoodReductionJacobian_RelativeGroupLaw_epi_zsmul_of_sectionsEquiv_of_flat_of_surjective
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_epi_zsmul_of_sectionsEquiv_of_flat_of_surjective (solution)
