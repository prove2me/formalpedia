-- Prove2me | solution 1 for OAI.MaximalSeshadri.Projective.sectionIdeal_dimension_le_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:19:59.053058+00:00
-- url     : https://prove2.me/submissions/95e05c58-e4e9-466a-bcee-c42f7c3ea541
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6
import Theorems.Thm_OAI_MaximalSeshadri_ProjectiveBertini_exists_etale_projective_chart
import Theorems.Thm_OAI_MaximalSeshadri_Projective_sectionIdeal_on_any_frame

set_option Elab.async false
set_option linter.all false

section
namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y Z : Scheme.{u}}

end
end MaximalSeshadri.Frames

namespace MaximalSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}}

lemma endValue_injective : Function.Injective (endValue (X := X)) := by
  intro f g h
  ext U a
  change Γ(X, U) at a
  change f.app U a = g.app U a
  rw [end_apply f U a, end_apply g U a]
  rw [end_naturality f U, end_naturality g U, h]

end
end MaximalSeshadri.Frames

end
end
end

end OAI
end

section
namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.EtaleDimension
noncomputable section
open IsLocalRing

lemma local_unramified_dimension_le (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  have hm := Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S)
  have h := Ideal.height_le_height_add_of_liesOver (maximalIdeal R) (maximalIdeal S)
  rw [hm, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at h
  have H : ((maximalIdeal S).height : WithBot ℕ∞) ≤ (maximalIdeal R).height := by exact_mod_cast h
  simpa only [maximalIdeal_height_eq_ringKrullDim] using H

lemma etale_dimension_le (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  apply (ringKrullDim_le_iff_height_le _).mpr
  intro q hq
  let := hq
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  let : Algebra.EssFiniteType Rp Sq := Algebra.EssFiniteType.of_comp R Rp Sq
  let : Algebra.FormallyUnramified R Sq := Algebra.FormallyUnramified.comp R S Sq
  let : Algebra.FormallyUnramified Rp Sq := Algebra.FormallyUnramified.of_restrictScalars R Rp Sq
  have H := local_unramified_dimension_le Rp Sq
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p Rp,
    IsLocalization.AtPrime.ringKrullDim_eq_height q Sq] at H
  exact H.trans ((ringKrullDim_le_iff_height_le _).mp le_rfl inferInstance)

lemma etale_polynomial_dimension_le (K S ι : Type*) [Field K] [CommRing S] [Finite ι]
    [Algebra (MvPolynomial ι K) S] [Algebra.Etale (MvPolynomial ι K) S] :
    ringKrullDim S ≤ (Nat.card ι : WithBot ℕ∞) := by
  let := Fintype.ofFinite ι
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing (MvPolynomial ι K) S
  have h := etale_dimension_le (MvPolynomial ι K) S
  simpa only [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    zero_add, ENat.card_eq_coe_fintype_card, Nat.card_eq_fintype_card, WithBot.coe_natCast] using h

end
end MaximalSeshadri.EtaleDimension
end

end
end

end OAI
end

section
namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry TopologicalSpace Order

lemma scheme_dimension_eq_point_dimension (X : Scheme) :
    topologicalKrullDim X = Order.krullDim X :=
  Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))

lemma scheme_dimension_le_of_neighborhoods (X : Scheme) (d : WithBot ℕ∞)
    (h : ∀ x : X, ∃ (U : Scheme) (f : U ⟶ X), IsOpenImmersion f ∧
      x ∈ Set.range f ∧ topologicalKrullDim U ≤ d) : topologicalKrullDim X ≤ d := by
  rw [scheme_dimension_eq_point_dimension, Order.krullDim_eq_iSup_coheight]
  apply iSup_le
  intro x
  obtain ⟨U,f,hf,⟨y,rfl⟩,hd⟩ := h x
  let := hf
  rw [AlgebraicGeometry.coheight_eq_of_isOpenImmersion]
  exact (Order.coheight_le_krullDim y).trans ((scheme_dimension_eq_point_dimension U) ▸ hd)

lemma subscheme_dimension_le_of_affine_neighborhoods {X : Scheme}
    (I : X.IdealSheafData) (d : WithBot ℕ∞)
    (h : ∀ x : I.subscheme, ∃ U : X.affineOpens, I.subschemeι x ∈ U.1 ∧
      ringKrullDim (Γ(X,U.1) ⧸ I.ideal U) ≤ d) :
    topologicalKrullDim I.subscheme ≤ d := by
  apply scheme_dimension_le_of_neighborhoods
  intro x
  obtain ⟨U,hx,hd⟩ := h x
  let := I.subschemeCover.map_prop U
  refine ⟨_, I.subschemeCover.f U,inferInstance,?_,?_⟩
  · change x ∈ (I.subschemeCover.f U).opensRange
    rw [I.opensRange_subschemeCover_map]
    exact hx
  · exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).le.trans hd

end
end MaximalSeshadri.Geometry
end

end
end

end OAI
end

section
namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Frames
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma coefficient_injective {M : X.Modules} (e : M ≅ O X) :
    Function.Injective (coefficient e) := by
  intro s t h
  apply (cancel_mono e.hom).1
  exact endValue_injective h

end
end MaximalSeshadri.Frames

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

end
end MaximalSeshadri.Geometry

end
end
end

end OAI
end

section
namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}}

lemma coefficient_zero {M : X.Modules} (e : M ≅ O X) :
    coefficient e (0 : O X ⟶ M) = 0 := by
  simp [coefficient, endValue]
  rfl

lemma restrictSection_zero (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules} :
    restrictSection φ (0 : O X ⟶ M) = 0 := by
  ext U value
  rfl

end
end MaximalSeshadri.Frames
end

end
end

end OAI
end

section
namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Frames
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped AlgebraicGeometry
variable {X : Scheme}

end
end MaximalSeshadri.Frames

namespace MaximalSeshadri.Frames
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X : Scheme}

end
end MaximalSeshadri.Frames

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

variable {X : Scheme}

lemma trivialModule_restriction_injective [IsIntegral X] (M : X.Modules)
    (e : M ≅ structureSheaf X) {U V : X.Opens} (i : U ⟶ V) [Nonempty U] :
    Function.Injective (M.presheaf.map i.op) := by
  intro s t h
  apply (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.toPresheaf X).mapIso e).app (Opposite.op V)).hom).injective
  have hn := e.hom.mapPresheaf.naturality i.op
  have heq := congrArg (fun a => e.hom.app U a) h
  have hh (a : Γ(M, V)) :
      e.hom.app U (M.presheaf.map i.op a) =
        X.presheaf.map i.op (e.hom.app V a) := by
    exact CategoryTheory.congr_fun hn a
  rw [hh, hh] at heq
  exact map_injective_of_isIntegral X i heq

theorem LineBundle.restriction_injective [IsIntegral X] (L : LineBundle X)
    {U V : X.Opens} (i : U ⟶ V) [Nonempty U] :
    Function.Injective (L.sheaf.presheaf.map i.op) := by
  intro s t h
  apply L.sheaf.isSheaf.section_ext
  intro x hx
  obtain ⟨T, hxT, ⟨e⟩⟩ := L.locallyRankOne x
  let f := T.ι
  let U' : T.toScheme.Opens := f ⁻¹ᵁ U
  let V' : T.toScheme.Opens := f ⁻¹ᵁ V
  have hU' : Nonempty U' := by
    obtain ⟨y, hyT, hyU⟩ := nonempty_preirreducible_inter T.isOpen U.isOpen
      ⟨x, hxT⟩ (by obtain ⟨u⟩ := ‹Nonempty U›; exact ⟨u.val, u.property⟩)
    exact ⟨⟨⟨y, hyT⟩, hyU⟩⟩
  have : Nonempty U' := hU'
  have : Nonempty T := ⟨⟨x, hxT⟩⟩
  let j : U' ⟶ V' := homOfLE (fun _ h => leOfHom i h)
  let W := f ''ᵁ V'
  have hWV : W ≤ V := f.image_preimage_le V
  refine ⟨W, hWV, ?_, ?_⟩
  · exact ⟨⟨x, hxT⟩, hx, rfl⟩
  · apply trivialModule_restriction_injective (L.sheaf.restrict f) e j
    change L.sheaf.presheaf.map ((f.opensFunctor.map j).op)
        (L.sheaf.presheaf.map (homOfLE hWV).op s) =
      L.sheaf.presheaf.map ((f.opensFunctor.map j).op)
        (L.sheaf.presheaf.map (homOfLE hWV).op t)
    have hh := congrArg
      (fun a => L.sheaf.presheaf.map (homOfLE (f.image_preimage_le U)).op a) h
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hh ⊢
    have eq : i.op ≫ (homOfLE (f.image_preimage_le U)).op =
        (homOfLE hWV).op ≫ (f.opensFunctor.map j).op := Subsingleton.elim _ _
    rw [eq] at hh
    exact hh

theorem LineBundle.section_restriction_injective [IsIntegral X] (L : LineBundle X)
    (U : X.Opens) [Nonempty U] :
    Function.Injective (fun s : GlobalSections X L.sheaf => s.app U (1 : Γ(X, U))) := by
  intro s t h
  have natural (s : GlobalSections X L.sheaf) (V : X.Opens) :
      s.app V (1 : Γ(X, V)) = L.sheaf.presheaf.map
        (homOfLE (show V ≤ ⊤ from le_top)).op (s.app ⊤ (1 : Γ(X, ⊤))) := by
    have hs := CategoryTheory.congr_fun (s.mapPresheaf.naturality
      (homOfLE (show V ≤ ⊤ from le_top)).op) (1 : Γ(X, ⊤))
    change s.app V (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op 1) =
      L.sheaf.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (s.app ⊤ (1 : Γ(X, ⊤))) at hs
    simpa only [map_one, ConcreteCategory.comp_apply] using hs
  have ht : s.app ⊤ (1 : Γ(X, ⊤)) = t.app ⊤ (1 : Γ(X, ⊤)) := by
    apply L.restriction_injective (homOfLE (show U ≤ ⊤ from le_top))
    rw [← natural s U, ← natural t U]
    exact h
  ext V a
  change Γ(X, V) at a
  have hv : s.app V (1 : Γ(X, V)) = t.app V (1 : Γ(X, V)) := by
    rw [natural s, natural t, ht]
  have scalar (s : GlobalSections X L.sheaf) :
      s.app V a = a • s.app V (1 : Γ(X, V)) := by
    have hs := s.app_smul (r := a) (x := (1 : Γ(X, V)))
    change s.app V (a * 1 : Γ(X, V)) = _ at hs
    simpa only [mul_one] using hs
  rw [scalar s, scalar t, hv]

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
variable {X : Scheme}

end
end MaximalSeshadri.Geometry

end
end
end

end OAI
end

section
namespace OAI

section
noncomputable section

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme} {σ : Type}

lemma projective_standard_cover :
    (⨆ i : σ, Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i)) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  change p ∈ idealOfVars σ K
  rw [← pow_one (idealOfVars σ K), mem_pow_idealOfVars_iff]
  intro d hd
  change 1 ≤ d.sum fun _ v => v
  rw [Finsupp.sum, ← hp.degree_eq_sum_deg_support hd]
  exact hn

 theorem exists_etale_projective_neighborhood [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (h : X ⟶ Proj (PolyGrade K σ)) [IsClosedImmersion h]
    (hbase : h ≫ projectiveToSpec = g)
    (W : X.Opens) (x : X) (hxW : x ∈ W) :
    ∃ C : EtaleProjectiveChart g h, x ∈ C.U.1 ∧ C.U.1 ≤ W := by
  have hx : h x ∈ ⨆ i : σ, Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i) := by
    rw [projective_standard_cover]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  obtain ⟨C, hxC, hCW, _⟩ := exists_etale_projective_chart g h hbase i W x hxW hi
  exact ⟨C, hxC, hCW⟩

end

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.BertiniIntegral
attribute [local instance] MvPolynomial.gradedAlgebra

end
end MaximalSeshadri.ProjectiveBertini

noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂

end
end
end

end OAI
end

section
namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames
variable {X Y : Scheme}

lemma LineBundle.restrict_sections_injective [IsIntegral X] (L : LineBundle X)
    (f : Y ⟶ X) [IsOpenImmersion f] [Nonempty Y] :
    Function.Injective (fun s : GlobalSections X L.sheaf =>
      (Scheme.Modules.restrictFunctor f).map s) := by
  intro s t h
  let U : X.Opens := f ''ᵁ ⊤
  have : Nonempty U := by
    obtain ⟨y⟩ := ‹Nonempty Y›
    exact ⟨⟨f y, y, Set.mem_univ y, rfl⟩⟩
  apply L.section_restriction_injective U
  have he := congrArg (fun s : (structureSheaf X).restrict f ⟶ L.sheaf.restrict f =>
    s.app ⊤ (1 : Γ(X, U))) h
  exact he

lemma LineBundle.restricted_coefficient_injective [IsIntegral X] (L : LineBundle X)
    (f : Y ⟶ X) [IsOpenImmersion f] [Nonempty Y]
    (e : L.sheaf.restrict f ≅ O Y) :
    Function.Injective (fun s : GlobalSections X L.sheaf => coefficient e (restrictSection f s)) := by
  intro s t h
  apply L.restrict_sections_injective f
  let u : (structureSheaf X).restrict f ≅ structureSheaf Y :=
    Scheme.Modules.restrictUnitIso f
  apply (cancel_epi u.inv).mp
  exact coefficient_injective e h

lemma LineBundle.section_coefficient_regular [IsIntegral X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0)
    (U : X.affineOpens) [Nonempty U.1]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    IsRegular (U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))) := by
  apply isRegular_iff_ne_zero.mpr
  intro h
  apply hs
  apply L.restricted_coefficient_injective U.1.ι e
  have he := (ConcreteCategory.bijective_of_isIso U.1.topIso.hom).injective
  apply he
  change U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)) =
    U.1.topIso.hom (coefficient e (restrictSection U.1.ι (0 : O X ⟶ L.sheaf)))
  exact h.trans (by rw [restrictSection_zero, coefficient_zero, map_zero])
end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Geometry
variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme}

end
end MaximalSeshadri.Projective
end

section

end

end
end

end OAI
end

section
namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.ProjectiveBertini MaximalSeshadri.Frames

attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ τ : Type} [Field K] [Fintype σ] {X : Scheme}

lemma EtaleProjectiveChart.dimension_le [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) (h : X ⟶ Proj (PolyGrade K τ))
    (C : EtaleProjectiveChart g h) : ringKrullDim Γ(X,C.U.1) ≤ 2 := by
  let := C.finite
  let φ := MvPolynomial.eval₂Hom (openScalars g C.U.1)
    (fun k => -C.φ (chartCoordinate C.coord (C.a k).1))
  let : Algebra (MvPolynomial C.κ K) Γ(X,C.U.1) := φ.toAlgebra
  let : Algebra.Etale (MvPolynomial C.κ K) Γ(X,C.U.1) := C.etale
  have H := MaximalSeshadri.EtaleDimension.etale_polynomial_dimension_le K Γ(X,C.U.1) C.κ
  simpa only [C.card, Nat.cast_ofNat] using H

theorem sectionIdeal_dimension_le_one [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (h : X ⟶ Proj (PolyGrade K τ)) [IsClosedImmersion h]
    (hbase : h ≫ projectiveToSpec = g)
    (L : LineBundle X) (k : K →+* Γ(X,⊤)) (s : σ → (O X ⟶ L.sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → K)
    (hv : sectionCombination k s v ≠ 0) :
    topologicalKrullDim (sectionIdeal k s hs v).subscheme ≤ 1 := by
  apply subscheme_dimension_le_of_affine_neighborhoods
  intro x
  let y := (sectionIdeal k s hs v).subschemeι x
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (hs.ge (show y ∈ (⊤ : X.Opens) from trivial))
  obtain ⟨C,hy,hU⟩ := exists_etale_projective_neighborhood g h hbase
    (SectionOpens.isoOpen (s i)) y hi
  let := C.nonempty
  let e := sectionFrameOn (s i) C.U.1 hU
  let f := C.U.1.topIso.hom (coefficient e
    (restrictSection C.U.1.ι (sectionCombination k s v)))
  have hf : f ≠ 0 := (isRegular_iff_ne_zero).mp (L.section_coefficient_regular _ hv C.U e)
  refine ⟨C.U,hy,?_⟩
  rw [sectionIdeal_on_any_frame k s hs v C.U e]
  apply ENat.WithBot.add_le_add_one_right_iff.mp
  have H := (ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (mem_nonZeroDivisors_iff_ne_zero.mpr hf)).trans (EtaleProjectiveChart.dimension_le g h C)
  exact H

end
end MaximalSeshadri.Projective
end

end
end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Projective.sectionIdeal_dimension_le_one := @OAI.MaximalSeshadri.Projective.sectionIdeal_dimension_le_one
