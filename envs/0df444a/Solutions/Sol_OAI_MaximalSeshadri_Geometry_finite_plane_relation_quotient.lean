-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.finite_plane_relation_quotient
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:23:41.404328+00:00
-- url     : https://prove2.me/submissions/ea9aaf86-cdae-4410-a126-ca286fcc107a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6
import Theorems.Thm_OAI_MaximalSeshadri_Projective_finite_plane_H1
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_BaseSections_plane_boundaries_lift

set_option Elab.async false
set_option linter.all false

section
namespace OAI

section

namespace MaximalSeshadri.PlaneCech
noncomputable section
variable {K M P : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup P] [Module K P]

theorem finite_quotient_of_kernel_le {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Module.Finite K W]
    (f : V →ₗ[K] W) (B : Submodule K V) (h : LinearMap.ker f ≤ B) :
    Module.Finite K (V ⧸ B) := by
  let : Module.Finite K (V ⧸ LinearMap.ker f) := Module.Finite.equiv f.quotKerEquivRange.symm
  let q : (V ⧸ LinearMap.ker f) →ₗ[K] (V ⧸ B) :=
    Submodule.mapQ (LinearMap.ker f) B LinearMap.id h
  apply Module.Finite.of_surjective q
  intro x
  obtain ⟨v,rfl⟩ := B.mkQ_surjective x
  exact ⟨(LinearMap.ker f).mkQ v,rfl⟩

end
end MaximalSeshadri.PlaneCech

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

namespace MaximalSeshadri.ModuleMayerVietoris
noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open ModuleFlasque
universe u
variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

lemma freeOpen_glue3 {U V W : Opens X} {N : SheafOfModules R}
    (f : freeOpen R U ⟶ N) (g : freeOpen R V ⟶ N) (h : freeOpen R W ⟶ N)
    (hfg : freeOpenMap R (homOfLE (show U ⊓ V ≤ U from inf_le_left)) ≫ f =
      freeOpenMap R (homOfLE (show U ⊓ V ≤ V from inf_le_right)) ≫ g)
    (hfh : freeOpenMap R (homOfLE (show U ⊓ W ≤ U from inf_le_left)) ≫ f =
      freeOpenMap R (homOfLE (show U ⊓ W ≤ W from inf_le_right)) ≫ h)
    (hgh : freeOpenMap R (homOfLE (show V ⊓ W ≤ V from inf_le_left)) ≫ g =
      freeOpenMap R (homOfLE (show V ⊓ W ≤ W from inf_le_right)) ≫ h) :
    ∃ l : freeOpen R ((U ⊔ V) ⊔ W) ⟶ N,
      freeOpenMap R (homOfLE (le_sup_left.trans le_sup_left)) ≫ l = f ∧
      freeOpenMap R (homOfLE (le_sup_right.trans le_sup_left)) ≫ l = g ∧
      freeOpenMap R (homOfLE le_sup_right) ≫ l = h := by
  let p : freeOpen R (U ⊔ V) ⟶ N := CategoryTheory.IsPushout.desc (freeOpen_isPushout R U V) f g hfg
  have hpU : freeOpenMap R (homOfLE (show U ≤ U ⊔ V from le_sup_left)) ≫ p = f :=
    CategoryTheory.IsPushout.inl_desc (freeOpen_isPushout R U V) f g hfg
  have hpV : freeOpenMap R (homOfLE (show V ≤ U ⊔ V from le_sup_right)) ≫ p = g :=
    CategoryTheory.IsPushout.inr_desc (freeOpen_isPushout R U V) f g hfg
  have hp : freeOpenMap R (homOfLE (show (U ⊔ V) ⊓ W ≤ U ⊔ V from inf_le_left)) ≫ p =
      freeOpenMap R (homOfLE (show (U ⊔ V) ⊓ W ≤ W from inf_le_right)) ≫ h := by
    apply freeOpen_hom_ext R (A := U ⊓ W) (B := V ⊓ W)
      (inf_le_inf le_sup_left le_rfl) (inf_le_inf le_sup_right le_rfl) (inf_sup_right U V W).symm
    · simp only [← Category.assoc,freeOpenMap_comp]
      change freeOpenMap R (homOfLE (inf_le_left.trans le_sup_left)) ≫ p = freeOpenMap R (homOfLE inf_le_right) ≫ h
      rw [show freeOpenMap R (homOfLE (show U ⊓ W ≤ U ⊔ V from inf_le_left.trans le_sup_left)) =
        freeOpenMap R (homOfLE (show U ⊓ W ≤ U from inf_le_left)) ≫
          freeOpenMap R (homOfLE (show U ≤ U ⊔ V from le_sup_left)) from
        (freeOpenMap_comp R _ _).symm,Category.assoc,hpU]
      exact hfh
    · simp only [← Category.assoc,freeOpenMap_comp]
      change freeOpenMap R (homOfLE (inf_le_left.trans le_sup_right)) ≫ p = freeOpenMap R (homOfLE inf_le_right) ≫ h
      rw [show freeOpenMap R (homOfLE (show V ⊓ W ≤ U ⊔ V from inf_le_left.trans le_sup_right)) =
        freeOpenMap R (homOfLE (show V ⊓ W ≤ V from inf_le_left)) ≫
          freeOpenMap R (homOfLE (show V ≤ U ⊔ V from le_sup_right)) from
        (freeOpenMap_comp R _ _).symm,Category.assoc,hpV]
      exact hgh
  let l : freeOpen R ((U ⊔ V) ⊔ W) ⟶ N := CategoryTheory.IsPushout.desc (freeOpen_isPushout R (U ⊔ V) W) p h hp
  have hl : freeOpenMap R (homOfLE (show U ⊔ V ≤ (U ⊔ V) ⊔ W from le_sup_left)) ≫ l = p :=
    CategoryTheory.IsPushout.inl_desc (freeOpen_isPushout R (U ⊔ V) W) p h hp
  refine ⟨l,?_,?_,CategoryTheory.IsPushout.inr_desc (freeOpen_isPushout R (U ⊔ V) W) p h hp⟩
  · rw [show freeOpenMap R (homOfLE (show U ≤ (U ⊔ V) ⊔ W from le_sup_left.trans le_sup_left)) =
      freeOpenMap R (homOfLE (show U ≤ U ⊔ V from le_sup_left)) ≫
        freeOpenMap R (homOfLE (show U ⊔ V ≤ (U ⊔ V) ⊔ W from le_sup_left)) from
      (freeOpenMap_comp R _ _).symm,Category.assoc,hl,hpU]
  · rw [show freeOpenMap R (homOfLE (show V ≤ (U ⊔ V) ⊔ W from le_sup_right.trans le_sup_left)) =
      freeOpenMap R (homOfLE (show V ≤ U ⊔ V from le_sup_right)) ≫
        freeOpenMap R (homOfLE (show U ⊔ V ≤ (U ⊔ V) ⊔ W from le_sup_left)) from
      (freeOpenMap_comp R _ _).symm,Category.assoc,hl,hpV]

end
end MaximalSeshadri.ModuleMayerVietoris

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.ModuleMayerVietoris
noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open ModuleFlasque
universe u
variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

def tripleG_isCokernel (U V W : Opens X) :
    IsColimit (CokernelCofork.ofπ (tripleG R U V W) (tripleDG R U V W)) := by
  apply CokernelCofork.IsColimit.ofπ'
  intro N k hk
  have hab := congrArg (fun z => biprod.inl ≫ z) hk
  have hac := congrArg (fun z => biprod.inl ≫ biprod.inr ≫ z) hk
  have hbc := congrArg (fun z => biprod.inr ≫ biprod.inr ≫ z) hk
  simp only [tripleD,Category.assoc,biprod.inl_desc_assoc,biprod.inr_desc_assoc,
    Preadditive.sub_comp,Preadditive.add_comp,Preadditive.neg_comp,Limits.comp_zero] at hab hac hbc
  apply Classical.indefiniteDescription
  obtain ⟨l,hl0,hl1,hl2⟩ := freeOpen_glue3 R (biprod.inl ≫ k)
    (biprod.inl ≫ biprod.inr ≫ k) (biprod.inr ≫ biprod.inr ≫ k)
    (sub_eq_zero.mp hab) (by simpa only [Preadditive.neg_comp,neg_add_eq_sub] using (sub_eq_zero.mp (by simpa only [Preadditive.neg_comp,neg_add_eq_sub] using hac)).symm)
    (sub_eq_zero.mp hbc)
  refine ⟨l,?_⟩
  apply biprod.hom_ext'
  · simpa [tripleG,Category.assoc] using hl0
  · apply biprod.hom_ext'
    · simpa [tripleG,Category.assoc] using hl1
    · simpa [tripleG,Category.assoc] using hl2

instance tripleToRelations_epi (U V W : Opens X) : Epi (tripleToRelations R U V W) := by
  let S := ShortComplex.mk (tripleD R U V W) (tripleG R U V W) (tripleDG R U V W)
  exact S.exact_iff_epi_kernel_lift.mp (S.exact_of_g_is_cokernel (tripleG_isCokernel R U V W))

end
end MaximalSeshadri.ModuleMayerVietoris

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ModuleFlasque

variable {K : Type} [Field K] {X : Scheme.{0}}
attribute [local instance] OAI.MaximalSeshadri.Geometry.BaseSections.instLinearCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopSheafOfModulesRingCatSheaf_definitions

attribute [local instance] OAI.MaximalSeshadri.Geometry.BaseSections.baseHomModule

attribute [local instance] OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupHomSheafOfModulesOpensCarrierCarrierCommRingCatRingCatSheafFreeOpen

attribute [local instance] OAI.MaximalSeshadri.Geometry.BaseSections.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen

lemma homChart_injective [IsIntegral X] (k : K →+* Γ(X,⊤)) (L : LineBundle X)
    {U T : X.Opens} (h : T ≤ U) [Nonempty T] : Function.Injective (homChart k L.sheaf h) := by
  intro f g he
  apply (freeBaseEquiv k L.sheaf U).injective
  apply L.restriction_injective (homOfLE h)
  change res k L.sheaf h (freeBaseEquiv k L.sheaf U f) = res k L.sheaf h (freeBaseEquiv k L.sheaf U g)
  exact (chartTop k L.sheaf T).symm.injective he

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames ModuleFlasque ModuleMayerVietoris MaximalSeshadri.Projective MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}}
attribute [local instance] OAI.MaximalSeshadri.Geometry.BaseSections.planeRelationCyclesLinear

attribute [local instance] baseHomModule

lemma relationCycles_injective [IsIntegral X] (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Fin 3 → (O X ⟶ M)) [Nonempty (planeTriple s)] (L : LineBundle X) :
    Function.Injective (relationCycles k s L) := by
  intro f g h
  let : Epi (planeRelPi s) := tripleToRelations_epi X.ringCatSheaf
    (SectionOpens.isoOpen (s 0)) (SectionOpens.isoOpen (s 1)) (SectionOpens.isoOpen (s 2))
  apply (cancel_epi (planeRelPi s)).mp
  apply biprod.hom_ext' (C := SheafOfModules X.ringCatSheaf)
  · have component : (biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫ planeRelPi s) ≫ f =
        (biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫ planeRelPi s) ≫ g :=
      homChart_injective k L (le_inf (planeTriple_le s 0) (planeTriple_le s 1))
        (congrArg (fun z => z.val.1.val) h)
    exact (Category.assoc _ _ _).symm.trans (component.trans (Category.assoc _ _ _))
  · apply biprod.hom_ext' (C := SheafOfModules X.ringCatSheaf)
    · have component : (biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫
          biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ planeRelPi s) ≫ f =
          (biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫
            biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ planeRelPi s) ≫ g :=
        homChart_injective k L (le_inf (planeTriple_le s 0) (planeTriple_le s 2))
          (congrArg (fun z => z.val.2.1.val) h)
      exact ((Category.assoc _ _ _).trans
        (congrArg (fun arrow => biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫ arrow)
          (Category.assoc _ _ _))).symm.trans (component.trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun arrow => biprod.inl (C := SheafOfModules X.ringCatSheaf) ≫ arrow)
                (Category.assoc _ _ _))))
    · have component : (biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫
          biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ planeRelPi s) ≫ f =
          (biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫
            biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ planeRelPi s) ≫ g :=
        homChart_injective k L (le_inf (planeTriple_le s 1) (planeTriple_le s 2))
          (congrArg (fun z => z.val.2.2.val) h)
      exact ((Category.assoc _ _ _).trans
        (congrArg (fun arrow => biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ arrow)
          (Category.assoc _ _ _))).symm.trans (component.trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun arrow => biprod.inr (C := SheafOfModules X.ringCatSheaf) ≫ arrow)
                (Category.assoc _ _ _))))

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end

section
namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames BaseSections ModuleFlasque ModuleMayerVietoris
open MaximalSeshadri.PlaneCech

variable {K : Type} [Field K] {X : Scheme.{0}}
attribute [local instance] OAI.MaximalSeshadri.Geometry.instLinearCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopSheafOfModulesRingCatSheaf_definitions_1

attribute [local instance] OAI.MaximalSeshadri.Geometry.instHasExtSheafOfModulesOpensCarrierCarrierCommRingCatRingCatSheaf_definitions_1

attribute [local instance] baseHomModule

lemma finite_plane_relation_quotient [IsIntegral X] (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] [Nonempty (planeTriple s)] (L : LineBundle X) :
    Module.Finite K (BaseHom k (planeRelations s) L.sheaf ⧸ relationBoundaries k s L) := by
  let Q := vertexBoundaries (planePair k s L 0 1) (planePair k s L 0 2) (planePair k s L 1 2)
    (planeVertex k s L)
  let : Module.Finite K
      (cycles (planePair k s L 0 1) (planePair k s L 0 2) (planePair k s L 1 2) ⧸ Q) :=
    finite_plane_H1 k s hs L
  apply finite_quotient_of_kernel_le (Q.mkQ.comp (relationCycles k s L))
  intro x hx
  have hx' : relationCycles k s L x ∈ Q := (Submodule.Quotient.mk_eq_zero Q).mp hx
  obtain ⟨y,hy,he⟩ := plane_boundaries_lift k s L hx'
  have hxy : y = x := relationCycles_injective k s L he
  rwa [hxy] at hy

end
end MaximalSeshadri.Geometry

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.finite_plane_relation_quotient := @OAI.MaximalSeshadri.Geometry.finite_plane_relation_quotient
