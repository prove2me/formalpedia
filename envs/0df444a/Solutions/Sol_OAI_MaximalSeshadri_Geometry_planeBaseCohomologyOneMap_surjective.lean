-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.planeBaseCohomologyOneMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T15:19:43.662364+00:00
-- url     : https://prove2.me/submissions/61cbb252-7d8d-48de-8f9e-e562a6ae11ea

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

set_option Elab.async false
set_option linter.all false

section
namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Abelian
open ModuleFlasque ModuleMayerVietoris

variable {X : Scheme.{0}}
attribute [local instance] OAI.MaximalSeshadri.Geometry.tripleTopExtLinear

attribute [local instance] OAI.MaximalSeshadri.Geometry.tripleTopExtHasExt

lemma tripleTopHomCohomologyOne_surjective [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V W : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hc : (U ⊔ V) ⊔ W = ⊤) : Function.Surjective
      (tripleTopHomCohomologyOne M U V W hU hV hW hc) :=
  (tripleTopHomExtEquiv (X := X) M U V W hU hV hW hc).surjective.comp
    (Submodule.mkQ_surjective _)

end
end MaximalSeshadri.Geometry

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

lemma planeBaseCohomologyOneMap_surjective [IsNoetherian X] (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (h : ∀ i, IsAffineOpen (SectionOpens.isoOpen (s i))) (L : LineBundle X) :
    Function.Surjective (planeBaseCohomologyOneMap k s hs h L) := by
  intro y
  have hc : (SectionOpens.isoOpen (s 0) ⊔ SectionOpens.isoOpen (s 1)) ⊔
      SectionOpens.isoOpen (s 2) = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (hs ▸ hx)
    fin_cases i
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi
  obtain ⟨x,hx⟩ := tripleTopHomCohomologyOne_surjective L.sheaf
    (SectionOpens.isoOpen (s 0)) (SectionOpens.isoOpen (s 1)) (SectionOpens.isoOpen (s 2))
      (h 0) (h 1) (h 2) hc y
  exact ⟨(relationBoundaries k s L).mkQ x,hx⟩

end
end MaximalSeshadri.Geometry

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.planeBaseCohomologyOneMap_surjective := @OAI.MaximalSeshadri.Geometry.planeBaseCohomologyOneMap_surjective
