-- Prove2me | solution 1 for NLabCohomology.trivialCocycle_cohomologous
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T21:42:35.913833+00:00
-- url     : https://prove2.me/submissions/5ebf88c6-1445-4f98-bc3f-a3ac847f3e68

import Definitions.Def_NLabCohomology_Cohomology

universe u

open CategoryTheory Simplicial Opposite

namespace TrivAux

open SSet

lemma sq : Subcomplex.BicartSq.{u} (⊥ : (Δ[1] : SSet.{u}).Subcomplex) (stdSimplex.face {0})
    (stdSimplex.face {1}) (boundary 1) where
  sup_eq := by
    have e0 : ({1}ᶜ : Finset (Fin 2)) = {0} := by decide
    have e1 : ({0}ᶜ : Finset (Fin 2)) = {1} := by decide
    apply le_antisymm
    · apply sup_le
      · have := face_singleton_compl_le_boundary.{u} (n := 1) 1
        rwa [e0] at this
      · have := face_singleton_compl_le_boundary.{u} (n := 1) 0
        rwa [e1] at this
    · rw [boundary_eq_iSup, iSup_le_iff]
      intro i
      fin_cases i
      · simp only [Fin.zero_eta, e1]; exact le_sup_right
      · simp only [Fin.mk_one, e0]; exact le_sup_left
  inf_eq := by
    rw [stdSimplex.face_inter_face]
    have : ({0} ⊓ {1} : Finset (Fin 2)) = ∅ := by decide
    rw [this]
    ext
    simp

lemma edge_of_contractible {K : SSet.{u}} (hK : NLabCohomology.IsContractible K)
    (t₁ t₂ : K _⦋0⦌) : Nonempty (K.Edge t₁ t₂) := by
  let u' : (stdSimplex.face.{u} {(0 : Fin 2)} : SSet.{u}) ⟶ K :=
    (stdSimplex.faceSingletonIso (0 : Fin 2)).inv ≫ yonedaEquiv.symm t₁
  let v' : (stdSimplex.face.{u} {(1 : Fin 2)} : SSet.{u}) ⟶ K :=
    (stdSimplex.faceSingletonIso (1 : Fin 2)).inv ≫ yonedaEquiv.symm t₂
  let f := sq.{u}.isPushout.desc u' v' (Subcomplex.isInitialBot.hom_ext _ _)
  obtain ⟨g, hg⟩ := hK.2 0 f
  have hl : (stdSimplex.face.{u} {(0 : Fin 2)}).ι = Subcomplex.homOfLE sq.le₂₄ ≫ (boundary 1).ι := rfl
  have hr : (stdSimplex.face.{u} {(1 : Fin 2)}).ι = Subcomplex.homOfLE sq.le₃₄ ≫ (boundary 1).ι := rfl
  have h1 : K.δ 1 (yonedaEquiv g) = t₁ := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ,
      hl, Category.assoc, Category.assoc, hg, sq.isPushout.inl_desc]
    simp [u', yonedaEquiv_const]
  have h0 : K.δ 0 (yonedaEquiv g) = t₂ := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← stdSimplex.faceSingletonIso_one_hom_comp_ι_eq_δ,
      hr, Category.assoc, Category.assoc, hg, sq.isPushout.inr_desc]
    simp [v', yonedaEquiv_const]
  exact ⟨(Edge.mk' (yonedaEquiv g)).ofEq h1 h0⟩

end TrivAux

open NLabCohomology in
theorem solution (H : InfinityOneCategory.{u})
    (T : TerminalObject H) (X : H.Obj) (t₁ t₂ : Cocycle H X T.star) :
    Cohomologous H t₁ t₂ :=
  TrivAux.edge_of_contractible (T.contractible X) t₁ t₂
