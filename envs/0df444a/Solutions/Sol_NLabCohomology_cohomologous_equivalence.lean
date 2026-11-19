-- Prove2me | solution 1 for NLabCohomology.cohomologous_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T21:41:31.287889+00:00
-- url     : https://prove2.me/submissions/94cd786a-fc91-4687-8ecc-6c0e302206d9

import Definitions.Def_NLabCohomology_Cohomology

universe u

open CategoryTheory Simplicial Opposite

namespace CohAux

open SSet

lemma horn20 {S : SSet.{u}} [S.KanComplex] {x0 x1 x2 : S _⦋0⦌}
    (a : S.Edge x0 x1) (b : S.Edge x0 x2) : Nonempty (S.Edge x1 x2) := by
  have w : stdSimplex.δ (1 : Fin 2) ≫ yonedaEquiv.symm a.edge =
      stdSimplex.δ (1 : Fin 2) ≫ yonedaEquiv.symm b.edge := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm, a.src_eq, b.src_eq]
  obtain ⟨σ, hσ⟩ := KanComplex.hornFilling (n := 1) (i := 0)
    (horn₂₀.isPushout.{u}.desc (yonedaEquiv.symm a.edge) (yonedaEquiv.symm b.edge) w)
  have h2 : S.δ 2 (yonedaEquiv σ) = a.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    have : stdSimplex.δ (2 : Fin 3) ≫ σ = yonedaEquiv.symm a.edge := by
      rw [← horn.ι_ι (0 : Fin 3) 2 (by decide), Category.assoc, ← hσ]
      exact horn₂₀.isPushout.inl_desc _ _ _
    rw [this, Equiv.apply_symm_apply]
  have h1 : S.δ 1 (yonedaEquiv σ) = b.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    have : stdSimplex.δ (1 : Fin 3) ≫ σ = yonedaEquiv.symm b.edge := by
      rw [← horn.ι_ι (0 : Fin 3) 1 (by decide), Category.assoc, ← hσ]
      exact horn₂₀.isPushout.inr_desc _ _ _
    rw [this, Equiv.apply_symm_apply]
  obtain ⟨y0, y1, y2, f01, f12, f02, h, hs⟩ := Edge.CompStruct.exists_of_simplex (yonedaEquiv σ)
  have e1 : f01.edge = a.edge := by rw [← h.d₂, hs, h2]
  have e2 : f02.edge = b.edge := by rw [← h.d₁, hs, h1]
  have hy1 : y1 = x1 := by rw [← f01.tgt_eq, e1, a.tgt_eq]
  have hy2 : y2 = x2 := by rw [← f02.tgt_eq, e2, b.tgt_eq]
  subst hy1 hy2
  exact ⟨f12⟩

end CohAux

open NLabCohomology in
theorem solution (H : InfinityOneCategory.{u}) (X A : H.Obj) :
    Equivalence (fun c₁ c₂ : Cocycle H X A => Cohomologous H c₁ c₂) := by
  have := H.kan X A
  refine ⟨fun c => ⟨SSet.Edge.id c⟩, fun {x y} h => ?_, fun {x y z} h1 h2 => ?_⟩
  · obtain ⟨e⟩ := h
    exact CohAux.horn20 e (SSet.Edge.id x)
  · obtain ⟨e1⟩ := h1
    obtain ⟨e2⟩ := h2
    obtain ⟨e1'⟩ := CohAux.horn20 e1 (SSet.Edge.id x)
    exact CohAux.horn20 e1' e2
