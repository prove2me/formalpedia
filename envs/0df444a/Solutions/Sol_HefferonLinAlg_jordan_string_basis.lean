-- Prove2me | solution 1 for HefferonLinAlg.jordan_string_basis
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-08-07T15:13:18.777987+00:00
-- url     : https://prove2.me/submissions/39e0cffc-4fb5-451d-9ffb-d2e5b3823417

import Theorems.Thm_HefferonLinAlg_nilpotent_string_basis

open Module

theorem solution {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) :
    ∃ (k : ℕ) (sz : Fin k → ℕ) (lam : Fin k → ℂ)
      (b : Module.Basis (Σ i : Fin k, Fin (sz i)) ℂ V),
      (∀ i, 0 < sz i) ∧
        ∀ (i : Fin k) (a : Fin (sz i)),
          f (b ⟨i, a⟩) =
            lam i • b ⟨i, a⟩ +
              (if h : (a : ℕ) + 1 < sz i then b ⟨i, ⟨(a : ℕ) + 1, h⟩⟩ else 0) := by
  classical
  have hint : DirectSum.IsInternal (fun μ : ℂ => f.maxGenEigenspace μ) := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    exact ⟨f.independent_maxGenEigenspace, f.iSup_maxGenEigenspace_eq_top⟩
  have hmaps : ∀ μ : ℂ, Set.MapsTo (f - algebraMap ℂ (Module.End ℂ V) μ)
      ↑(f.maxGenEigenspace μ) ↑(f.maxGenEigenspace μ) := fun μ =>
    Module.End.mapsTo_maxGenEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ
  have hnil : ∀ μ : ℂ,
      IsNilpotent ((f - algebraMap ℂ (Module.End ℂ V) μ).restrict (hmaps μ)) := fun μ =>
    Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap f μ
  choose kk ss bb hpos0 hstr0 using fun μ : ℂ =>
    HefferonLinAlg.nilpotent_string_basis _ (hnil μ)
  set B := hint.collectedBasis bb with hB
  letI : Fintype (Σ μ : ℂ, Σ i : Fin (kk μ), Fin (ss μ i)) :=
    FiniteDimensional.fintypeBasisIndex B
  letI : Fintype (Σ μ : ℂ, Fin (kk μ)) :=
    Fintype.ofInjective
      (fun p : Σ μ : ℂ, Fin (kk μ) =>
        (⟨p.1, ⟨p.2, ⟨0, hpos0 p.1 p.2⟩⟩⟩ : Σ μ : ℂ, Σ i : Fin (kk μ), Fin (ss μ i)))
      (by
        rintro ⟨μ, i⟩ ⟨ν, j⟩ h
        simp only [Sigma.mk.injEq] at h
        obtain ⟨rfl, h2⟩ := h
        simp only [heq_eq_eq, Sigma.mk.injEq] at h2
        obtain ⟨rfl, -⟩ := h2
        rfl)
  set eS := Fintype.equivFin (Σ μ : ℂ, Fin (kk μ)) with heS
  refine ⟨Fintype.card (Σ μ : ℂ, Fin (kk μ)),
    fun j => ss (eS.symm j).1 (eS.symm j).2, fun j => (eS.symm j).1, ?_⟩
  set E := (Equiv.sigmaCongrLeft
      (β := fun p : (Σ μ : ℂ, Fin (kk μ)) => Fin (ss p.1 p.2)) eS.symm).trans
      (Equiv.sigmaAssoc (fun (μ : ℂ) (i : Fin (kk μ)) => Fin (ss μ i))) with hE
  refine ⟨B.reindex E.symm, fun j => hpos0 _ _, ?_⟩
  intro j a
  have hcoe : ∀ (c : Fin (Fintype.card (Σ μ : ℂ, Fin (kk μ))))
      (d : Fin (ss (eS.symm c).1 (eS.symm c).2)),
      (B.reindex E.symm) ⟨c, d⟩ = ((bb (eS.symm c).1 ⟨(eS.symm c).2, d⟩ : _) : V) := by
    intro c d
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, hB,
      DirectSum.IsInternal.collectedBasis_coe]
    rfl
  rw [hcoe]
  have hs := hstr0 (eS.symm j).1 (eS.symm j).2 a
  have key : ∀ w : f.maxGenEigenspace (eS.symm j).1,
      (((f - algebraMap ℂ (Module.End ℂ V) (eS.symm j).1).restrict (hmaps _) w : _) : V)
        = f (w : V) - (eS.symm j).1 • (w : V) := fun w => rfl
  by_cases h : (a : ℕ) + 1 < ss (eS.symm j).1 (eS.symm j).2
  · rw [dif_pos h] at hs
    have := congrArg Subtype.val hs
    rw [key] at this
    rw [dif_pos h, hcoe, ← this]
    abel
  · rw [dif_neg h] at hs
    have := congrArg Subtype.val hs
    rw [key] at this
    rw [dif_neg h, add_zero, ← sub_eq_zero]
    exact this
