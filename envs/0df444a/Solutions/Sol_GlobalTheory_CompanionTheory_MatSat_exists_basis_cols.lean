-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MatSat.exists_basis_cols
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:52:40.098527+00:00
-- url     : https://prove2.me/submissions/2afdbae1-eb37-4685-96d7-929a1d0e2b26

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_OrderOKOneInert
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsBasisCols
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Implements_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MatSat
namespace GlobalTheory.CompanionTheory.MatSat
theorem _root_.solution {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (A : Matrix (β ⊕ γ) β O) (hA : Function.Injective A.mulVecLin) :
    ∃ (P : Matrix (β ⊕ γ) (β ⊕ γ) O) (a : β → O) (s u : Matrix β β O),
      IsUnit P.det ∧ (∀ j, a j ≠ 0) ∧ A * s = P.toCols₁ * Matrix.diagonal a ∧
        A = P.toCols₁ * u := by
  classical
  obtain ⟨n, S⟩ := Submodule.smithNormalForm (Pi.basisFun O (β ⊕ γ)) (LinearMap.range A.mulVecLin)
  obtain ⟨φ⟩ : Nonempty (Fin n ≃ β) :=
    ⟨S.bN.indexEquiv ((Pi.basisFun O β).map (LinearEquiv.ofInjective A.mulVecLin hA))⟩
  obtain ⟨f', hf'⟩ : ∃ f' : β ↪ β ⊕ γ, ∀ b, f' b = S.f (φ.symm b) :=
    ⟨φ.symm.toEmbedding.trans S.f, fun _ => rfl⟩
  have hcard : Fintype.card γ = Fintype.card ((Set.range f')ᶜ : Set (β ⊕ γ)) := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective f'.injective, Fintype.card_sum]
    omega
  obtain ⟨e, he⟩ : ∃ e : β ⊕ γ ≃ β ⊕ γ, ∀ b, e (Sum.inl b) = f' b :=
    ⟨(Equiv.sumCongr (Equiv.ofInjective f' f'.injective) (Fintype.equivOfCardEq hcard)).trans
      (Equiv.Set.sumCompl (Set.range f')), fun b => by simp⟩
  obtain ⟨P, hPdef⟩ : ∃ P : Matrix (β ⊕ γ) (β ⊕ γ) O,
      P = (Pi.basisFun O (β ⊕ γ)).toMatrix (S.bM.reindex e.symm) := ⟨_, rfl⟩
  have hPdet : IsUnit P.det := by
    letI := (Pi.basisFun O (β ⊕ γ)).invertibleToMatrix (S.bM.reindex e.symm)
    rw [hPdef]
    exact Matrix.isUnit_det_of_invertible _
  have hP1 : ∀ i b, P.toCols₁ i b = S.bM (f' b) i := by
    intro i b
    show P i (Sum.inl b) = _
    rw [hPdef, Module.Basis.toMatrix_apply, Pi.basisFun_repr, Module.Basis.reindex_apply,
      Equiv.symm_symm, he]
  have hpre : ∀ b, ∃ v : β → O, A *ᵥ v = (S.bN (φ.symm b) : β ⊕ γ → O) := by
    intro b
    obtain ⟨v, hv⟩ := LinearMap.mem_range.1 (S.bN (φ.symm b)).2
    exact ⟨v, hv⟩
  choose pre hpre using hpre
  obtain ⟨s, hs⟩ : ∃ s : Matrix β β O, ∀ i b, s i b = pre b i :=
    ⟨Matrix.of fun i b => pre b i, fun _ _ => rfl⟩
  have ha : ∀ b, S.a (φ.symm b) ≠ 0 := by
    intro b h
    have h1 := S.snf (φ.symm b)
    rw [h, zero_smul] at h1
    exact S.bN.ne_zero _ ((Submodule.coe_eq_zero).1 h1)
  obtain ⟨u, hu⟩ : ∃ u : Matrix β β O, ∀ b' b, u b' b =
      S.bN.repr ⟨A.mulVecLin (Pi.single b 1), LinearMap.mem_range_self _ _⟩ (φ.symm b') *
        S.a (φ.symm b') :=
    ⟨Matrix.of fun b' b => S.bN.repr ⟨A.mulVecLin (Pi.single b 1), LinearMap.mem_range_self _ _⟩
      (φ.symm b') * S.a (φ.symm b'), fun _ _ => rfl⟩
  refine ⟨P, fun b => S.a (φ.symm b), s, u, hPdet, ha, ?_, ?_⟩
  · ext i b
    rw [Matrix.mul_diagonal, hP1, Matrix.mul_apply]
    have h1 := congrFun (hpre b) i
    simp only [Matrix.mulVec, dotProduct] at h1
    simp only [hs]
    rw [h1, S.snf, hf']
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · ext i b
    have hw := S.bN.sum_repr ⟨A.mulVecLin (Pi.single b 1), LinearMap.mem_range_self _ _⟩
    have hw' := congrArg (fun v : LinearMap.range A.mulVecLin => (v : β ⊕ γ → O) i) hw
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, S.snf] at hw'
    have hcol : (A.mulVecLin (Pi.single b 1)) i = A i b := by
      simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [Matrix.mul_apply]
    refine hcol.symm.trans (hw'.symm.trans ?_)
    simp only [hP1, hu, hf']
    refine Fintype.sum_equiv φ _ _ fun k => ?_
    simp only [Equiv.symm_apply_apply]
    ring
end GlobalTheory.CompanionTheory.MatSat
