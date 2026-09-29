-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.IsFormalCoordinates.eq_of_forall_apply_nilEval_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/8f6825f6-8e8c-5628-8306-1e647a1a5bf8

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_IsFormalCoordinates_eq_of_forall_apply_nilEval_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry GoodReductionJacobian

theorem solution
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    {g : ℕ} (F : MvFormalGroup g B) (θ : RelativeGroupLaw.FormalCoordinates f g) (hθ : L.IsFormalCoordinates F θ)
    (ε ε' : MvFormalGroup.End F)
    (h : ∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
      ∀ s : Fin g → B', (∀ i, s i ∈ J) →
        θ B' (fun i => MvFormalGroup.nilEval m (ε.toPowerSeries i) s) =
          θ B' (fun i => MvFormalGroup.nilEval m (ε'.toPowerSeries i) s)) :
    ε = ε' := by
  classical

  have hmem : ∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (m : ℕ) (φ : MvPowerSeries (Fin g) B),
      φ.constantCoeff = 0 → ∀ s : Fin g → B', (∀ i, s i ∈ J) → MvFormalGroup.nilEval m φ s ∈ J := by
    intro B' _ _ J m φ hφ s hs
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    unfold MvFormalGroup.nilEval
    have hs0 : (fun i => (Ideal.Quotient.mkₐ B J) (s i)) = 0 := by
      funext i
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr (hs i)
    have e1 : (Ideal.Quotient.mkₐ B J)
        (MvPolynomial.aeval s (MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ => m) φ)) =
        MvPolynomial.aeval (fun i => (Ideal.Quotient.mkₐ B J) (s i))
          (MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ => m) φ) := by
      rw [← MvPolynomial.comp_aeval, AlgHom.comp_apply]
    change (Ideal.Quotient.mkₐ B J) _ = 0
    rw [e1, hs0, MvPolynomial.aeval_zero]
    have : MvPolynomial.constantCoeff (MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ => m) φ) = 0 := by
      change MvPolynomial.coeff 0 _ = 0
      rw [MvPowerSeries.coeff_trunc', if_pos (show (0 : Fin g →₀ ℕ) ≤ _ from bot_le), MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact hφ
    rw [this, map_zero]

  have hsep : ∀ φ ψ : MvPowerSeries (Fin g) B,
      (∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (m : ℕ), J ^ (m + 1) = ⊥ →
        ∀ s : Fin g → B', (∀ i, s i ∈ J) → MvFormalGroup.nilEval m φ s = MvFormalGroup.nilEval m ψ s) → φ = ψ := by
    intro φ ψ hφψ
    ext e
    set m : ℕ := e.degree with hm
    let I : Ideal (MvPolynomial (Fin g) B) := MvPolynomial.idealOfVars (Fin g) B ^ (m + 1)

    have hJ : (Ideal.map (Ideal.Quotient.mk I) (MvPolynomial.idealOfVars (Fin g) B)) ^ (m + 1) = ⊥ := by
      rw [← Ideal.map_pow, Ideal.map_quotient_self]
    have hs : ∀ i : Fin g, Ideal.Quotient.mk I (MvPolynomial.X i) ∈
        Ideal.map (Ideal.Quotient.mk I) (MvPolynomial.idealOfVars (Fin g) B) :=
      fun i => Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)
    have key := hφψ (MvPolynomial (Fin g) B ⧸ I) _ m hJ (fun i => Ideal.Quotient.mk I (MvPolynomial.X i)) hs

    have hev : ∀ p : MvPolynomial (Fin g) B,
        MvPolynomial.aeval (fun i => Ideal.Quotient.mk I (MvPolynomial.X i)) p = Ideal.Quotient.mk I p := by
      intro p
      have : MvPolynomial.aeval (R := B) (fun i => Ideal.Quotient.mk I (MvPolynomial.X i)) =
          Ideal.Quotient.mkₐ B I := by
        apply MvPolynomial.algHom_ext
        intro i
        rw [MvPolynomial.aeval_X]
        rfl
      exact congrArg (fun F => F p) this
    unfold MvFormalGroup.nilEval at key
    rw [hev, hev, Ideal.Quotient.eq, MvPolynomial.mem_pow_idealOfVars_iff'] at key
    have hdeg : e.degree < m + 1 := by omega
    have := key e hdeg
    rw [MvPolynomial.coeff_sub, sub_eq_zero, MvPowerSeries.coeff_trunc', MvPowerSeries.coeff_trunc'] at this
    have hle : e ≤ Finsupp.equivFunOnFinite.symm (fun _ : Fin g => m) := by
      rw [Finsupp.le_def]
      intro i
      rw [Finsupp.coe_equivFunOnFinite_symm]
      exact (Finsupp.le_degree i e).trans (le_of_eq hm.symm)
    simpa [hle] using this

  apply MvFormalGroup.Hom.ext
  funext i
  apply hsep
  intro B' _ _ J m hJ s hs
  have hinj := ((hθ.2 B' J m hJ).2.1)
    (fun i => MvFormalGroup.nilEval m (ε.toPowerSeries i) s) (fun i => MvFormalGroup.nilEval m (ε'.toPowerSeries i) s)
    (fun i => hmem B' J m _ (ε.constantCoeff_eq_zero i) s hs)
    (fun i => hmem B' J m _ (ε'.constantCoeff_eq_zero i) s hs)
    (h B' J m hJ s hs)
  exact congrFun hinj i

end S_GoodReductionJacobian_RelativeGroupLaw_IsFormalCoordinates_eq_of_forall_apply_nilEval_eq
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_IsFormalCoordinates_eq_of_forall_apply_nilEval_eq (solution)
