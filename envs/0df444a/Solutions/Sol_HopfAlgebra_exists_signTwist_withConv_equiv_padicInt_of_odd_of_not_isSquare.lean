-- Prove2me | solution 1 for HopfAlgebra.exists_signTwist_withConv_equiv_padicInt_of_odd_of_not_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c20bcac1-331f-5317-b2e4-b27ddedf3bc8

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_HopfAlgebra_exists_signTwist_withConv_mulEquiv_padicInt_of_odd_of_not_isSquare
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_signTwist_withConv_equiv_padicInt_of_odd_of_not_isSquare

open scoped NNReal TensorProduct

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (d : ℚ_[p]) (hd : ‖d‖₊ = 1) (hd_nsq : ¬ IsSquare d)
    (s : AlgebraicClosure ℚ_[p]) (hs : s ^ 2 = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) d)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (hfin : Module.Finite ℤ_[p] H) (hflat : Module.Flat ℤ_[p] H)
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] H)
    {M : Type} [AddCommGroup M]
    [DistribMulAction (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) M]
    (e : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ h : H, g h = σ (f h)) → e g = σ • (e f)) :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra ℤ_[p] H'),
      Module.Finite ℤ_[p] H' ∧ Module.Flat ℤ_[p] H' ∧ Coalgebra.IsCocomm ℤ_[p] H' ∧
      ∃ e' : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃ M,
        (∀ f g, e' (f * g) = e' f + e' g) ∧
        ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
          (f g : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
          (∀ h' : H', g h' = σ (f h')) →
            (σ s = s → e' g = σ • (e' f)) ∧
            (σ s ≠ s → e' g = -(σ • (e' f))) := by

  obtain ⟨H', iCR, iHA, hfin', hflat', hcc', β, hβmul, hβtw⟩ :=
    HopfAlgebra.exists_signTwist_withConv_mulEquiv_padicInt_of_odd_of_not_isSquare
      p hp2 d hd hd_nsq s hs H hfin hflat hcocomm
  letI : CommRing H' := iCR
  letI : HopfAlgebra ℤ_[p] H' := iHA

  have he1 : e 1 = 0 := by
    have h := he_add 1 1; rw [one_mul] at h
    have h' : e 1 + 0 = e 1 + e 1 := by rw [add_zero]; exact h
    exact (add_left_cancel h').symm

  have heinv : ∀ (x y : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
      x * y = 1 → e x = - e y := by
    intro x y hxy
    have h := he_add x y; rw [hxy, he1] at h
    exact eq_neg_of_add_eq_zero_left h.symm

  refine ⟨H', iCR, iHA, hfin', hflat', hcc', β.trans e, ?_, ?_⟩
  ·
    intro f' g'
    show e (β (f' * g')) = e (β f') + e (β g')
    rw [hβmul f' g', he_add]
  ·
    intro σ f' g' hσ

    let G : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) :=
      WithConv.toConv
        ((σ.toAlgHom.restrictScalars ℤ_[p]).comp (WithConv.ofConv (β f')))
    have hG : ∀ h : H, G h = σ ((β f') h) := by
      intro h
      first
        | rfl
        | simp only [G, WithConv.ofConv_toConv, AlgHom.coe_comp, Function.comp_apply,
            AlgHom.coe_restrictScalars, AlgEquiv.coe_toAlgHom,
            AlgEquiv.restrictScalars_apply, AlgHom.restrictScalars_apply]
        | (show (WithConv.ofConv G) h = σ ((WithConv.ofConv (β f')) h);
           simp only [G, WithConv.ofConv_toConv, AlgHom.coe_comp, Function.comp_apply,
             AlgHom.coe_restrictScalars, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_algHom])
    have heG : e G = σ • e (β f') := he_act σ (β f') G hG
    obtain ⟨hfix, hneg⟩ := hβtw σ f' g' G hσ hG
    refine ⟨fun hss => ?_, fun hss => ?_⟩
    ·
      show e (β g') = σ • e (β f')
      rw [hfix hss, heG]
    ·
      show e (β g') = -(σ • e (β f'))
      rw [heinv (β g') G (hneg hss), heG]

end S_HopfAlgebra_exists_signTwist_withConv_equiv_padicInt_of_odd_of_not_isSquare
end P2MW
export P2MW.S_HopfAlgebra_exists_signTwist_withConv_equiv_padicInt_of_odd_of_not_isSquare (solution)
