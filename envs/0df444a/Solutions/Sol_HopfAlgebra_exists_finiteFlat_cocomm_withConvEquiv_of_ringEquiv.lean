-- Prove2me | solution 1 for HopfAlgebra.exists_finiteFlat_cocomm_withConvEquiv_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/be77fe77-4103-5466-8594-e39e28ee9b31

import Mathlib
import Theorems.Thm_AlgHom_liftEquiv_symm_withConv_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_finiteFlat_cocomm_withConvEquiv_of_ringEquiv

set_option maxHeartbeats 8000000

open TensorProduct

theorem solution
    (R : Type) [CommRing R] (S : Type) [CommRing S] (φ : R ≃+* S)
    [Algebra R (AlgebraicClosure ℚ)] [Algebra S (AlgebraicClosure ℚ)]
    (hφ : ∀ r, algebraMap R (AlgebraicClosure ℚ) r = algebraMap S (AlgebraicClosure ℚ) (φ r))
    {N : Type} [AddCommGroup N]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N]
    (H : Type) [CommRing H] [HopfAlgebra S H]
    (hHfin : Module.Finite S H) (hHflat : Module.Flat S H)
    (hHcocomm : Coalgebra.IsCocomm S H)
    (eH : WithConv (H →ₐ[S] AlgebraicClosure ℚ) ≃ N)
    (heH_add : ∀ f g, eH (f * g) = eH f + eH g)
    (heH_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[S] AlgebraicClosure ℚ)),
      (∀ h : H, g h = σ (f h)) → eH g = σ • (eH f)) :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra R H'),
      Module.Finite R H' ∧ Module.Flat R H' ∧ Coalgebra.IsCocomm R H' ∧
      ∃ e' : WithConv (H' →ₐ[R] AlgebraicClosure ℚ) ≃ N,
        (∀ f g, e' (f * g) = e' f + e' g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H' →ₐ[R] AlgebraicClosure ℚ)),
          (∀ h : H', g h = σ (f h)) → e' g = σ • (e' f) := by
  classical

  letI algSR : Algebra S R := φ.symm.toRingHom.toAlgebra
  haveI towSRK : IsScalarTower S R (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq (fun s => by
      show algebraMap S (AlgebraicClosure ℚ) s = algebraMap R (AlgebraicClosure ℚ) (φ.symm s)
      rw [hφ (φ.symm s), RingEquiv.apply_symm_apply])
  refine ⟨R ⊗[S] H, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩

  let ι := AlgHom.liftEquiv S R H (AlgebraicClosure ℚ)
  let ιW : WithConv (R ⊗[S] H →ₐ[R] AlgebraicClosure ℚ) ≃
           WithConv (H →ₐ[S] AlgebraicClosure ℚ) :=
    ⟨fun f => WithConv.toConv (ι.symm f.ofConv), fun g => WithConv.toConv (ι g.ofConv),
     fun f => by simp only [WithConv.ofConv_toConv, Equiv.apply_symm_apply, WithConv.toConv_ofConv],
     fun g => by simp only [WithConv.ofConv_toConv, Equiv.symm_apply_apply, WithConv.toConv_ofConv]⟩
  have hιW_ofConv : ∀ f, (ιW f).ofConv = ι.symm f.ofConv := fun f => rfl
  have hιW_fn : ∀ (f : WithConv (R ⊗[S] H →ₐ[R] AlgebraicClosure ℚ)) (h : H),
      (ιW f).ofConv h = f.ofConv (1 ⊗ₜ[S] h) := fun f h => rfl
  refine ⟨ιW.trans eH, ?_, ?_⟩
  ·
    intro f g
    simp only [Equiv.trans_apply]
    rw [show ιW (f * g) = ιW f * ιW g from
      AlgHom.liftEquiv_symm_withConv_mul S R H (AlgebraicClosure ℚ) f g]
    exact heH_add _ _
  ·
    intro σ f g hfg
    simp only [Equiv.trans_apply]
    apply heH_act σ (ιW f) (ιW g)
    intro h
    rw [hιW_fn g h, hιW_fn f h]
    exact hfg (1 ⊗ₜ[S] h)

end S_HopfAlgebra_exists_finiteFlat_cocomm_withConvEquiv_of_ringEquiv
end P2MW
export P2MW.S_HopfAlgebra_exists_finiteFlat_cocomm_withConvEquiv_of_ringEquiv (solution)
