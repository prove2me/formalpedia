-- Prove2me | solution 1 for HopfAlgebra.bijective_withConv_algHomComp_of_finite_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/764ba6d4-9b2a-5c9c-8710-ff05ce2f0349

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_bijective_withConv_algHomComp_of_finite_of_isAlgClosed

private theorem convMul_apply_repr' {K L : Type} [CommRing K] [CommRing L] [Algebra K L]
    {A : Type} [CommRing A] [HopfAlgebra K A]
    (f g : WithConv (A →ₐ[K] L)) (a : A) {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr K a ι𝓡) :
    (WithConv.ofConv (f * g)) a
      = ∑ i ∈ 𝓡.index, (WithConv.ofConv f) (𝓡.left i) * (WithConv.ofConv g) (𝓡.right i) := by
  have h := Coalgebra.Repr.convMul_apply 𝓡 (WithConv.toConv (WithConv.ofConv f).toLinearMap)
    (WithConv.toConv (WithConv.ofConv g).toLinearMap)
  rw [LinearMap.convMul_apply] at h
  exact h

theorem solution
    (K : Type) [Field K]
    (L₁ : Type) [Field L₁] [Algebra K L₁] [IsAlgClosed L₁]
    (L₂ : Type) [Field L₂] [Algebra K L₂] [IsAlgClosed L₂]
    (ι : L₁ →ₐ[K] L₂)
    (A : Type) [CommRing A] [HopfAlgebra K A] (hfin : Module.Finite K A) :
    Function.Bijective
      (fun f : WithConv (A →ₐ[K] L₁) => (WithConv.toConv (ι.comp f.ofConv) :
        WithConv (A →ₐ[K] L₂))) ∧
    ∀ f g : WithConv (A →ₐ[K] L₁),
      WithConv.toConv (ι.comp (f * g).ofConv)
        = WithConv.toConv (ι.comp f.ofConv) * WithConv.toConv (ι.comp g.ofConv) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro f g hfg
    have hfg' : ι.comp (WithConv.ofConv f) = ι.comp (WithConv.ofConv g) :=
      congrArg WithConv.ofConv hfg
    exact congrArg WithConv.toConv
      (AlgHom.ext fun a => ι.injective (DFunLike.congr_fun hfg' a))
  · intro g
    have hint : ∀ a, IsIntegral K ((WithConv.ofConv g) a) := fun a =>
      ((Algebra.IsIntegral.of_finite K A).isIntegral a).map (WithConv.ofConv g)
    have hmem : ∀ a, (WithConv.ofConv g) a ∈ ι.fieldRange := fun a => by
      obtain ⟨b, hb⟩ := (hint a).mem_range_algHom_of_minpoly_splits (IsAlgClosed.splits _) ι
      exact ⟨b, hb⟩
    let ιR : L₁ ≃ₐ[K] ι.fieldRange := AlgEquiv.ofInjectiveField ι
    let gR : A →ₐ[K] ι.fieldRange :=
      { toFun := fun a => ⟨(WithConv.ofConv g) a, hmem a⟩
        map_one' := Subtype.ext (WithConv.ofConv g).map_one
        map_mul' := fun a b => Subtype.ext ((WithConv.ofConv g).map_mul a b)
        map_zero' := Subtype.ext (WithConv.ofConv g).map_zero
        map_add' := fun a b => Subtype.ext ((WithConv.ofConv g).map_add a b)
        commutes' := fun r => Subtype.ext ((WithConv.ofConv g).commutes r) }
    refine ⟨WithConv.toConv (ιR.symm.toAlgHom.comp gR), ?_⟩
    apply congrArg WithConv.toConv
    ext a
    show ι (ιR.symm (gR a)) = (WithConv.ofConv g) a
    have h2 : ∀ y, (ιR y : L₂) = ι y := fun y => rfl
    rw [← h2, ιR.apply_symm_apply]; rfl
  · intro f g
    apply congrArg WithConv.toConv
    ext a
    show ι ((f * g).ofConv a)
       = (WithConv.toConv (ι.comp f.ofConv) * WithConv.toConv (ι.comp g.ofConv)).ofConv a
    let 𝓡 := Coalgebra.Repr.arbitrary K a
    rw [convMul_apply_repr' f g a 𝓡,
        convMul_apply_repr' (WithConv.toConv (ι.comp f.ofConv))
                            (WithConv.toConv (ι.comp g.ofConv)) a 𝓡,
        map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [WithConv.ofConv_toConv, AlgHom.comp_apply]
      exact ι.map_mul _ _

end S_HopfAlgebra_bijective_withConv_algHomComp_of_finite_of_isAlgClosed
end P2MW
export P2MW.S_HopfAlgebra_bijective_withConv_algHomComp_of_finite_of_isAlgClosed (solution)
