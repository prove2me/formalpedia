-- Prove2me | solution 1 for HopfAlgebra.exists_restriction_points_hopfKer_mul_and_eq_one_iff_and_surjective_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ca417d16-92cb-52e1-ac82-1a84d08d3532

import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Theorems.Thm_HopfAlgebra_toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique
import Theorems.Thm_HopfAlgebra_exists_algHom_comp_hopfKer_val_eq_of_surjective_of_isAlgClosed
import Theorems.Thm_HopfAlgebra_hopfKer_baseChange_toSubmodule_eq_range_baseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_restriction_points_hopfKer_mul_and_eq_one_iff_and_surjective_of_isAlgClosed

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

open scoped TensorProduct

universe u v w

theorem solution
    (R : Type) [CommRing R] [IsDomain R] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
    (hR : Function.Injective (algebraMap R Ω))
    {H : Type} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H]
    {B₁ B₀ : Type} [CommRing B₁] [HopfAlgebra R B₁] [Module.Finite R B₁] [Module.Free R B₁] [Coalgebra.IsCocomm R B₁]
    [CommRing B₀] [HopfAlgebra R B₀] [Module.Finite R B₀] [Module.Free R B₀] [Coalgebra.IsCocomm R B₀]
    (π₁ : H →ₐc[R] B₁) (hπ₁ : Function.Surjective π₁) (ρ : B₁ →ₐc[R] B₀) (hρ : Function.Surjective ρ)
    [Module.Finite R ↥(HopfAlgebra.hopfKer ρ)] [Module.Free R ↥(HopfAlgebra.hopfKer ρ)]
    (N N' : Submonoid (WithConv (H →ₐ[R] Ω))) (hNN' : N ≤ N')
    (hpts₁ : ∀ f : H →ₐ[R] Ω,
      (∃ g : B₁ →ₐ[R] Ω, g.comp (π₁ : H →ₐ[R] B₁) = f) ↔ WithConv.toConv f ∈ N')
    (hpts₀ : ∀ f : H →ₐ[R] Ω,
      (∃ g : B₀ →ₐ[R] Ω, g.comp ((ρ.comp π₁ : H →ₐc[R] B₀) : H →ₐ[R] B₀) = f) ↔ WithConv.toConv f ∈ N) :
    ∃ r : WithConv (H →ₐ[R] Ω) → WithConv (↥(HopfAlgebra.hopfKer ρ) →ₐ[R] Ω),
      (∀ f ∈ N', ∀ g : B₁ →ₐ[R] Ω, g.comp (π₁ : H →ₐ[R] B₁) = f.ofConv →
        (r f).ofConv = g.comp (HopfAlgebra.hopfKer ρ).val) ∧
      (∀ f ∈ N', ∀ f' ∈ N', r (f * f') = r f * r f') ∧
      (∀ f ∈ N', (r f = 1 ↔ f ∈ N)) ∧
      (∀ ν : WithConv (↥(HopfAlgebra.hopfKer ρ) →ₐ[R] Ω), ∃ f ∈ N', r f = ν) := by
  classical
  haveI : Module.Flat R B₁ := Module.Flat.of_free
  haveI : Module.Flat R ↥(HopfAlgebra.hopfKer ρ) := Module.Flat.of_free
  obtain ⟨h1, hmul, huniq⟩ := HopfAlgebra.toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique ρ hρ (Ω)

  have hfac : ∀ f : WithConv (H →ₐ[R] Ω), f ∈ N' →
      ∃ g : B₁ →ₐ[R] Ω, g.comp (π₁ : H →ₐ[R] B₁) = f.ofConv := fun f hf =>
    (hpts₁ f.ofConv).mpr (by rw [WithConv.toConv_ofConv]; exact hf)
  have hfac_uniq : ∀ (g g' : B₁ →ₐ[R] Ω),
      g.comp (π₁ : H →ₐ[R] B₁) = g'.comp (π₁ : H →ₐ[R] B₁) → g = g' := by
    intro g g' h
    ext b
    obtain ⟨x, rfl⟩ := hπ₁ b
    exact congrArg (fun φ : H →ₐ[R] Ω => φ x) h
  let r : WithConv (H →ₐ[R] Ω) → WithConv (↥(HopfAlgebra.hopfKer ρ) →ₐ[R] Ω) := fun f =>
    if hf : f ∈ N' then WithConv.toConv ((Classical.choose (hfac f hf)).comp (HopfAlgebra.hopfKer ρ).val) else 1
  have hr : ∀ f (hf : f ∈ N') (g : B₁ →ₐ[R] Ω), g.comp (π₁ : H →ₐ[R] B₁) = f.ofConv →
      r f = WithConv.toConv (g.comp (HopfAlgebra.hopfKer ρ).val) := by
    intro f hf g hg
    simp only [r, dif_pos hf]
    rw [hfac_uniq _ g ((Classical.choose_spec (hfac f hf)).trans hg.symm)]
  refine ⟨r, fun f hf g hg => by rw [hr f hf g hg], ?_, ?_, ?_⟩
  ·
    intro f hf f' hf'
    obtain ⟨g, hg⟩ := hfac f hf
    obtain ⟨g', hg'⟩ := hfac f' hf'
    have hgg : (WithConv.ofConv (WithConv.toConv g * WithConv.toConv g')).comp (π₁ : H →ₐ[R] B₁) = (f * f').ofConv := by
      rw [AlgHom.convMul_comp_bialgHom_distrib, hg, hg', WithConv.toConv_ofConv, WithConv.toConv_ofConv]
    rw [hr _ ((N').mul_mem hf hf') _ hgg, hr f hf g hg, hr f' hf' g' hg']
    exact hmul _ _
  ·
    intro f hf
    obtain ⟨g, hg⟩ := hfac f hf
    rw [hr f hf g hg, ← h1]
    constructor
    · intro h
      have h' : (WithConv.ofConv (1 : WithConv (B₁ →ₐ[R] Ω))).comp (HopfAlgebra.hopfKer ρ).val =
          (WithConv.ofConv (WithConv.toConv g)).comp (HopfAlgebra.hopfKer ρ).val := by
        rw [WithConv.ofConv_toConv]; exact (WithConv.toConv_injective h).symm
      obtain ⟨χ, hχ, -⟩ := (huniq 1 (WithConv.toConv g)).mp h'
      rw [one_mul] at hχ
      have hgχ : g = χ.comp (ρ : B₁ →ₐ[R] B₀) := WithConv.toConv_injective hχ
      apply (hpts₀ f.ofConv).mp
      refine ⟨χ, ?_⟩
      rw [← hg, hgχ]
      rfl
    · intro hN
      obtain ⟨χ, hχ⟩ := (hpts₀ f.ofConv).mpr (by rw [WithConv.toConv_ofConv]; exact hN)
      have hgχ : g = χ.comp (ρ : B₁ →ₐ[R] B₀) := by
        apply hfac_uniq
        rw [hg, ← hχ]
        rfl
      have h' := (huniq 1 (WithConv.toConv g)).mpr ⟨χ, by beta_reduce; rw [one_mul, hgχ], fun χ' hχ' => by
        beta_reduce at hχ'
        rw [one_mul] at hχ'
        have := (WithConv.toConv_injective hχ').symm.trans hgχ
        ext b
        obtain ⟨x, rfl⟩ := hρ b
        exact congrArg (fun φ : B₁ →ₐ[R] Ω => φ x) this⟩
      rw [WithConv.ofConv_toConv] at h'
      exact congrArg WithConv.toConv h'.symm
  ·
    intro ν

    letI algK : Algebra (FractionRing R) (Ω) :=
      (IsFractionRing.lift hR : FractionRing R →+* Ω).toAlgebra
    haveI : IsScalarTower R (FractionRing R) (Ω) :=
      IsScalarTower.of_algebraMap_eq (fun r => (IsFractionRing.lift_algebraMap hR r).symm)
    haveI : Module.Flat R (FractionRing R) := IsLocalization.flat _ (nonZeroDivisors R)
    haveI : Module.Flat R (Ω) := Module.Flat.trans R (FractionRing R) (Ω)

    let ρK : Ω ⊗[R] B₁ →ₐc[Ω] Ω ⊗[R] B₀ :=
      Bialgebra.TensorProduct.map (BialgHom.id (Ω) (Ω)) ρ
    have hρK : Function.Surjective ρK := by
      change Function.Surjective (ρK : Ω ⊗[R] B₁ →ₐ[Ω] Ω ⊗[R] B₀)
      rw [show (ρK : Ω ⊗[R] B₁ →ₐ[Ω] Ω ⊗[R] B₀) =
        Algebra.TensorProduct.map (AlgHom.id (Ω) (Ω)) (ρ : B₁ →ₐ[R] B₀) from
        Bialgebra.TensorProduct.map_toAlgHom _ _]
      exact Algebra.TensorProduct.map_surjective _ _ Function.surjective_id hρ
    have hsub := HopfAlgebra.hopfKer_baseChange_toSubmodule_eq_range_baseChange (Ω) ρ
    let j : Ω ⊗[R] ↥(HopfAlgebra.hopfKer ρ) →ₐ[Ω] Ω ⊗[R] B₁ :=
      Algebra.TensorProduct.map (AlgHom.id (Ω) (Ω)) (HopfAlgebra.hopfKer ρ).val
    have hjfun : ∀ z, j z = ((HopfAlgebra.hopfKer ρ).val.toLinearMap.baseChange (Ω)) z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul c x => rfl
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    have hjinj : Function.Injective j := by
      have h : Function.Injective ((HopfAlgebra.hopfKer ρ).val.toLinearMap.baseChange (Ω)) :=
        Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
      intro x y hxy
      exact h (by rw [← hjfun, ← hjfun]; exact hxy)
    have hjrange : j.range = HopfAlgebra.hopfKer ρK := by
      apply Subalgebra.ext
      intro x
      rw [AlgHom.mem_range, ← Subalgebra.mem_toSubmodule, hsub, LinearMap.mem_range]
      constructor
      · rintro ⟨y, rfl⟩; exact ⟨y, (hjfun y).symm⟩
      · rintro ⟨y, rfl⟩; exact ⟨y, hjfun y⟩
    let e : Ω ⊗[R] ↥(HopfAlgebra.hopfKer ρ) ≃ₐ[Ω] ↥(HopfAlgebra.hopfKer ρK) :=
      (AlgEquiv.ofInjective j hjinj).trans (Subalgebra.equivOfEq _ _ hjrange)
    have he : ∀ x, ((e x : ↥(HopfAlgebra.hopfKer ρK)) : Ω ⊗[R] B₁) = j x := fun x => rfl

    let νbar : Ω ⊗[R] ↥(HopfAlgebra.hopfKer ρ) →ₐ[Ω] Ω :=
      Algebra.TensorProduct.lift (AlgHom.id (Ω) (Ω)) ν.ofConv (fun _ _ => Commute.all _ _)
    obtain ⟨ν₁, hν₁⟩ := HopfAlgebra.exists_algHom_comp_hopfKer_val_eq_of_surjective_of_isAlgClosed ρK hρK
      (Ω) (νbar.comp e.symm.toAlgHom)
    let g : B₁ →ₐ[R] Ω := (ν₁.restrictScalars R).comp Algebra.TensorProduct.includeRight
    have hgval : g.comp (HopfAlgebra.hopfKer ρ).val = ν.ofConv := by
      ext x
      change ν₁ ((1 : Ω) ⊗ₜ[R] ((HopfAlgebra.hopfKer ρ).val x)) = ν.ofConv x
      have h1x : (1 : Ω) ⊗ₜ[R] ((HopfAlgebra.hopfKer ρ).val x) =
          (HopfAlgebra.hopfKer ρK).val (e ((1 : Ω) ⊗ₜ[R] x)) := by
        change _ = ((e ((1 : Ω) ⊗ₜ[R] x) : ↥(HopfAlgebra.hopfKer ρK)) : Ω ⊗[R] B₁)
        rw [he]
        rfl
      rw [h1x, ← AlgHom.comp_apply, hν₁, AlgHom.comp_apply]
      change νbar (e.symm (e ((1 : Ω) ⊗ₜ[R] x))) = _
      rw [AlgEquiv.symm_apply_apply]
      change Algebra.TensorProduct.lift _ _ _ ((1 : Ω) ⊗ₜ[R] x) = _
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    refine ⟨WithConv.toConv (g.comp (π₁ : H →ₐ[R] B₁)), (hpts₁ _).mp ⟨g, rfl⟩, ?_⟩
    rw [hr _ ((hpts₁ _).mp ⟨g, rfl⟩) g rfl, hgval, WithConv.toConv_ofConv]

end S_HopfAlgebra_exists_restriction_points_hopfKer_mul_and_eq_one_iff_and_surjective_of_isAlgClosed
end P2MW
export P2MW.S_HopfAlgebra_exists_restriction_points_hopfKer_mul_and_eq_one_iff_and_surjective_of_isAlgClosed (solution)
