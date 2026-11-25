-- Prove2me | solution 1 for GlobalTheory.UnitCocycle.exists_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:59:30.19018+00:00
-- url     : https://prove2.me/submissions/2f3479f5-3b13-4259-a0e5-d833f1ca2bad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueBaseChangeEqOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyTrivialUnitCocycleFaithfullyFlat
import Theorems.Thm_GlobalTheory_UnitCocycle_exists_local_tensor
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_SymAlg_baseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.SymAlg.baseChangeEquiv_tmul



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TensorProduct
open GlobalTheory
open GlobalTheory.UnitCocycle
namespace GlobalTheory.UnitCocycle
theorem _root_.solution (R B C D : CommRingCat.{0}) (f : R ⟶ B) (j₁ j₂ : B ⟶ C) (d₁₂ d₂₃ d₁₃ : C ⟶ D)
    (hC : IsPushout f f j₁ j₂) (hD : IsPushout j₂ j₁ d₁₂ d₂₃) (h₁ : j₁ ≫ d₁₃ = j₁ ≫ d₁₂)
    (h₂ : j₂ ≫ d₁₃ = j₂ ≫ d₂₃) (hf : f.hom.FaithfullyFlat) (c : Cˣ)
    (hc : d₁₃.hom (c : C) = d₁₂.hom (c : C) * d₂₃.hom (c : C)) (P : Ideal R) (hP : P.IsPrime) :
    ∃ s : R, s ∉ P ∧ ∃ x y : B, x * y = f.hom s ∧ j₂.hom x = (c : C) * j₁.hom x := by
  letI : Algebra R B := f.hom.toAlgebra
  haveI : Module.FaithfullyFlat R B := hf
  have hT := CommRingCat.isPushout_tensorProduct R B B
  let e : C ≅ CommRingCat.of (B ⊗[R] B) := hC.isoIsPushout _ _ hT
  have e1 : j₁ ≫ e.hom = _ := hC.inl_isoIsPushout_hom _ _ hT
  have e2 : j₂ ≫ e.hom = _ := hC.inr_isoIsPushout_hom _ _ hT
  have e1' : ∀ x : B, e.hom.hom (j₁.hom x) = x ⊗ₜ[R] (1 : B) := fun x =>
    congrArg (fun q => q.hom x) e1
  have e2' : ∀ x : B, e.hom.hom (j₂.hom x) = (1 : B) ⊗ₜ[R] x := fun x =>
    congrArg (fun q => q.hom x) e2
  let n₁₂ : C ⟶ CommRingCat.of (B ⊗[R] (B ⊗[R] B)) := e.hom ≫ CommRingCat.ofHom (m₁₂ R B).toRingHom
  let n₁₃ : C ⟶ CommRingCat.of (B ⊗[R] (B ⊗[R] B)) := e.hom ≫ CommRingCat.ofHom (m₁₃ R B).toRingHom
  let n₂₃ : C ⟶ CommRingCat.of (B ⊗[R] (B ⊗[R] B)) := e.hom ≫ CommRingCat.ofHom (m₂₃ R B).toRingHom
  have w : j₂ ≫ n₁₂ = j₁ ≫ n₂₃ := by
    ext x
    change m₁₂ R B (e.hom.hom (j₂.hom x)) = m₂₃ R B (e.hom.hom (j₁.hom x))
    rw [e1', e2']
    simp [m₁₂, m₂₃]
  let ψ := hD.desc n₁₂ n₂₃ w
  have p12 : d₁₂ ≫ ψ = n₁₂ := hD.inl_desc _ _ _
  have p23 : d₂₃ ≫ ψ = n₂₃ := hD.inr_desc _ _ _
  have p13 : d₁₃ ≫ ψ = n₁₃ := by
    apply hC.hom_ext
    · rw [← Category.assoc, h₁, Category.assoc, p12]
      ext x
      change m₁₂ R B (e.hom.hom (j₁.hom x)) = m₁₃ R B (e.hom.hom (j₁.hom x))
      rw [e1']
      simp [m₁₂, m₁₃, Algebra.TensorProduct.one_def]
    · rw [← Category.assoc, h₂, Category.assoc, p23]
      ext x
      change m₂₃ R B (e.hom.hom (j₂.hom x)) = m₁₃ R B (e.hom.hom (j₂.hom x))
      rw [e2']
      simp [m₂₃, m₁₃]
  have hco : m₁₃ R B (e.hom.hom c) = m₁₂ R B (e.hom.hom c) * m₂₃ R B (e.hom.hom c) := by
    have h' := congrArg ψ.hom hc
    rw [map_mul] at h'
    have q12 : ψ.hom (d₁₂.hom c) = m₁₂ R B (e.hom.hom c) := congrArg (fun q => q.hom (c : C)) p12
    have q13 : ψ.hom (d₁₃.hom c) = m₁₃ R B (e.hom.hom c) := congrArg (fun q => q.hom (c : C)) p13
    have q23 : ψ.hom (d₂₃.hom c) = m₂₃ R B (e.hom.hom c) := congrArg (fun q => q.hom (c : C)) p23
    rwa [q12, q13, q23] at h'
  obtain ⟨s, hs, x, y, hxy, hx⟩ :=
    exists_local_tensor (c.isUnit.map e.hom.hom) hco P hP.ne_top
  refine ⟨s, hs, x, y, hxy, ?_⟩
  apply e.commRingCatIsoToRingEquiv.injective
  change e.hom.hom _ = e.hom.hom _
  rw [map_mul, e1', e2']
  exact hx
end GlobalTheory.UnitCocycle
