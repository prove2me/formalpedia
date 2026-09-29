-- Prove2me | solution 1 for InfiniteGalois.nonempty_continuousMulEquiv_fixedField_ker
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T20:24:48.842762+00:00
-- url     : https://prove2.me/submissions/d74c5396-3d9e-432e-9615-deead68ec88f

import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Homeomorph.Lemmas

open IntermediateField

theorem solution {k K : Type*} [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [T2Space Γ]
    (φ : Gal(K/k) →* Γ) (hφ : Continuous φ) (hs : Function.Surjective φ) :
    IsGalois k (fixedField φ.ker) ∧ Nonempty (Gal(fixedField φ.ker/k) ≃ₜ* Γ) := by
  have hcl : IsClosed (φ.ker : Set Gal(K/k)) := by
    exact (isClosed_singleton (x := (1 : Γ))).preimage hφ
  let H : ClosedSubgroup Gal(K/k) := ⟨φ.ker, hcl⟩
  have : (H : Subgroup Gal(K/k)).Normal := φ.normal_ker
  refine ⟨inferInstance, ?_⟩
  let e1 := InfiniteGalois.normalAutEquivQuotient H
  let e2 := QuotientGroup.quotientKerEquivOfSurjective φ hs
  let f : Gal(fixedField φ.ker/k) ≃* Γ := e1.symm.trans e2
  have hf : ∀ σ : Gal(K/k), f (AlgEquiv.restrictNormalHom (fixedField φ.ker) σ) = φ σ := by
    intro σ
    have : e1.symm (AlgEquiv.restrictNormalHom (fixedField φ.ker) σ) = (QuotientGroup.mk σ) := by
      rw [MulEquiv.symm_apply_eq]; rfl
    simp only [f, MulEquiv.trans_apply, this]
    rfl
  have hr := InfiniteGalois.restrictNormalHom_continuous (fixedField φ.ker)
  have hrs := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := fixedField φ.ker) K
  have hq := (hr.isClosedMap).isQuotientMap hr hrs
  have hfc : Continuous f := by
    rw [hq.continuous_iff]
    have : (f ∘ AlgEquiv.restrictNormalHom (fixedField φ.ker)) = φ := funext hf
    rw [this]; exact hφ
  exact ⟨{ f with
    continuous_toFun := hfc
    continuous_invFun := (hfc.homeoOfEquivCompactToT2 (f := f.toEquiv)).symm.continuous }⟩
