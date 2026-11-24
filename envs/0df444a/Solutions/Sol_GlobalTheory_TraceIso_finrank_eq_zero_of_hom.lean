-- Prove2me | solution 1 for GlobalTheory.TraceIso.finrank_eq_zero_of_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:38:51.573087+00:00
-- url     : https://prove2.me/submissions/056461a5-66d2-422c-8395-a88a85fcf7c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyLinearEquivOfCharpolyEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TraceIso
open Module
variable {k A : Type} [Field k] [Ring A] [Algebra k A]
variable {V W : Type} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
namespace GlobalTheory.TraceIso
theorem _root_.solution [CharZero k] [FiniteDimensional k V] [FiniteDimensional k W]
    [IsSemisimpleModule A V] [IsSemisimpleModule A W] (h : ∀ a : A, tr k V a = tr k W a)
    (h₁ : ∀ f : V →ₗ[A] W, f = 0) (h₂ : ∀ f : W →ₗ[A] V, f = 0) : finrank k V = 0 := by
  classical
  let p : End A (V × W) := (LinearMap.inl A V W).comp (LinearMap.fst A V W)
  let F : End (End A (V × W)) (V × W) :=
    { toFun := p
      map_add' := p.map_add
      map_smul' := by
        rintro φ ⟨v, w⟩
        have e₁ := LinearMap.congr_fun
          (h₁ ((LinearMap.snd A V W).comp (φ.comp (LinearMap.inl A V W)))) v
        have e₂ := LinearMap.congr_fun
          (h₂ ((LinearMap.fst A V W).comp (φ.comp (LinearMap.inr A V W)))) w
        have e₃ : φ (v, w) = φ (v, 0) + φ (0, w) := by rw [← map_add]; simp
        simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply, LinearMap.snd_apply,
          LinearMap.fst_apply, LinearMap.zero_apply] at e₁ e₂
        change ((φ (v, w)).1, (0 : W)) = φ (v, 0)
        rw [e₃]
        ext
        · simp [e₂]
        · exact e₁.symm }
  let b := Module.finBasis k (V × W)
  haveI : IsSemisimpleModule A (V × W) := by
    have hs := IsSemisimpleModule.sup (IsSemisimpleModule.range (LinearMap.inl A V W))
      (IsSemisimpleModule.range (LinearMap.inr A V W))
    rw [LinearMap.sup_range_inl_inr] at hs
    exact IsSemisimpleModule.congr Submodule.topEquiv.symm
  obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image b)
  have hall : (p.restrictScalars k) = Algebra.lsmul k k (V × W) r :=
    b.ext fun i => hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hV : Algebra.lsmul k k V r = 1 := by
    ext v
    exact (congrArg Prod.fst (LinearMap.congr_fun hall (v, 0))).symm
  have hW : Algebra.lsmul k k W r = 0 := by
    ext w
    exact (congrArg Prod.snd (LinearMap.congr_fun hall (0, w))).symm
  have := h r
  unfold tr at this
  rw [hV, hW, LinearMap.trace_one, map_zero] at this
  exact_mod_cast this
end GlobalTheory.TraceIso
