-- Prove2me | solution 1 for GlobalTheory.SmGL.Stages.stage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:17:09.911874+00:00
-- url     : https://prove2.me/submissions/0b9e1dfa-1c0b-4ee6-b6ce-996a0a3a5117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyInv
import Theorems.Thm_GlobalTheory_SmGL_Stages_trans_ind
import Theorems.Thm_GlobalTheory_SmGL_Stages_tensor_inj
import Theorems.Thm_GlobalTheory_SmGL_Stages_tensor_surj
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Topology Filter
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.Stages
variable {F G M W X Y Z : Type} [Field F] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group M] [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup W] [Module F W]
  [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y] [AddCommGroup Z] [Module F Z]
namespace GlobalTheory.SmGL.Stages
theorem _root_.solution {Q R : Subgroup G} (hRQ : R ≤ Q) {P : Subgroup M} (ℓ : Q →* M) (s : M →* Q)
    (hs : Continuous s) (hls : ∀ m, ℓ (s m) = m) (hR : ∀ q : Q, (q : G) ∈ R ↔ ℓ q ∈ P)
    {K : Set M} (hK : IsCompact K) (hPK : ∀ m, ∃ p : P, ∃ c ∈ K, m = p * c)
    (σ : Representation F P W) (τ : Representation F Q X) (hτ : ∀ᶠ u in 𝓝 (1 : M), τ (s u) = 1)
    (Θ : Representation F Q Y) (j : Y ≃ₗ[F] smoothPart (ind P σ) ⊗[F] X)
    (hj : ∀ q y, j (Θ q y) = TensorProduct.map (smInd P σ (ℓ q)) (τ q) (j y))
    (ρ : Representation F R Z) (i : W ⊗[F] X ≃ₗ[F] Z)
    (hi : ∀ (q : Q) (h : (q : G) ∈ R) z,
      ρ ⟨q, h⟩ (i z) = i (TensorProduct.map (σ ⟨ℓ q, (hR q).1 h⟩) (τ q) z)) :
    Nonempty ((smInd Q Θ).Equiv (smInd R ρ)) := by
  have hval : ∀ (q : Q) (y : smoothPart (ind P σ) ⊗[F] X),
      (evalAt σ 1).rTensor X (TensorProduct.map (smInd P σ (ℓ q)) (τ q) y) =
        (τ q).lTensor W ((evalAt σ (ℓ q)).rTensor X y) := fun q y => by
    induction y with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul f x =>
      simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
      congr 1
      exact congrArg f.1.1 (one_mul _)
  have hmul : ∀ (q q' : Q) (z : W ⊗[F] X),
      (τ q).lTensor W ((τ q').lTensor W z) = (τ (q * q')).lTensor W z := fun q q' z => by
    rw [map_mul, ← LinearMap.lTensor_comp_apply]; rfl
  have hone : ∀ z : W ⊗[F] X, (τ 1).lTensor W z = z := fun z => by
    rw [map_one, Module.End.one_eq_id, LinearMap.lTensor_id]; rfl
  refine trans_ind hRQ Θ ρ (i.toLinearMap ∘ₗ (evalAt σ 1).rTensor X ∘ₗ j.toLinearMap)
    (fun r y => ?_) (fun y hy => ?_) (fun φ h1 h2 => ?_)
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hj, hval, hi ⟨r, hRQ r.2⟩ r.2]
    congr 1
    generalize j y = z
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul f x =>
      simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
      congr 1
      exact (congrArg f.1.1 (mul_one _).symm).trans (f.1.2 ⟨_, (hR ⟨r, hRQ r.2⟩).1 r.2⟩ 1)
  · rw [← j.map_eq_zero_iff]
    refine tensor_inj σ _ fun m => ?_
    have := hy (s m)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, i.map_eq_zero_iff] at this
    rw [hj, hval, hls] at this
    rw [← hone ((evalAt σ m).rTensor X _), ← inv_mul_cancel (s m), ← hmul, this, map_zero]
  · have h1' : ∀ (q : Q) (h : ℓ q ∈ P) (q' : Q), i.symm (φ (q * q')) =
        (σ ⟨ℓ q, h⟩).rTensor X ((τ q).lTensor W (i.symm (φ q'))) := fun q h q' => by
      rw [LinearEquiv.symm_apply_eq, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
        ← hi q ((hR q).2 h), i.apply_symm_apply]
      exact h1 ⟨q, (hR q).2 h⟩ q'
    have hcomm : ∀ (A : W →ₗ[F] W) (B : X →ₗ[F] X) z,
        B.lTensor W (A.rTensor X z) = A.rTensor X (B.lTensor W z) := fun A B z => by
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
        LinearMap.lTensor_comp_rTensor]
    obtain ⟨y, hy⟩ := tensor_surj σ hK hPK (fun m => (τ (s m)⁻¹).lTensor W (i.symm (φ (s m))))
      (fun p m => by
        rw [map_mul, h1' (s p) (by rw [hls]; exact p.2), hcomm, hmul]
        simp only [hls, mul_inv_rev, inv_mul_cancel_right])
      (by
        have hc : Tendsto s (𝓝 1) (𝓝 1) := hs.tendsto' _ _ (map_one s)
        have hc' : Tendsto (fun u : M => u⁻¹) (𝓝 1) (𝓝 1) := continuous_inv.tendsto' _ _ inv_one
        filter_upwards [hc.eventually h2, hc'.eventually hτ] with u hu hu' x
        rw [map_mul, hu, mul_inv_rev, map_mul, ← map_inv s u, hu', one_mul])
    refine ⟨j.symm y, fun q => ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hj, hval, j.apply_symm_apply, hy, hmul, ← LinearEquiv.eq_symm_apply]
    have h0 : ℓ (q * (s (ℓ q))⁻¹) = 1 := by rw [map_mul, map_inv, hls, mul_inv_cancel]
    have := h1' (q * (s (ℓ q))⁻¹) (h0 ▸ one_mem P) (s (ℓ q))
    rw [inv_mul_cancel_right, show (⟨_, h0 ▸ one_mem P⟩ : P) = 1 from Subtype.ext h0, map_one,
      Module.End.one_eq_id, LinearMap.rTensor_id] at this
    exact this.symm
end GlobalTheory.SmGL.Stages
