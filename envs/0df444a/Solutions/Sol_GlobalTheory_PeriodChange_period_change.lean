-- Prove2me | solution 1 for GlobalTheory.PeriodChange.period_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:38:27.820488+00:00
-- url     : https://prove2.me/submissions/2340c376-0595-489f-9de5-b550bdaf02d1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ChangeOfNormalisation
import Theorems.Thm_GlobalTheory_PeriodChange_swap_mem_symplectic
import Theorems.Thm_GlobalTheory_PeriodChange_change_of_normalisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.PeriodChange
open Complex Matrix NumberField in
private theorem addMonoidHom_eq_matrix_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] {g : ℕ}
    (Q : (ι → ℤ) →+ (Fin g → ℂ)) (x : ι → ℤ) :
    Q x = (Matrix.of fun i u => Q (Pi.single u 1) i) *ᵥ fun u => (x u : ℂ) := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  funext i
  simp only [Finset.sum_apply, mulVec, dotProduct, of_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hs : Pi.single u (x u) = x u • (Pi.single u 1 : ι → ℤ) := by
    ext v; by_cases hv : v = u <;> simp [hv]
  rw [hs, map_zsmul, Pi.smul_apply, zsmul_eq_mul, mul_comm]
end GlobalTheory.PeriodChange
end

set_option autoImplicit false
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChange
open Complex Matrix NumberField
namespace GlobalTheory.PeriodChange
namespace _root_.GlobalTheory.PeriodChange
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (gam : D.La ≃ₗ[𝓞 E] D.La) (N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (P P' : D.La →+ (Fin g → ℂ)) (h h' τ τ' : Matrix (Fin g) (Fin g) ℂ), (∀ a b, D.EF (bas a) (bas b) = -_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd a b) → (∀ a b, D.EF (gam a) (gam b) = D.EF a b) → (∀ u v, N u v = bas.symm (gam (bas (Pi.single v 1))) u) → (∀ a, P' a = P (gam a)) → (∀ k, h *ᵥ P (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h *ᵥ P (bas (Pi.single (Sum.inr k) 1)) = τ *ᵥ Pi.single k 1) → (∀ k, h' *ᵥ P' (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h' *ᵥ P' (bas (Pi.single (Sum.inr k) 1)) = τ' *ᵥ Pi.single k 1) → τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → τ' ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → IsUnit h.det → ∃ γ ∈ Matrix.symplecticGroup (Fin g) ℤ, γ = Matrix.fromBlocks N.toBlocks₂₂ᵀ N.toBlocks₁₂ᵀ N.toBlocks₂₁ᵀ N.toBlocks₁₁ᵀ ∧ τ' = _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.spAct γ τ ∧ h' = ((_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut γ τ)⁻¹)ᵀ * h ∧ h.det = (_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut γ τ).det * h'.det := by
  intro E _ _ _ H D g bas gam N P P' h h' τ τ' hEF hgam hNdef hP' hnorm hnorm' hτ hτ' hu
  have hτs : τ.IsSymm := by unfold _root_.ReciprocityTheory.PTheta.SiegelH at hτ; exact hτ.1
  have hτs' : τ'.IsSymm := by unfold _root_.ReciprocityTheory.PTheta.SiegelH at hτ'; exact hτ'.1
  have hNv : ∀ a, bas (N *ᵥ a) = gam (bas a) := by
    intro a
    let f₁ : (Fin g ⊕ Fin g → ℤ) →+ (Fin g ⊕ Fin g → ℤ) := (Matrix.mulVecLin N).toAddMonoidHom
    let f₂ : (Fin g ⊕ Fin g → ℤ) →+ (Fin g ⊕ Fin g → ℤ) :=
      bas.symm.toLinearMap.toAddMonoidHom.comp
        (gam.toAddEquiv.toAddMonoidHom.comp bas.toLinearMap.toAddMonoidHom)
    have hf : f₁ = f₂ := by
      refine AddMonoidHom.functions_ext _ _ _ fun v x => ?_
      have hs : Pi.single v x = x • (Pi.single v 1 : Fin g ⊕ Fin g → ℤ) := by
        ext u; by_cases hu : u = v <;> simp [hu]
      rw [hs, map_zsmul, map_zsmul]
      congr 1
      funext u
      simp [f₁, f₂, hNdef, mulVec_single_one]
    have := DFunLike.congr_fun hf a
    change N *ᵥ a = bas.symm (gam (bas a)) at this
    rw [this, LinearEquiv.apply_symm_apply]
  have hγ := _root_.GlobalTheory.PeriodChange.swap_mem_symplectic N fun a b => by
    have := hEF (N *ᵥ a) (N *ᵥ b)
    rw [hNv, hNv, hgam, hEF] at this
    exact (neg_inj.mp this).symm
  have hcol : ∀ v, h *ᵥ P' (bas (Pi.single v 1)) =
      fun i => (N (Sum.inl i) v : ℂ) + ∑ j, τ i j * N (Sum.inr j) v := by
    intro v
    have hPb : ∀ x, P (bas x) =
        (Matrix.of fun i u => P (bas (Pi.single u 1)) i) *ᵥ fun u => (x u : ℂ) :=
      fun x => addMonoidHom_eq_matrix_mulVec (P.comp bas.toLinearMap.toAddMonoidHom) x
    rw [hP', ← hNv, hPb, mulVec_mulVec]
    funext i
    have hc : ∀ u, (h * Matrix.of fun i u => P (bas (Pi.single u 1)) i) i u
        = (h *ᵥ P (bas (Pi.single u 1))) i := by
      intro u; simp [mul_apply, mulVec, dotProduct]
    rw [mulVec, dotProduct, Fintype.sum_sum_type]
    simp only [hc, (hnorm _).1, (hnorm _).2]
    simp [mulVec_single_one, Pi.single_apply]
  let A₀ : Matrix (Fin g) (Fin g) ℂ :=
    N.toBlocks₁₁.map (fun x : ℤ => (x : ℂ)) + τ * N.toBlocks₂₁.map (fun x : ℤ => (x : ℂ))
  let B₀ : Matrix (Fin g) (Fin g) ℂ :=
    N.toBlocks₁₂.map (fun x : ℤ => (x : ℂ)) + τ * N.toBlocks₂₂.map (fun x : ℤ => (x : ℂ))
  have hAL : h * (Matrix.of fun i k => P' (bas (Pi.single (Sum.inl k) 1)) i) = A₀ := by
    ext i k
    have := congrFun (hcol (Sum.inl k)) i
    simp only [mulVec, dotProduct] at this
    simp [A₀, mul_apply, this, toBlocks₁₁, toBlocks₂₁]
  have hBR : h * (Matrix.of fun i k => P' (bas (Pi.single (Sum.inr k) 1)) i) = B₀ := by
    ext i k
    have := congrFun (hcol (Sum.inr k)) i
    simp only [mulVec, dotProduct] at this
    simp [B₀, mul_apply, this, toBlocks₁₂, toBlocks₂₂]
  have hL1 : h' * (Matrix.of fun i k => P' (bas (Pi.single (Sum.inl k) 1)) i) = 1 := by
    ext i k
    have := congrFun (hnorm' k).1 i
    simp only [mulVec, dotProduct] at this
    simp [mul_apply, this, one_apply, Pi.single_apply]
  have hRτ : h' * (Matrix.of fun i k => P' (bas (Pi.single (Sum.inr k) 1)) i) = τ' := by
    ext i k
    have := congrFun (hnorm' k).2 i
    simp only [mulVec, dotProduct] at this
    simp [mul_apply, this, Pi.single_apply]
  obtain ⟨e₁, e₂, e₃⟩ :=
    _root_.GlobalTheory.PeriodChange.change_of_normalisation h h' τ' A₀ B₀ _ _ hAL hBR hL1 hRτ hτs' hu
  have hj : _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut (Matrix.fromBlocks N.toBlocks₂₂ᵀ N.toBlocks₁₂ᵀ N.toBlocks₂₁ᵀ N.toBlocks₁₁ᵀ) τ =
      A₀ᵀ := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.cMat
    simp [A₀, fromBlocks_map, transpose_add, transpose_mul, hτs.eq, transpose_map, add_comm]
  refine ⟨_, hγ, rfl, ?_, ?_, ?_⟩
  · unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.spAct
    rw [hj, e₁]
    congr 1
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.cMat
    simp [B₀, fromBlocks_map, transpose_add, transpose_mul, hτs.eq, transpose_map, add_comm]
  · rw [hj]; exact e₂
  · rw [hj]; exact e₃
end _root_.GlobalTheory.PeriodChange
end GlobalTheory.PeriodChange
