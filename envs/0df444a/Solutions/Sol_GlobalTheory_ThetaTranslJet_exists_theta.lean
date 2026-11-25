-- Prove2me | solution 1 for GlobalTheory.ThetaTranslJet.exists_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:40:00.613391+00:00
-- url     : https://prove2.me/submissions/ee684517-10ed-41f9-8fef-cdee78349739

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImFormApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaFunctionIsogenyRestriction
import Theorems.Thm_GlobalTheory_ThetaTranslJet_exists_coc
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_reindex
import Theorems.Thm_GlobalTheory_ThetaExist_exists_sec_ne_zero
import Theorems.Thm_GlobalTheory_ThetaGauss_transl_apply
import Theorems.Thm_GlobalTheory_ThetaJet_exists_sec_ne_zero
import Theorems.Thm_GlobalTheory_ThetaTranslSpan_exists_im_eq_lattice
import Theorems.Thm_GlobalTheory_ThetaTranslSpan_herm_swap
import Theorems.Thm_GlobalTheory_ThetaTranslSpan_span_eq_top
import Theorems.Thm_GlobalTheory_UpperHalfImaginaryForm_exists_coc
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_zero
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.ThetaGauss.transl_apply
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open Matrix ReciprocityTheory.ChartRestriction.G.I2
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaTranslJet
variable {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
open scoped MatrixOrder
namespace GlobalTheory.ThetaTranslJet
theorem _root_.solution (hH : Hm.PosDef) (Λ : AddSubgroup (Fin g → ℂ)) [hd : DiscreteTopology Λ]
    (hΛ : ∀ v, (∀ a ∈ Λ, ∃ k : ℤ, (star v ⬝ᵥ Hm.mulVec a).im = k) ↔ v ∈ Λ) :
    ∃ χ θ : (Fin g → ℂ) → ℂ, Differentiable ℂ θ ∧ θ ≠ 0 ∧ (∀ a ∈ Λ, ‖χ a‖ = 1) ∧
      ∀ a ∈ Λ, ∀ z, θ (z + a) = χ a * Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec z) +
        Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a)) * θ z := by
  let L : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule Λ
  haveI hL : DiscreteTopology L := hd
  have hsp : Submodule.span ℝ (L : Set (Fin g → ℂ)) = ⊤ :=
    ThetaTranslSpan.span_eq_top hH Λ fun v => (hΛ v).1
  haveI : IsZLattice ℝ L := ⟨hsp⟩
  obtain ⟨B, hB, hY⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    hH.isStrictlyPositive
  let Φ : (Fin g → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin g) :=
    (B.toLinearEquiv' hB.invertible).trans (WithLp.linearEquiv 2 ℂ _).symm
  have hΦ : ∀ v w, Hf (Φ v) (Φ w) = star w ⬝ᵥ Hm.mulVec v := fun v w => by
    have : Hf (Φ v) (Φ w) = star (B.mulVec w) ⬝ᵥ B.mulVec v := by
      rw [dotProduct_comm]; rfl
    rw [this, hY, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, star_eq_conjTranspose]
  let b₀ := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  let b₁ := b₀.map (Φ.restrictScalars ℝ)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) =
      Fintype.card (Fin (2 * Fintype.card (Fin g))) := by
    rw [← Module.finrank_eq_card_basis b₁, finrank_real_of_complex]
    simp
  let b := b₁.reindex (Fintype.equivOfCardEq hcard)
  have hb : ∀ z, Φ z ∈ lat b ↔ z ∈ Λ := fun z => by
    change _ ↔ z ∈ L
    rw [← (Module.Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ, lat, Module.Basis.range_reindex]
    simp only [Module.Basis.mem_span_iff_repr_mem, b₁, Module.Basis.map_repr]
    simp [b₀]
  have hsk : ∀ z u : Fin g → ℂ, (star u ⬝ᵥ Hm.mulVec z).im = -(star z ⬝ᵥ Hm.mulVec u).im :=
    fun z u => by rw [ThetaTranslSpan.herm_swap hH z u]; simp
  obtain ⟨Y, hYb, hC⟩ := exists_coc b (fun x y hx hy => by
    obtain ⟨x, rfl⟩ := Φ.surjective x
    obtain ⟨y, rfl⟩ := Φ.surjective y
    rw [hΦ]
    exact (hΛ y).2 ((hb y).1 hy) x ((hb x).1 hx)) (fun φ => by
    let p : L →+ lat b := (Φ.toLinearMap.toAddMonoidHom.comp L.subtype.toAddMonoidHom).codRestrict
      (lat b) fun a => (hb _).2 a.2
    obtain ⟨y, hy⟩ := ThetaTranslSpan.exists_im_eq_lattice hH L hsp
      (-((Int.castAddHom ℝ).comp (φ.comp p)).toIntLinearMap)
    refine ⟨Φ y, (hb y).2 ((hΛ y).1 fun a ha => ⟨-φ (p ⟨a, ha⟩), by rw [hy ⟨a, ha⟩]; simp⟩), ?_⟩
    rintro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := Φ.surjective x
    rw [hΦ, hsk, hy ⟨x, (hb x).1 hx⟩]
    simp only [LinearMap.neg_apply, neg_neg]
    rfl)
  obtain ⟨s, ⟨hs, hs'⟩, hs0⟩ := ThetaExist.exists_sec_ne_zero Y hC
  refine ⟨fun a => Y.ka (Φ a), fun z => s (Φ z),
    hs.comp Φ.toContinuousLinearEquiv.differentiable, fun h => hs0 ?_,
    fun a ha => Y.ka_abs _ (hYb ▸ (hb a).2 ha), fun a ha z => ?_⟩
  · funext x
    obtain ⟨x, rfl⟩ := Φ.surjective x
    exact congrFun h x
  · simp only [map_add]
    rw [hs' _ (hYb ▸ (hb a).2 ha), hΦ, hΦ]
    congr 3
    push_cast; ring
end GlobalTheory.ThetaTranslJet
