-- Prove2me | solution 1 for GlobalTheory.CMLattice.exists_basis_of_cmType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:34:40.926641+00:00
-- url     : https://prove2.me/submissions/b7fc57a1-9521-4c92-a9ff-a3dbb95f51b3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
import Theorems.Thm_GlobalTheory_CMLattice_finrank_eq_two_mul_card
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
import Theorems.Thm_GlobalTheory_CMLattice_eq_top_of_forall_embAll_mem
import Theorems.Thm_GlobalTheory_CMLattice_embAll_mem_of_span
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.CMLattice
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMLattice
theorem _root_.solution (Ψ : Finset (E →+* ℂ))
    (h : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (r : ℕ)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG)
    (hΛ : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) :
    ∃ b : Module.Basis (Fin (2 * (Ψ.card * r))) ℝ (Ψ → Fin r → ℂ),
      ∀ y, y ∈ Submodule.span ℤ (Set.range b) ↔ ∃ v ∈ Λ, embAll Ψ r v = y := by
  classical
  let L : Submodule ℤ (Fin r → E) := Λ.restrictScalars ℤ
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hfg
  haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
  haveI : Module.Finite ℤ L := inferInstanceAs (Module.Finite ℤ Λ)
  haveI : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  let c := Module.Free.chooseBasis ℤ L
  let w : Module.Free.ChooseBasisIndex ℤ L → (Fin r → E) := fun i => (c i : Fin r → E)
  have hw : Submodule.span ℤ (Set.range w) = L := by
    have : Set.range w = L.subtype '' Set.range c := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, c.span_eq, Submodule.map_subtype_top]
  have hli : LinearIndependent ℤ w := c.linearIndependent.map' L.subtype L.ker_subtype
  have hliQ : LinearIndependent ℚ w := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hli
  have hle : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) ≤ 2 * (Ψ.card * r) := by
    have := hliQ.fintype_card_le_finrank
    rw [Module.finrank_pi_fintype, Finset.sum_const, finrank_eq_two_mul_card Ψ h] at this
    simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
    calc _ ≤ _ := this
      _ = _ := by ring
  have hZ : Submodule.span ℤ (Set.range (embAll Ψ r ∘ w)) = L.map (embAll Ψ r) := by
    rw [Set.range_comp, ← Submodule.map_span, hw]
  have htop : Submodule.span ℝ (Set.range (embAll Ψ r ∘ w)) = ⊤ := by
    refine eq_top_of_forall_embAll_mem Ψ (fun τ => (h τ).1) r _
      (embAll_mem_of_span Ψ r Λ hΛ _ fun v hv => ?_)
    have : embAll Ψ r v ∈ Submodule.span ℤ (Set.range (embAll Ψ r ∘ w)) := by
      rw [hZ]; exact Submodule.mem_map_of_mem hv
    exact Submodule.span_subset_span ℤ ℝ _ this
  have hfr : Module.finrank ℝ (Ψ → Fin r → ℂ) = 2 * (Ψ.card * r) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]; ring
  have hge : 2 * (Ψ.card * r) ≤ Fintype.card (Module.Free.ChooseBasisIndex ℤ L) := by
    rw [← hfr, ← finrank_top, ← htop]
    exact finrank_range_le_card _
  have hcard := le_antisymm hle hge
  let b := basisOfTopLeSpanOfCardEqFinrank (embAll Ψ r ∘ w) htop.ge (hcard.trans hfr.symm)
  refine ⟨b.reindex (Fintype.equivFinOfCardEq hcard), fun y => ?_⟩
  rw [Module.Basis.range_reindex, coe_basisOfTopLeSpanOfCardEqFinrank, hZ]
  rfl
end GlobalTheory.CMLattice
