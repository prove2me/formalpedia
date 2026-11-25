-- Prove2me | solution 1 for GlobalTheory.SW.MinkowskiProductBounds.basis_many
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:18:19.487738+00:00
-- url     : https://prove2.me/submissions/374c40a7-3467-43b5-aa19-7536a78d5341

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_basis_one
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.MinkowskiProductBounds
open Module Submodule
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
namespace GlobalTheory.SW.MinkowskiProductBounds
theorem _root_.solution (h : IsType Ψ) (m : ℕ) :
    ∃ b : Basis (Σ _ : Fin m, Free.ChooseBasisIndex ℤ (𝓞 E)) ℝ (Ψ → Fin m → ℂ),
    ∀ x, x ∈ span ℤ (Set.range b) ↔
      ∃ v : Fin m → E, (∀ a, IsIntegral ℤ (v a)) ∧ x = fun τ a => τ.1 (v a) := by
  obtain ⟨b, hb⟩ := basis_one h
  let e : (Fin m → Ψ → ℂ) ≃ₗ[ℝ] (Ψ → Fin m → ℂ) :=
    { toFun := fun x τ a => x a τ, invFun := fun x a τ => x τ a, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  refine ⟨(Pi.basis fun _ => b).map e, fun x => ?_⟩
  have : x ∈ span ℤ (Set.range ((Pi.basis fun _ : Fin m => b).map e)) ↔
      ∀ a, (fun τ => x τ a) ∈ span ℤ (Set.range b) := by
    simp only [Basis.mem_span_iff_repr_mem, Sigma.forall]
    rfl
  rw [this]
  simp only [hb]
  constructor
  · intro hx
    choose v hv hx using hx
    exact ⟨v, hv, by ext τ a; exact congrFun (hx a) τ⟩
  · rintro ⟨v, hv, rfl⟩ a
    exact ⟨v a, hv a, rfl⟩
end GlobalTheory.SW.MinkowskiProductBounds
