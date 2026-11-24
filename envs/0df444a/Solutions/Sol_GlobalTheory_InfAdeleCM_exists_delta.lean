-- Prove2me | solution 1 for GlobalTheory.InfAdeleCM.exists_delta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:33:58.424373+00:00
-- url     : https://prove2.me/submissions/d1d66fc8-b372-4dca-8070-3ade250a969d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
open GlobalTheory GlobalTheory.InfAdeleCM
variable {F : Type} [Field F] [NumberField F]
variable {E : Type} [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.InfAdeleCM
theorem _root_.solution (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (hτ : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x)) :
    ∃ δ : E, δ ≠ 0 ∧ c δ = -δ ∧ ∀ x : E, ∃ p q : F, x = algebraMap F E p + algebraMap F E q * δ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨y, hy⟩ : ∃ y, c y ≠ y := by
    by_contra h
    push_neg at h
    exact hc (AlgEquiv.ext h)
  have hcc : c (c y) = y := τ.injective (by rw [hτ, hτ, Complex.conj_conj])
  have hδ : y - c y ≠ 0 := sub_ne_zero.2 hy.symm
  have hcδ : c (y - c y) = -(y - c y) := by rw [map_sub, hcc]; ring
  refine ⟨y - c y, hδ, hcδ, ?_⟩
  generalize y - c y = δ at hδ hcδ
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h' := congrArg c hst
    have hsm : ∀ (p : F) (x : E), c (p • x) = p • c x := fun p x => by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, c.commutes]
    rw [map_add, hsm, hsm, map_one, hcδ, map_zero, smul_neg] at h'
    have ht : t • δ = 0 := by
      have : (2 : E) * (t • δ) = 0 := by linear_combination hst - h'
      simpa using this
    have ht' : t = 0 := by simpa [hδ] using ht
    refine ⟨?_, ht'⟩
    simpa [ht'] using hst
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by simp [h2])
  intro x
  have hx : x ∈ Submodule.span F (Set.range ![(1 : E), δ]) := hsp ▸ Submodule.mem_top
  rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hx
  obtain ⟨p, q, rfl⟩ := hx
  exact ⟨p, q, by simp [Algebra.smul_def]⟩
end GlobalTheory.InfAdeleCM
