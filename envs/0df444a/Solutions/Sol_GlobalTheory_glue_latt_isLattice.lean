-- Prove2me | solution 1 for GlobalTheory.glue_latt_isLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:59:44.399227+00:00
-- url     : https://prove2.me/submissions/af898442-118e-4127-9a37-3c79e2172bfc

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanSingleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLatticeOfSqueezedBetweenNatMultiples

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
namespace GlobalTheory
theorem _root_.solution {E : Type} [Field E] [NumberField E] (n : ℕ) (Γ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ) (hN : N ≠ 0)
    (hlow : ∀ x : Fin n → E, (∀ i, IsIntegral ℤ (x i)) → (N : E) • x ∈ Γ)
    (hup : ∀ x ∈ Γ, ∀ i, IsIntegral ℤ ((N : E) * x i)) : Submodule.IsLattice E Γ := by
  have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN
  let f : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → E) :=
    ((N : E)⁻¹ • (LinearMap.pi fun i => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj i)))
  have hle : Γ ≤ LinearMap.range f := by
    intro x hx
    refine ⟨fun i => ⟨(N : E) * x i, hup x hx i⟩, ?_⟩
    ext i
    change (N : E)⁻¹ * ((N : E) * x i) = x i
    rw [← mul_assoc, inv_mul_cancel₀ hNE, one_mul]
  refine ⟨?_, ?_⟩
  · rw [← Submodule.map_comap_eq_self hle]
    exact (IsNoetherian.noetherian _).map f
  · rw [eq_top_iff]
    intro y _
    rw [pi_eq_sum_univ y]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have hmem : (N : E) • (fun j => if i = j then (1 : E) else 0) ∈ Γ := by
      apply hlow
      intro j
      split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
    have : (fun j => if i = j then (1 : E) else 0) = (N : E)⁻¹ • ((N : E) • (fun j => if i = j then (1 : E) else 0)) := by
      rw [smul_smul, inv_mul_cancel₀ hNE, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
end GlobalTheory
