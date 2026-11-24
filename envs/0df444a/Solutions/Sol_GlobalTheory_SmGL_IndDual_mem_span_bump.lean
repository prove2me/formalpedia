-- Prove2me | solution 1 for GlobalTheory.SmGL.IndDual.mem_span_bump
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:43:43.240894+00:00
-- url     : https://prove2.me/submissions/20ef98f6-a6f1-4225-a136-3ec13da13806

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviIntegralFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralIntegralGLMulRightComplexProductSigma
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Theorems.Thm_GlobalTheory_SmGL_IndDual_isOpen_cell
import Theorems.Thm_GlobalTheory_SmGL_IndDual_bump_mul
import Theorems.Thm_GlobalTheory_SmGL_IndDual_bump_zero
import Theorems.Thm_GlobalTheory_SmGL_IndDual_smInd_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.IndDual
variable {G W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W'] {P : Subgroup G}
namespace GlobalTheory.SmGL.IndDual
theorem _root_.solution (σ : Representation ℂ P W) {J K : Subgroup G} (hJ : IsOpen (J : Set G))
    (hK : IsCompact (K : Set G)) (hle : J ≤ K) (hn : ∀ x ∈ K, ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    (hPK : ∀ g : G, ∃ p ∈ P, ∃ x ∈ K, g = p * x) (f : smoothPart (ind P σ))
    (hf : ∀ j ∈ J, smInd P σ j f = f) :
    f ∈ Submodule.span ℂ {v | ∃ z ∈ K, ∃ w, v = smInd P σ z⁻¹ (bump σ hJ w)} := by
  classical
  have hf' : ∀ j ∈ J, ∀ x, f.1.1 (x * j) = f.1.1 x := fun j hj x => by rw [← smInd_apply, hf j hj]
  have hK' : ∀ (p : P) (x : K), (p : G)⁻¹ * x ∈ J → (p : G) ∈ K := fun p x h => by
    simpa using mul_mem x.2 (inv_mem (hle h))
  let H : Subgroup K :=
    { carrier := {x | (x : G) ∈ cell P J}
      one_mem' := ⟨1, by simp⟩
      mul_mem' := by
        rintro x y ⟨p, hp⟩ ⟨q, hq⟩
        exact ⟨p * q, by simpa [mul_assoc] using mul_mem (hn _ (inv_mem (hK' q y hq)) _ hp) hq⟩
      inv_mem' := by
        rintro x ⟨p, hp⟩
        exact ⟨p⁻¹, by simpa [mul_assoc] using hn _ (hK' p x hp) _ (inv_mem hp)⟩ }
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Finite (K ⧸ H) := H.quotient_finite_of_isOpen ((isOpen_cell hJ).preimage continuous_subtype_val)
  haveI := Fintype.ofFinite (K ⧸ H)
  have hw : ∀ z : K, f.1.1 (z : G)⁻¹ ∈ fixed σ (J.subgroupOf P) := fun z => mem_fixed_iff.2 fun h hh => by
    rw [← f.1.2 h, ← hf' _ (hn z z.2 h hh) (z : G)⁻¹]
    simp [mul_assoc]
  have key : f = ∑ q : K ⧸ H, smInd P σ (q.out : G) (bump σ hJ ⟨_, hw q.out⟩) := by
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    obtain ⟨p, hp, y, hy, rfl⟩ := hPK g
    rw [f.1.2 ⟨p, hp⟩, Subtype.property (p := (· ∈ indSpace P σ)) _ ⟨p, hp⟩]
    congr 1
    simp only [Submodule.coe_sum, Finset.sum_apply, smInd_apply]
    rw [Finset.sum_eq_single (QuotientGroup.mk (⟨y, hy⟩⁻¹ : K))]
    · have h1 := QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk (⟨y, hy⟩⁻¹ : K) : K ⧸ H)).symm
      generalize (QuotientGroup.mk (⟨y, hy⟩⁻¹ : K) : K ⧸ H).out = z at h1
      obtain ⟨q, hq⟩ := h1
      have h2 : y * z = q * ((q : G)⁻¹ * (y * z)) := by simp
      have hq' : (q : G)⁻¹ * (y * z) ∈ J := by simpa using hq
      rw [h2, bump_mul _ _ _ _ hq', ← f.1.2 q, ← hf' _ (hn z z.2 _ hq') (q * (z : G)⁻¹)]
      simp [mul_assoc]
    · intro q _ hq
      refine bump_zero _ _ _ fun h => hq ?_
      rw [← QuotientGroup.out_eq' q, eq_comm, QuotientGroup.eq]
      rw [inv_inv]
      exact h
    · simp
  rw [key]
  exact Submodule.sum_mem _ fun q _ => Submodule.subset_span ⟨(q.out : G)⁻¹, inv_mem q.out.2, _, by rw [inv_inv]⟩
end GlobalTheory.SmGL.IndDual
