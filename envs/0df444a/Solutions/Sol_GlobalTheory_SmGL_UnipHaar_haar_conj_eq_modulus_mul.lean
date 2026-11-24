-- Prove2me | solution 1 for GlobalTheory.SmGL.UnipHaar.haar_conj_eq_modulus_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:29:57.90821+00:00
-- url     : https://prove2.me/submissions/79be2098-28d6-4866-8cb5-56a5e3597c08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Theorems.Thm_GlobalTheory_SmGL_UnipHaar_continuous_conj
import Theorems.Thm_GlobalTheory_SmGL_UnipHaar_isHaarMeasure_map
import Theorems.Thm_GlobalTheory_SmGL_UnipHaar_map_preimage_conj
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped Kronecker
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnipHaar
namespace GlobalTheory.SmGL.UnipHaar
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) [MeasurableSpace (unipRad k e)] [BorelSpace (unipRad k e)] (μ : Measure (unipRad k e)) [μ.IsHaarMeasure] (g : Levi k m) (S : Set (unipRad k e)), MeasurableSet S → μ {u | ∃ s ∈ S, (u : GL n k) = leviEmb k e g * (s : GL n k) * (leviEmb k e g)⁻¹} = ENNReal.ofReal (modulus k m g) * μ S := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e _ _ μ _ g S hS
  borelize k
  haveI := secondCountable k
  haveI := t2Space k
  haveI : LocallyCompactSpace (unipRad k e) := (unipHomeo e).isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (unipRad k e) := (unipHomeo e).secondCountableTopology
  haveI := isHaarMeasure_map e (Measure.addHaar : Measure k)
  have h1 : {u : unipRad k e | ∃ s ∈ S, (u : GL n k) = leviEmb k e g * (s : GL n k) * (leviEmb k e g)⁻¹} =
      conj e g⁻¹ ⁻¹' S := by
    ext u
    refine ⟨?_, fun h => ⟨_, h, by simp [conj, mul_assoc]⟩⟩
    rintro ⟨s, hs, h⟩
    have : conj e g⁻¹ u = s := Subtype.ext (by simp [conj, h, mul_assoc])
    rwa [Set.mem_preimage, this]
  have h2 : conj e g ⁻¹' (conj e g⁻¹ ⁻¹' S) = S := by
    ext u
    have : conj e g⁻¹ (conj e g u) = u := Subtype.ext (by simp [conj, mul_assoc])
    rw [Set.mem_preimage, Set.mem_preimage, this]
  have h3 := map_preimage_conj e (Measure.addHaar : Measure k) g
    ((continuous_conj e g⁻¹).measurable hS)
  rw [h2] at h3
  rw [h1, Measure.isMulLeftInvariant_eq_smul μ
    (Measure.map (unipHomeo e).symm (Measure.pi fun _ : Idx e => (Measure.addHaar : Measure k))),
    Measure.smul_apply, Measure.smul_apply, h3, mul_smul_comm]
end GlobalTheory.SmGL.UnipHaar
