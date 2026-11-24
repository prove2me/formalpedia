-- Prove2me | solution 1 for GlobalTheory.EigenLattice.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:44:35.207196+00:00
-- url     : https://prove2.me/submissions/2a4af147-1139-46d9-97f2-df93bec9ddc9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralSecond
import Theorems.Thm_GlobalTheory_EigenLattice_sat
import Theorems.Thm_GlobalTheory_EigenLattice_exists_ne_mem
import Theorems.Thm_GlobalTheory_EigenLattice_finrank_le
import Theorems.Thm_GlobalTheory_EigenLattice_compl
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
namespace GlobalTheory.EigenLattice
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → ∀ σ : E →+* K, IsSat (eigLat ρ σ) ∧ (∃ g : H, g ≠ 0 ∧ eigLat ρ σ = O ∙ g) ∧ Module.Free O (eigLat ρ σ) ∧ Module.finrank O (eigLat ρ σ) = 1 ∧ ∃ C : Submodule O H, IsCompl (eigLat ρ σ) C := by
  intro E _ _ _ c _ l _ O _ _ _ _ K _ _ _ _ _ D _ _ I _ φ _ H _ _ ρ Fil B hL σ
  obtain ⟨hfree, hfin, -, hline, -⟩ := hL
  haveI := hfree; haveI := hfin
  have hsat := GlobalTheory.EigenLattice.sat (K := K) ρ σ
  obtain ⟨g0, hg0, hg0m⟩ := GlobalTheory.EigenLattice.exists_ne_mem ρ σ (hline σ)
  set N := eigLat ρ σ
  have hle := GlobalTheory.EigenLattice.finrank_le ρ σ (hline σ)
  haveI : Nontrivial N := ⟨⟨⟨g0, hg0m⟩, 0, fun h => hg0 (congrArg Subtype.val h)⟩⟩
  have hpos : 0 < Module.finrank O N := Module.finrank_pos_iff.2 inferInstance
  have h1 : Module.finrank O N = 1 := le_antisymm hle hpos
  let b := Module.finBasisOfFinrankEq O N h1
  refine ⟨hsat, ⟨(b 0 : H), fun h => b.ne_zero 0 (Subtype.ext h), ?_⟩, inferInstance, h1,
    GlobalTheory.EigenLattice.compl N hsat⟩
  apply le_antisymm
  · intro x hx
    have := b.sum_repr ⟨x, hx⟩
    rw [Fin.sum_univ_one] at this
    rw [Submodule.mem_span_singleton]
    exact ⟨b.repr ⟨x, hx⟩ 0, by simpa using congrArg Subtype.val this⟩
  · rw [Submodule.span_singleton_le_iff_mem]; exact (b 0).2
end GlobalTheory.EigenLattice
