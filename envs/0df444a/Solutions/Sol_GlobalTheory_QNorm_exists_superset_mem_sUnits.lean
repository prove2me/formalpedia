-- Prove2me | solution 1 for GlobalTheory.QNorm.exists_superset_mem_sUnits
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:57.684655+00:00
-- url     : https://prove2.me/submissions/f453835a-34b3-48de-a84f-b77635c0a0e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSupersetMemSUnits
import Theorems.Thm_GlobalTheory_QNorm_finite_valuation_ne_one
import Theorems.Thm_GlobalTheory_QNorm_mem_sUnits


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution :
    ∀ (F : Type) [Field F] [NumberField F] (X : Finset Fˣ)
      (S₀ : Finset (HeightOneSpectrum (𝓞 F))),
      ∃ S, S₀ ⊆ S ∧ ∀ S', S ⊆ S' → ∀ x ∈ X, x ∈ sUnits F S' := by
  intro F _ _ X S₀
  classical
  have hT : (⋃ x ∈ X, {v : HeightOneSpectrum (𝓞 F) | v.valuation F (x : F) ≠ 1}).Finite :=
    X.finite_toSet.biUnion fun x _ => finite_valuation_ne_one F x
  refine ⟨S₀ ∪ hT.toFinset, Finset.subset_union_left, ?_⟩
  intro S' hS' x hx
  rw [mem_sUnits]
  intro v hv
  by_contra h
  apply hv
  apply hS'
  apply Finset.mem_union_right
  rw [Set.Finite.mem_toFinset]
  exact Set.mem_biUnion hx h
end GlobalTheory.QNorm
