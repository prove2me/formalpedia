-- Prove2me | solution 1 for GlobalTheory.GLDoubling.isIwasawa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:05.275444+00:00
-- url     : https://prove2.me/submissions/3e3006af-7d1b-47f1-884b-70768c163e4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Theorems.Thm_GlobalTheory_GLDoubling_coe_absRatio
import Theorems.Thm_GlobalTheory_GLDoubling_one_int
import Theorems.Thm_GlobalTheory_GLDoubling_shear_mem
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_refl
import Theorems.Thm_GlobalTheory_SplitWeil_iwasawa_blockTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf



set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling Formalism.UG
open scoped NNReal Pointwise
open GlobalTheory GlobalTheory.GLDoubling
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n]
variable {k n}
namespace GlobalTheory.GLDoubling
theorem _root_.solution : IsIwasawa (absRatio k n) (KO k (n ⊕ n)) := by
  constructor
  · intro g
    let δ : GL (n ⊕ n) k := shear 0 1 (by simp) (by simp)
    have hδ : δ ∈ KO k (n ⊕ n) := shear_mem _ _ (fun _ _ => zero_mem _) one_int
    obtain ⟨b, hb, w, hw, e⟩ := iwasawa_blockTriangular k (n ⊕ n) (Sum.elim (fun _ => 0) fun _ => 1) (δ⁻¹ * g)
    have h21 : b.1.toBlocks₂₁ = 0 := by
      ext i j
      exact hb (by simp)
    refine ⟨⟨δ * b * δ⁻¹, mem_stabGL_diagSub.2 ?_⟩, δ * w, mul_mem hδ hw, ?_⟩
    · have : (δ * b * δ⁻¹).1 = fromBlocks 1 0 1 1 * b.1 * fromBlocks 1 (-0) (-1) 1 := rfl
      rw [this, ← fromBlocks_toBlocks b.1, h21]
      simp [KeepsDiag, leviMat, fromBlocks_multiply]
      abel
    · show g = δ * b * δ⁻¹ * (δ * w)
      rw [inv_mul_eq_iff_eq_mul] at e
      rw [e]; group
  · intro p hp
    have key : ∀ q : siegel k n, (q : GL (n ⊕ n) k) ∈ KO k (n ⊕ n) → ∀ i j,
        (leviGL (Equiv.refl (n ⊕ n)) q).1 i j ∈ 𝒪[k] := fun q hq i j =>
      add_mem (((SplitFlip.mem_KO_iff _).1 hq).1 _ _) (((SplitFlip.mem_KO_iff _).1 hq).1 _ _)
    have h1 : leviGL (Equiv.refl (n ⊕ n)) p ∈ KO k n :=
      (SplitFlip.mem_KO_iff _).2 ⟨key p hp, by rw [← map_inv]; exact key _ (inv_mem hp)⟩
    apply NNReal.coe_injective
    rw [coe_absRatio, nabs_det_of_mem_KO h1, nabs_det_of_mem_KO hp]
    simp
end GlobalTheory.GLDoubling
