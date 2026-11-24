-- Prove2me | solution 1 for GlobalTheory.BI.isChar_finsum_conj_ext0_of_isChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:14:38.808584+00:00
-- url     : https://prove2.me/submissions/222e1166-cb86-4d37-8dc9-8f0191b67367

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterFinsumConjSubgroupFunctionExtendByZer
import Theorems.Thm_GlobalTheory_BI_inv_smul_eq_iff_conj_mem
import Theorems.Thm_GlobalTheory_BI_isChar_and_isIrrChar_of_rep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI
private theorem trace_block_permutation (K : Type) [Field K] (X : Type) [Fintype X] [DecidableEq X]
    (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (π : X → X)
    (A : X → W →ₗ[K] W) :
    LinearMap.trace K (X → W) (LinearMap.pi fun q => A q ∘ₗ LinearMap.proj (π q))
      = ∑ q, if π q = q then LinearMap.trace K W (A q) else 0 := by
  have hdec : (LinearMap.pi fun q => A q ∘ₗ LinearMap.proj (π q) : (X → W) →ₗ[K] (X → W))
      = ∑ q, LinearMap.single K (fun _ : X => W) q ∘ₗ (A q ∘ₗ LinearMap.proj (π q)) := by
    apply LinearMap.ext
    intro f
    funext p
    simp
  rw [hdec, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]
  split_ifs with h
  · have hid : LinearMap.proj (π q) ∘ₗ LinearMap.single K (fun _ : X => W) q = LinearMap.id := by
      apply LinearMap.ext
      intro w
      simp [h]
    rw [hid, LinearMap.comp_id]
  · have hz : LinearMap.proj (π q) ∘ₗ LinearMap.single K (fun _ : X => W) q = 0 := by
      apply LinearMap.ext
      intro w
      simp [h]
    rw [hz, LinearMap.comp_zero, map_zero]
section
variable {G : Type} [Group G] (H : Subgroup G)
end
end GlobalTheory.BI
end
end

set_option autoImplicit false
open GlobalTheory.BI
noncomputable section
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
theorem _root_.solution :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → L), IsChar K L ψ → IsChar K L (fun g : G => ∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out)) := by
  intro K L _ _ _ G _ _ H ψ hψ
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  obtain ⟨n, σ, hσ⟩ := hψ
  obtain ⟨m, ρ, hρ⟩ :=
    (isChar_and_isIrrChar_of_rep K L G (G ⧸ H → Fin n → K) (cosetIndRep H σ)).1
  refine ⟨m, ρ, fun g => ?_⟩
  have hg := hρ g
  simp only at hg
  rw [← hg]
  show (∑ᶠ q : G ⧸ H, ext0 H ψ (q.out⁻¹ * g * q.out)) = _
  have hc : (cosetIndRep H σ).character g
      = ∑ q, if g⁻¹ • q = q then LinearMap.trace K (Fin n → K) (σ (cosetCocycle H g q)) else 0 :=
    trace_block_permutation K (G ⧸ H) (Fin n → K) (fun q => g⁻¹ • q)
      (fun q => σ (cosetCocycle H g q))
  rw [finsum_eq_sum_of_fintype, hc, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases h : g⁻¹ • q = q
  · have hm : q.out⁻¹ * g * q.out ∈ H := (inv_smul_eq_iff_conj_mem H g q).mp h
    have he : (⟨q.out⁻¹ * g * q.out, hm⟩ : H) = cosetCocycle H g q :=
      Subtype.ext (by simp [cosetCocycle, h])
    rw [if_pos h, ext0, dif_pos hm, hσ, he]
    rfl
  · have hm : q.out⁻¹ * g * q.out ∉ H := fun hm => h ((inv_smul_eq_iff_conj_mem H g q).mpr hm)
    rw [if_neg h, ext0, dif_neg hm, map_zero]
end GlobalTheory.BI
