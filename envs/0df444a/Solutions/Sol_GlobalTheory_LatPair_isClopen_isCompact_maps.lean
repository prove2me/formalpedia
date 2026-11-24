-- Prove2me | solution 1 for GlobalTheory.LatPair.isClopen_isCompact_maps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:39.871207+00:00
-- url     : https://prove2.me/submissions/ddfa49cf-32e3-47cc-b9f6-3bb4e2bebeac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Theorems.Thm_GlobalTheory_LatPair_maps_stdLat_iff
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_int
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_int
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
open SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable [Fintype n] [Fintype n']
namespace GlobalTheory.LatPair
theorem _root_.solution (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k)) [S.IsLattice k]
    [L.IsLattice k] : IsClopen {x : Matrix n n' k | ∀ y ∈ S, x *ᵥ y ∈ L} ∧
      IsCompact {x : Matrix n n' k | ∀ y ∈ S, x *ᵥ y ∈ L} := by
  classical
  haveI := t2Space k
  obtain ⟨g, rfl⟩ := exists_smul_lat (stdLat k n') S
  obtain ⟨h, rfl⟩ := exists_smul_lat (stdLat k n) L
  let K : Set (Matrix n n' k) := Set.univ.pi fun _ => Set.univ.pi fun _ => (𝒪[k] : Set k)
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_int k
  have hKo : IsOpen K :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_int k
  have e : {x : Matrix n n' k | ∀ y ∈ g • stdLat k n', x *ᵥ y ∈ h • stdLat k n} = sideMul g h ⁻¹' K := by
    ext x
    have h1 : sideMul g h x ∈ K ↔ ∀ i j, ((h⁻¹ : GL n k).val * x * g.val) i j ∈ 𝒪[k] :=
      ⟨fun H i j => H i trivial j trivial, fun H i _ j _ => H i j⟩
    rw [Set.mem_preimage, h1, ← maps_stdLat_iff, Set.mem_setOf_eq]
    simp only [mem_smul_iff, ← mulVec_mulVec]
    refine ⟨fun H y hy => H (g • y) (by simpa using hy), fun H y hy => ?_⟩
    have := H _ hy
    rwa [show g.val *ᵥ (g⁻¹ • y) = y from smul_inv_smul g y] at this
  rw [e]
  exact ⟨IsClopen.preimage ⟨hKc.isClosed, hKo⟩ (sideMul g h).continuous, (sideMul g h).isCompact_preimage.2 hKc⟩
end GlobalTheory.LatPair
