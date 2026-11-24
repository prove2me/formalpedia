-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.ind_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:28:53.307221+00:00
-- url     : https://prove2.me/submissions/e3a8092f-0edc-49ca-9f0d-d2bb12028b75

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistB
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_ind_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology GlobalTheory.WeilM
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution (χ : G → ℂ) (l : (G → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ φ ∈ SB G, ∀ h, l (fun x => φ (x * h)) = χ h * l φ)
    {H K : Subgroup G} (hHK : H ≤ K) (ho : IsOpen (H : Set G)) (hc : IsCompact (K : Set G)) (hχ : ∀ k ∈ K, χ k = 1) :
    l (ind K) = H.relIndex K * l (ind H) := by
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hc
  haveI : DiscreteTopology (K ⧸ H.subgroupOf K) := QuotientGroup.discreteTopology (ho.preimage continuous_subtype_val)
  haveI : Fintype (K ⧸ H.subgroupOf K) := @Fintype.ofFinite _ finite_of_compact_of_discrete
  have hH := ind_mem ho (hc.of_isClosed_subset (H.isClosed_of_isOpen ho) hHK)
  have : ind K = ∑ q : K ⧸ H.subgroupOf K, fun x => ind H (x * q.out.1) := by
    ext x
    rw [Finset.sum_apply]
    by_cases hx : x ∈ K
    · have hmem : ∀ q : K ⧸ H.subgroupOf K, x * q.out.1 ∈ (H : Set G) ↔ ((⟨x, hx⟩⁻¹ : K) : K ⧸ H.subgroupOf K) = q := by
        intro q
        conv_rhs => rw [← QuotientGroup.out_eq' q, QuotientGroup.eq, inv_inv]
        rfl
      rw [Finset.sum_eq_single ((⟨x, hx⟩⁻¹ : K) : K ⧸ H.subgroupOf K)]
      · rw [ind, ind, Set.indicator_of_mem ((hmem _).2 rfl), Set.indicator_of_mem (by exact hx)]
      · intro q _ hq; exact Set.indicator_of_notMem (fun h => hq ((hmem q).1 h).symm) _
      · simp
    · rw [ind, Set.indicator_of_notMem (by exact hx)]
      exact (Finset.sum_eq_zero fun q _ => Set.indicator_of_notMem
        (fun h => hx ((mul_mem_cancel_right q.out.2).1 (hHK h))) _).symm
  rw [this, map_sum, Finset.sum_congr rfl fun q _ => by rw [hl _ hH, hχ _ q.out.2, one_mul]]
  simp [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
end GlobalTheory.ThK.Dbl.LD
