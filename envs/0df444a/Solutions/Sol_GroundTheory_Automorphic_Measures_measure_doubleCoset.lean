-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.measure_doubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:13:04.493588+00:00
-- url     : https://prove2.me/submissions/46c89a06-a413-4ba1-8b60-3ecb1cfca9cc

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsHaar
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Theorems.Thm_GroundTheory_Automorphic_Measures_measure_preimage_mk_finset
import Theorems.Thm_GroundTheory_Automorphic_Measures_mem_map_conj_iff
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel DoubleCoset
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution (μ : Measure G) [μ.IsMulLeftInvariant] {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (g : G) :
    μ (doubleCoset g (K : Set G) K) =
      ((K.map (MulAut.conj g).toMonoidHom).relIndex K : ℝ≥0∞) * μ K := by
  set H := K.map (MulAut.conj g).toMonoidHom with hH
  let O : Set (G ⧸ K) := MulAction.orbit K (g : G ⧸ K)
  have hstab : MulAction.stabilizer K (g : G ⧸ K) = H.subgroupOf K := by
    ext k
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_map_conj_iff]
    show ((k : G) • ((g : G) : G ⧸ K)) = ((g : G) : G ⧸ K) ↔ _
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul,
      show ((k : G) * g)⁻¹ * g = (g⁻¹ * k * g)⁻¹ by group, K.inv_mem_iff]
  have hdc : doubleCoset g (K : Set G) K = (QuotientGroup.mk : G → G ⧸ K) ⁻¹' O := by
    ext x
    rw [mem_doubleCoset, Set.mem_preimage, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨k₁, hk₁, k₂, hk₂, rfl⟩
      refine ⟨⟨k₁, hk₁⟩, ?_⟩
      show ((k₁ : G) • ((g : G) : G ⧸ K)) = _
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
      simpa [mul_assoc] using hk₂
    · rintro ⟨k, hk⟩
      change ((k : G) • ((g : G) : G ⧸ K)) = _ at hk
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq] at hk
      exact ⟨k, k.2, (k * g)⁻¹ * x, hk, by group⟩
  have hcK : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  have hopen : IsOpen ((H.subgroupOf K : Subgroup K) : Set K) := by
    have : IsOpen (H : Set G) := by
      have e : (H : Set G) = (fun x => g⁻¹ * x * g) ⁻¹' K := by
        ext x
        exact mem_map_conj_iff
      rw [e]
      exact hKo.preimage (by fun_prop)
    exact this.preimage continuous_subtype_val
  have hfin : Finite (K ⧸ H.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hopen
  have hOfin : O.Finite := by
    have : Finite O := by
      rw [← hstab] at hfin
      exact Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer K (g : G ⧸ K)).symm
    exact Set.toFinite O
  have hcard : hOfin.toFinset.card = H.relIndex K := by
    rw [← Nat.card_eq_card_finite_toFinset, Subgroup.relIndex, Subgroup.index, ← hstab]
    exact Nat.card_congr (MulAction.orbitEquivQuotientStabilizer K (g : G ⧸ K))
  rw [hdc, ← hOfin.coe_toFinset, measure_preimage_mk_finset μ hKo, hcard]
end GroundTheory.Automorphic.Measures
