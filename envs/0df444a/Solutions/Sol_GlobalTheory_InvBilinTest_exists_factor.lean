-- Prove2me | solution 1 for GlobalTheory.InvBilinTest.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:05:03.212416+00:00
-- url     : https://prove2.me/submissions/23b68ce3-d0b0-4c75-8c3a-1ba9339572ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantCosetInd
import Theorems.Thm_GlobalTheory_InvBilinTest_cosetInd_apply
import Theorems.Thm_GlobalTheory_InvBilinTest_smoothOp_cosetInd
import Theorems.Thm_GlobalTheory_InvBilinTest_key
import Theorems.Thm_GlobalTheory_OpTrace_isOpen_leftStabilizer
import Theorems.Thm_GlobalTheory_OpTrace_mem_fixed
import Theorems.Thm_GlobalTheory_PRep_IsSmooth_smoothOp_mem_fixed
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace
noncomputable section
open GlobalTheory GlobalTheory.InvBilinTest
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
variable [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
  {Y : Type} [AddCommGroup Y] [Module ℂ Y]
namespace GlobalTheory.InvBilinTest
theorem _root_.solution (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G,
      IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (hπ : IsSmooth π)
    (Y : Type) [AddCommGroup Y] [Module ℂ Y] (B : SB G →ₗ[ℂ] V →ₗ[ℂ] Y)
    (hB : ∀ (g : G) (φ ψ : SB G) (v : V), (∀ x, ψ.1 x = φ.1 (x * g)) → B ψ (π g v) = B φ v) :
    ∃ B₀ : V →ₗ[ℂ] Y, ∀ (φ : SB G) (v : V), B φ v = B₀ (smoothOp π μ φ.1 v) := by
  have hpos : ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) →
      (μ.real K : ℂ) ≠ 0 := fun K ho hK => by
    have h1 : μ K ≠ 0 := (ho.measure_pos μ ⟨1, K.one_mem⟩).ne'
    have h2 : μ.real K ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h1, hK.measure_ne_top⟩
    exact_mod_cast h2
  have hle : ∀ (K : Subgroup G) (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G))
      (L : Subgroup G) (ho' : IsOpen (L : Set G)) (hL : IsCompact (L : Set G)), L ≤ K →
      ∀ w, (∀ k ∈ K, π k w = w) →
      (μ.real K : ℂ)⁻¹ • B (cosetInd K ho hK 1) w = (μ.real L : ℂ)⁻¹ • B (cosetInd L ho' hL 1) w := by
    intro K ho hK L ho' hL hLK w hw
    have h := key (μ := μ) hπ B hB L ho' hL (cosetInd K ho hK 1) (fun k hk g => by
      classical
      rw [cosetInd_apply, cosetInd_apply, mul_assoc]
      exact if_congr (K.mul_mem_cancel_left (hLK hk)) rfl rfl) w
    rw [smoothOp_cosetInd hπ K ho hK hw, map_smul] at h
    rw [inv_smul_eq_iff₀ (hpos K ho hK), smul_comm, h, inv_smul_smul₀ (hpos L ho' hL)]
  have hex : ∀ w : V, ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧
      ∀ k ∈ K, π k w = w := fun w => by
    obtain ⟨K, ho, hK, h⟩ := hG _ ((hπ w).mem_nhds (show π 1 w = w by simp))
    exact ⟨K, ho, hK, fun k hk => h hk⟩
  choose K ho hK hw using hex
  have hinter : ∀ (L M : Subgroup G), IsCompact (L : Set G) → IsOpen (M : Set G) →
      IsCompact ((L ⊓ M : Subgroup G) : Set G) := fun L M hL hM =>
    hL.inter_right (M.isClosed_of_isOpen hM)
  let b : V → Y := fun w => (μ.real (K w) : ℂ)⁻¹ • B (cosetInd (K w) (ho w) (hK w) 1) w
  have hb : ∀ (L : Subgroup G) (ho' : IsOpen (L : Set G)) (hL : IsCompact (L : Set G)) (w : V),
      (∀ k ∈ L, π k w = w) → b w = (μ.real L : ℂ)⁻¹ • B (cosetInd L ho' hL 1) w := by
    intro L ho' hL w h
    have h1 : IsOpen ((L ⊓ K w : Subgroup G) : Set G) := ho'.inter (ho w)
    have h2 := hinter L (K w) hL (ho w)
    exact (hle _ _ _ _ h1 h2 inf_le_right w (hw w)).trans (hle _ _ _ _ h1 h2 inf_le_left w h).symm
  refine ⟨⟨⟨b, fun v w => ?_⟩, fun c v => ?_⟩, fun φ v => ?_⟩
  · have h1 : IsOpen ((K v ⊓ K w : Subgroup G) : Set G) := (ho v).inter (ho w)
    have h2 := hinter (K v) (K w) (hK v) (ho w)
    rw [hb _ h1 h2 v fun k hk => hw v k hk.1, hb _ h1 h2 w fun k hk => hw w k hk.2,
      hb _ h1 h2 (v + w) fun k hk => by rw [map_add, hw v k hk.1, hw w k hk.2], map_add, smul_add]
  · show b (c • v) = c • b v
    rw [hb _ (ho v) (hK v) (c • v) fun k hk => by rw [map_smul, hw v k hk], map_smul, smul_comm]
  · show _ = b _
    obtain ⟨L, ho', hL, h⟩ := hG _ ((isOpen_leftStabilizer φ.2.1 φ.2.2).mem_nhds (one_mem _))
    have hφ : ∀ k ∈ L, ∀ g, φ.1 (k * g) = φ.1 g := fun k hk => h hk
    rw [hb L ho' hL _ (mem_fixed.1 (hπ.smoothOp_mem_fixed φ.2.1 φ.2.2 hφ v)),
      key hπ B hB L ho' hL φ hφ, inv_smul_smul₀ (hpos L ho' hL)]
end GlobalTheory.InvBilinTest
