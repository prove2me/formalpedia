-- Prove2me | solution 1 for GlobalTheory.OrbitAvg.avg_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:46:31.088557+00:00
-- url     : https://prove2.me/submissions/516098e3-7a1c-4347-aa6a-c831988d4b82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAveragingProjection
import Theorems.Thm_GlobalTheory_OrbitAvg_cv_mk
import Theorems.Thm_GlobalTheory_OrbitAvg_avg_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrbitAvg
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
  (π : G →* Module.End ℂ V) (L : Subgroup G)
namespace GlobalTheory.OrbitAvg
theorem _root_.solution {x y : V} (hx : (stab π L x).FiniteIndex) (hy : (stab π L y).FiniteIndex) :
    ∃ (s : Finset G) (f : G → G), s.Nonempty ∧ (∀ g ∈ s, g ∈ L) ∧
      avg π L x = (s.card : ℂ)⁻¹ • ∑ g ∈ s, π g x ∧
      avg π L y = (s.card : ℂ)⁻¹ • ∑ g ∈ s, π g y ∧
      Set.BijOn f (s : Set G) (s : Set G) ∧ ∀ g ∈ s, π g⁻¹ y = π (f g) y := by
  classical
  set N := (stab π L x ⊓ stab π L y).normalCore with hN
  have hNx : N ≤ stab π L x := le_trans (Subgroup.normalCore_le _) inf_le_left
  have hNy : N ≤ stab π L y := le_trans (Subgroup.normalCore_le _) inf_le_right
  haveI : (stab π L x ⊓ stab π L y).FiniteIndex := inferInstance
  haveI : N.FiniteIndex := Subgroup.finiteIndex_normalCore _
  haveI := Fintype.ofFinite (L ⧸ N)
  let r : L ⧸ N → G := fun q => ((q.out : L) : G)
  have hr : Function.Injective r := by
    intro q1 q2 h
    have h1 : q1.out = q2.out := Subtype.ext h
    rw [← QuotientGroup.out_eq' q1, ← QuotientGroup.out_eq' q2, h1]
  let s : Finset G := Finset.univ.image r
  have hcard : s.card = N.index := by
    rw [Finset.card_image_of_injective _ hr, Finset.card_univ, Fintype.card_eq_nat_card]; rfl
  have hsum : ∀ z : V, N ≤ stab π L z → avg π L z = (s.card : ℂ)⁻¹ • ∑ g ∈ s, π g z := by
    intro z hz
    have hzf : (stab π L z).FiniteIndex := Subgroup.finiteIndex_of_le hz
    rw [avg_eq π L hz, hcard, Finset.sum_image (fun a _ b _ h => hr h)]
    unfold avgH
    rw [finsum_eq_sum_of_fintype]
    rfl
  let f : G → G := fun g => if h : g ∈ L then
    (((((QuotientGroup.mk (⟨g, h⟩ : L) : L ⧸ N))⁻¹).out : L) : G) else g
  have hf : ∀ q : L ⧸ N, f (r q) = r q⁻¹ := by
    intro q
    simp only [f, r, Subtype.coe_eta, QuotientGroup.out_eq']
    rw [dif_pos (q.out).2]
  have hmem : ∀ g, g ∈ s ↔ ∃ q, r q = g := by
    intro g; simp [s]
  refine ⟨s, f, ?_, ?_, hsum x hNx, hsum y hNy, ?_, ?_⟩
  · exact ⟨r 1, (hmem _).mpr ⟨1, rfl⟩⟩
  · intro g hg
    obtain ⟨q, rfl⟩ := (hmem g).mp hg
    exact (q.out).2
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨q, rfl⟩ := (hmem g).mp hg
      rw [Finset.mem_coe, hf]
      exact (hmem _).mpr ⟨_, rfl⟩
    · intro g1 hg1 g2 hg2 h
      obtain ⟨q1, rfl⟩ := (hmem g1).mp hg1
      obtain ⟨q2, rfl⟩ := (hmem g2).mp hg2
      rw [hf, hf] at h
      rw [inv_injective (hr h)]
    · intro g hg
      obtain ⟨q, rfl⟩ := (hmem g).mp hg
      refine ⟨r q⁻¹, (hmem _).mpr ⟨_, rfl⟩, ?_⟩
      rw [hf, inv_inv]
  · intro g hg
    obtain ⟨q, rfl⟩ := (hmem g).mp hg
    rw [hf]
    have e1 : π (r q⁻¹) y = cv π L N y q⁻¹ := rfl
    have e2 : π (r q)⁻¹ y = cv π L N y (QuotientGroup.mk (q.out)⁻¹) := by
      rw [cv_mk π L hNy]; rfl
    rw [e1, e2, QuotientGroup.mk_inv, QuotientGroup.out_eq']
end GlobalTheory.OrbitAvg
