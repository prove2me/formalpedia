-- Prove2me | solution 1 for GlobalTheory.SBUnif.sb_lattice_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:34:14.800923+00:00
-- url     : https://prove2.me/submissions/b8eb1cb4-1248-4f7f-8272-c926010960c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Theorems.Thm_GlobalTheory_SBUnif_exists_nat_mem_mul_integer
import Theorems.Thm_GlobalTheory_SBUnif_exists_ne_zero_of_eventually

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
noncomputable section
open GlobalTheory GlobalTheory.SBUnif
namespace GlobalTheory.SBUnif
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (Y Y' : Type) [Fintype Y] [Fintype Y'] (Φ : Matrix Y Y' k → ℂ), Φ ∈ SB (Matrix Y Y' k) → ∃ n : ℕ, 0 < n ∧ (∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) → ∀ t, Φ (t + n • u) = Φ t) ∧ ∀ t, Φ t ≠ 0 → ∀ r q, (n • t) r q ∈ 𝒪[k] := by
  intro k _ _ _ _ _ Y Y' _ _ Φ hΦ
  obtain ⟨hlc, hcs⟩ := hΦ
  set O : Set (Matrix Y Y' k) := {u | ∀ r q, u r q ∈ 𝒪[k]} with hOdef
  have hOpi : O = Set.univ.pi (fun _ : Y => Set.univ.pi (fun _ : Y' => (𝒪[k] : Set k))) := by
    ext u
    constructor
    · intro h r _ q _
      exact h r q
    · intro h r q
      exact h r (Set.mem_univ _) q (Set.mem_univ _)
  have hOc : IsCompact O := by
    rw [hOpi]
    exact isCompact_univ_pi (fun _ => isCompact_univ_pi
      (fun _ => (isCompact_iff_compactSpace (s := (𝒪[k] : Set k))).mpr
        (inferInstanceAs (CompactSpace 𝒪[k]))))
  have hOo : IsOpen O := by
    rw [hOpi]
    exact isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_set_pi Set.finite_univ
      (fun _ _ => Valuation.isOpen_integer (v := valuation k)))
  have hK : IsCompact (tsupport Φ) := hcs
  have h1 : ∀ᶠ s in nhds (0 : k), ∀ p ∈ tsupport Φ ×ˢ O, Φ (p.1 + s • p.2) = Φ p.1 := by
    apply (hK.prod hOc).eventually_forall_of_forall_eventually
    intro p _
    have hc : Continuous (fun z : k × (Matrix Y Y' k × Matrix Y Y' k) => z.2.1 + z.1 • z.2.2) := by
      fun_prop
    have e1 := (hlc.comp_continuous hc).eventually_eq (0, p)
    have e2 := (hlc.comp_continuous (continuous_fst.comp continuous_snd)).eventually_eq
      ((0 : k), p)
    filter_upwards [e1, e2] with z hz1 hz2
    simp only [Function.comp_apply, zero_smul, add_zero] at hz1 hz2
    rw [hz1, hz2]
  have h2 : ∀ᶠ s in nhds (0 : k), ∀ t ∈ tsupport Φ, s • t ∈ O := by
    apply hK.eventually_forall_of_forall_eventually
    intro t _
    have hc : Continuous (fun z : k × Matrix Y Y' k => z.1 • z.2) := by fun_prop
    have h0 : (fun z : k × Matrix Y Y' k => z.1 • z.2) ((0 : k), t) ∈ O := by
      simp only [zero_smul]
      intro r q
      simp
    exact hc.continuousAt.preimage_mem_nhds (hOo.mem_nhds h0)
  obtain ⟨c, hc0, hc1, hc2⟩ := exists_ne_zero_of_eventually (h1.and h2)
  obtain ⟨n, hn, hy⟩ := exists_nat_mem_mul_integer c hc0
  set y := c⁻¹ * (n : k) with hydef
  have hn' : (n : k) = c * y := by
    rw [hydef, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  have hsmul : ∀ u : Matrix Y Y' k, n • u = c • (y • u) := by
    intro u
    rw [smul_smul, ← hn', Nat.cast_smul_eq_nsmul]
  have hyO : ∀ u ∈ O, y • u ∈ O := fun u hu r q => by
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact mul_mem hy (hu r q)
  refine ⟨n, hn, ?_, ?_⟩
  · intro u hu t
    rw [hsmul]
    have hu' : y • u ∈ O := hyO u hu
    by_cases ht : t ∈ tsupport Φ
    · exact hc1 (t, y • u) ⟨ht, hu'⟩
    by_cases ht' : t + c • (y • u) ∈ tsupport Φ
    · have hneg : -(y • u) ∈ O := fun r q => by
        simp only [Matrix.neg_apply]
        exact neg_mem (hu' r q)
      have := hc1 (t + c • (y • u), -(y • u)) ⟨ht', hneg⟩
      simp only [smul_neg, add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport ht', image_eq_zero_of_notMem_tsupport ht]
  · intro t ht r q
    have htK : t ∈ tsupport Φ := subset_tsupport _ ht
    rw [hsmul, smul_comm]
    exact hyO _ (hc2 t htK) r q
end GlobalTheory.SBUnif
