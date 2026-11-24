-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeMul.hk_hconv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:08:34.327406+00:00
-- url     : https://prove2.me/submissions/bbc8b775-6a02-4269-a488-fed378c956dc

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FinsumOutTranslate
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_finsum_out_translate
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_finite_out_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_isHk_right
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_support_hconv
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_hk_eq_sum
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2 Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeMul
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.HeckeMul
theorem _root_.solution {K : Subgroup (GL ι F)} {e₁ e₂ : GL ι F → ℂ} (h₁ : IsHk K e₁) (h₂ : IsHk K e₂)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V) {v : V}
    (hv : v ∈ fixed ρ K) :
    hk ρ K (hconv K e₁ e₂) v = hk ρ K e₁ (hk ρ K e₂ v) := by
  have hvk : ∀ k ∈ K, ρ k v = v := fun k hk' => by
    have := hv ⟨k, hk'⟩
    simpa using this
  have c1 : IsCompact (tsupport e₁) := h₁.2.2.1
  have c2 : IsCompact (tsupport e₂) := h₂.2.2.1
  have c12 : IsCompact (tsupport e₁ * tsupport e₂) := IsCompact.mul c1 c2
  let A := (finite_out_mem K h₁.1 c1).toFinset
  let A₂ := (finite_out_mem K h₁.1 c2).toFinset
  let B := (finite_out_mem K h₁.1 c12).toFinset
  have memA : ∀ q : GL ι F ⧸ K, q ∈ A ↔ q.out ∈ tsupport e₁ := fun q => by simp [A]
  have memA₂ : ∀ q : GL ι F ⧸ K, q ∈ A₂ ↔ q.out ∈ tsupport e₂ := fun q => by simp [A₂]
  have memB : ∀ q : GL ι F ⧸ K, q ∈ B ↔ q.out ∈ tsupport e₁ * tsupport e₂ := fun q => by simp [B]
  have hc : ∀ g, hconv K e₁ e₂ g = ∑ q ∈ A, e₁ q.out * e₂ (q.out⁻¹ * g) := fun g => by
    unfold hconv
    refine finsum_eq_sum_of_support_subset _ ?_
    intro q hq
    exact Finset.mem_coe.2 ((memA q).2 (subset_tsupport _ (left_ne_zero_of_mul hq)))
  have hL := hk_eq_sum ρ K (hconv K e₁ e₂) v B
    (fun s hs => (memB s).2 (support_hconv K e₁ e₂ hs))
  have hT : ∀ x : GL ι F, ∑ᶠ r : GL ι F ⧸ K, e₂ r.out • ρ (x * r.out) v
      = ∑ᶠ s : GL ι F ⧸ K, e₂ (x⁻¹ * s.out) • ρ s.out v := fun x => by
    have hr : ∀ y, ∀ k ∈ K, (fun y => e₂ (x⁻¹ * y) • ρ y v) (y * k) = (fun y => e₂ (x⁻¹ * y) • ρ y v) y := by
      intro y k hk'
      show e₂ (x⁻¹ * (y * k)) • ρ (y * k) v = e₂ (x⁻¹ * y) • ρ y v
      rw [← mul_assoc, isHk_right h₂ _ hk', map_mul, Module.End.mul_apply, hvk k hk']
    have ht := finsum_out_translate K (fun y => e₂ (x⁻¹ * y) • ρ y v) hr x
    simpa only [inv_mul_cancel_left] using ht
  have hI : ∀ q ∈ A, ρ q.out (hk ρ K e₂ v) = ∑ s ∈ B, e₂ (q.out⁻¹ * s.out) • ρ s.out v := by
    intro q hq
    have hq' := (memA q).1 hq
    rw [hk_eq_sum ρ K e₂ v A₂ (fun r hr => (memA₂ r).2 (subset_tsupport _ hr)), map_sum]
    have h1 : ∑ r ∈ A₂, ρ q.out (e₂ r.out • ρ r.out v) = ∑ᶠ r : GL ι F ⧸ K, e₂ r.out • ρ (q.out * r.out) v := by
      symm
      rw [finsum_eq_sum_of_support_subset (s := A₂)]
      · refine Finset.sum_congr rfl fun r _ => ?_
        rw [map_smul, map_mul, Module.End.mul_apply]
      · intro r hr
        refine Finset.mem_coe.2 ((memA₂ r).2 (subset_tsupport _ fun h0 => (Function.mem_support.1 hr) ?_))
        show e₂ r.out • ρ (q.out * r.out) v = 0
        rw [h0, zero_smul]
    rw [h1, hT]
    refine finsum_eq_sum_of_support_subset _ ?_
    intro s hs
    refine Finset.mem_coe.2 ((memB s).2 (Set.mem_mul.2 ⟨q.out, hq', q.out⁻¹ * s.out,
      subset_tsupport _ fun h0 => (Function.mem_support.1 hs) ?_, mul_inv_cancel_left _ _⟩))
    show e₂ (q.out⁻¹ * s.out) • ρ s.out v = 0
    rw [h0, zero_smul]
  have hR : hk ρ K e₁ (hk ρ K e₂ v)
      = ∑ q ∈ A, e₁ q.out • ∑ s ∈ B, e₂ (q.out⁻¹ * s.out) • ρ s.out v := by
    rw [hk_eq_sum ρ K e₁ _ A (fun q hq => (memA q).2 (subset_tsupport _ hq))]
    exact Finset.sum_congr rfl (fun q hq => by rw [hI q hq])
  rw [hL, hR]
  simp only [hc, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm
end GlobalTheory.CompanionTheory.HeckeMul
