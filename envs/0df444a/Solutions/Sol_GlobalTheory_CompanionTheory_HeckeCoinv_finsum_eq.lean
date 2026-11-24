-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeCoinv.finsum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:37:02.084341+00:00
-- url     : https://prove2.me/submissions/b332adb8-20b9-4152-894a-b062a967757d

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ModularityStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCoinv_support_finite
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open CompanionTheory.Rg.Fl
open scoped InnerProductSpace ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeCoinv
variable (Γ : Type) {X : Type} [Group Γ] [MulAction Γ X]
variable {Γ}
namespace GlobalTheory.CompanionTheory.HeckeCoinv
theorem _root_.solution [∀ x : X, Finite (MulAction.stabilizer Γ x)] (f : X →₀ ℂ) (x : X) :
    ∑ᶠ γ : Γ, f (γ • x) = f.sum fun z c => c * (cnt Γ x z : ℂ) := by
  classical
  rw [finsum_eq_sum_of_support_subset _ (s := (support_finite (Γ := Γ) f x).toFinset) (by simp)]
  have hmaps : ∀ γ ∈ (support_finite (Γ := Γ) f x).toFinset, γ • x ∈ f.support := by
    intro γ hγ
    simpa using hγ
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finsupp.sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  have h1 : ∀ γ ∈ (support_finite (Γ := Γ) f x).toFinset.filter (fun γ => γ • x = z),
      f (γ • x) = f z := by
    intro γ hγ
    rw [(Finset.mem_filter.1 hγ).2]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 2
  have H : ∀ γ : Γ, γ • x = z ↔ γ ∈ (support_finite (Γ := Γ) f x).toFinset.filter (fun γ => γ • x = z) := by
    intro γ
    constructor
    · intro hγ
      refine Finset.mem_filter.2 ⟨?_, hγ⟩
      simpa [hγ] using Finsupp.mem_support_iff.1 hz
    · intro hγ
      exact (Finset.mem_filter.1 hγ).2
  unfold cnt
  rw [Nat.card_congr (Equiv.subtypeEquivRight H), Nat.card_eq_fintype_card, Fintype.card_coe]
end GlobalTheory.CompanionTheory.HeckeCoinv
