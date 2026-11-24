-- Prove2me | solution 1 for GlobalTheory.BetaEx.detSpan_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:17:21.664481+00:00
-- url     : https://prove2.me/submissions/0c82c476-4bdc-4861-947e-38488d602760

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal
import Theorems.Thm_GlobalTheory_BetaEx_mem_detSet
import Theorems.Thm_GlobalTheory_BetaEx_det_mem
import Theorems.Thm_GlobalTheory_BetaEx_row_update_mem
import Theorems.Thm_GlobalTheory_BetaEx_smul_det_mem
import Theorems.Thm_GlobalTheory_BetaEx_cramer_rows
import Theorems.Thm_GlobalTheory_BetaEx_detSpan_mono
import Theorems.Thm_GlobalTheory_BetaEx_frac_of_bdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BetaEx
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
namespace GlobalTheory.BetaEx
theorem _root_.solution (M' : Submodule (𝓞 E) (Fin n → E)) (m : Fin n → E)
    (hb : Bdd (M' ⊔ Submodule.span (𝓞 E) {m})) :
    detSpan M' = (M'.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)) •
      detSpan (M' ⊔ Submodule.span (𝓞 E) {m}) := by
  set M := M' ⊔ Submodule.span (𝓞 E) {m} with hM
  have hle : M' ≤ M := le_sup_left
  have hm : m ∈ M := Submodule.mem_sup_right (Submodule.mem_span_singleton_self m)
  apply le_antisymm
  · by_cases h0 : detSpan M = ⊥
    · exact (detSpan_mono hle).trans (h0.le.trans bot_le)
    let I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨detSpan M, frac_of_bdd hb⟩
    have hI : I ≠ 0 := fun h => h0 (by
      have := congrArg (fun J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E => (J : Submodule (𝓞 E) E)) h
      simp only [FractionalIdeal.coe_zero] at this
      exact this)
    have h1 : detSpan M * ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) = 1 := by
      have := congrArg (fun J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E => (J : Submodule (𝓞 E) E))
        (mul_inv_cancel₀ hI)
      simp only [FractionalIdeal.coe_mul, FractionalIdeal.coe_one] at this
      exact this
    generalize ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) = J at h1
    have hint : ∀ x ∈ detSpan M, ∀ y ∈ J, ∃ b : 𝓞 E, (b : E) = x * y := by
      intro x hx y hy
      have := Submodule.mul_mem_mul hx hy
      rw [h1] at this
      exact Submodule.mem_one.1 this
    apply Submodule.span_le.2
    intro d hd
    obtain ⟨v, hv, rfl⟩ := (mem_detSet M' d).1 hd
    have h1m : (1 : E) ∈ detSpan M * J := by rw [h1]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
    have : ∀ z ∈ detSpan M * J, v.det * z ∈
        (M'.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)) • detSpan M := by
      intro z hz
      refine Submodule.mul_induction_on hz ?_ ?_
      · intro x hx y hy
        obtain ⟨b, hb⟩ := hint _ (det_mem v fun i => hle (hv i)) y hy
        have e : v.det * (x * y) = b • x := by
          change _ = (b : E) * x
          rw [hb]; ring
        rw [e]
        refine Submodule.smul_mem_smul ?_ hx
        change b • m ∈ M'
        have e2 : b • m = y • (v.det • m) := by
          change (b : E) • m = _
          rw [hb, smul_smul, mul_comm]
        rw [e2, cramer_rows, Finset.smul_sum]
        refine Submodule.sum_mem _ fun i _ => ?_
        obtain ⟨b', hb'⟩ := hint _ (det_mem _ (row_update_mem v (fun i => hle (hv i)) i m hm)) y hy
        rw [smul_smul, mul_comm, ← hb']
        exact M'.smul_mem b' (hv i)
      · intro x y hx hy
        rw [mul_add]; exact Submodule.add_mem _ hx hy
    simpa using this 1 h1m
  · apply Submodule.smul_le.2
    intro a ha x hx
    have : detSpan M ≤ (detSpan M').comap (LinearMap.lsmul (𝓞 E) E a) := by
      apply Submodule.span_le.2
      intro d hd
      obtain ⟨v, hv, rfl⟩ := (mem_detSet M d).1 hd
      exact smul_det_mem M' m a ha v hv
    exact this hx
end GlobalTheory.BetaEx
