-- Prove2me | solution 1 for GlobalTheory.TorsionCoset.exists_ne_zero_on_coset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:06:28.624804+00:00
-- url     : https://prove2.me/submissions/a515ab82-8a11-4fd1-96b2-11eb72c53ffc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TBNFinal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNeZeroPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNeZeroOnCoset
import Theorems.Thm_GlobalTheory_TorsionCoset_isPi_natCast
import Theorems.Thm_GlobalTheory_TorsionCoset_exists_isReps
import Theorems.Thm_GlobalTheory_BasePointFree_exists_sec_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_thetaBasis_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.TorsionCoset
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.TorsionCoset
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E)
    (s : (Fin 1 → Vsp X.dim) → ℂ) (hs : s ∈ X.Sec 1 1) (h0 : s ≠ 0) (n : ℕ) (hn : 2 ≤ n)
    (a : Vsp X.dim) : ∃ y ∈ X.L, s (fun _ => a + ((n : ℂ)⁻¹) • y) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hn0 : n ≠ 0 := by omega
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn0
  have hq : 2 ≤ n ^ 2 := by nlinarith
  obtain ⟨K, hK⟩ := exists_isReps X n hn0
  obtain ⟨-, -, -, hspan⟩ :=
    thetaBasis_holds E X (n ^ 2) 1 _ (by omega) (isPi_natCast X n) s hs h0 K hK
  obtain ⟨F, hF, hFv⟩ := GlobalTheory.BasePointFree.exists_sec_ne_zero E X s hs h0 (n ^ 2) hq
    (fun _ => (n : ℂ)⁻¹ • a)
  apply hFv
  have hle : Submodule.span ℂ ((fun b => X.U (n ^ 2) b (s0 X ((n : ℂ) • LinearMap.id) s)) ''
      (K : Set _)) ≤ LinearMap.ker (LinearMap.proj (R := ℂ) (φ := fun _ => ℂ)
        (fun _ : Fin 1 => (n : ℂ)⁻¹ • a)) := by
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    have h := hcon _ (neg_mem (hK.1 b hb 0))
    have e : a + (n : ℂ)⁻¹ • -(((n ^ 2 : ℕ) : ℂ) • b 0) = (n : ℂ) • ((n : ℂ)⁻¹ • a - b 0) := by
      rw [smul_sub, smul_inv_smul₀ hn', smul_neg, smul_smul, sub_eq_add_neg]
      congr 3
      push_cast
      field_simp
    rw [e] at h
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply, PT.U, s0,
      Fin.prod_univ_one, LinearMap.smul_apply, LinearMap.id_apply, Pi.sub_apply, h, mul_zero]
  exact hle (hspan hF)
end GlobalTheory.TorsionCoset
