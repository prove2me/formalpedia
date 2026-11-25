-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.cycZ_weil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:07:43.778596+00:00
-- url     : https://prove2.me/submissions/03b46c5d-21dd-4671-bd97-d1442387432a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ToZModPowKummerEqIff
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpChar_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_lpSp
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDual_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpSum_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_unr_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_exists_eq_zpow_mul
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
import Theorems.Thm_ReciprocityTheory_Gal_cycZ_of_isFrob
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpChar_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_lpSp
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDual_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpSum_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.unr_mk
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.WeilDeligne
theorem _root_.solution {h : IsPlaceOver A w} (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (g : Weil h) :
    (((cycZ E Ω l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = ((normV w : ℕ) : ℚ_[l]) ^ deg g := by
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) g
  have h1 : cycZ E Ω l g = cycZ E Ω l (frob h) ^ deg g := by
    conv_lhs => rw [hτ]
    rw [Subgroup.coe_mul, map_mul, coe_ineIncl, cycZ_of_mem_Ine h hl τ.2, mul_one,
      Subgroup.coe_zpow, map_zpow]
  have h2 := map_zpow ((PadicInt.Coe.ringHom (p := l) : ℤ_[l] →* ℚ_[l]).comp (Units.coeHom _)).toHomUnits
    (cycZ E Ω l (frob h)) (deg g)
  have h3 := congrArg Units.val h2
  rw [Units.val_zpow_eq_zpow_val] at h3
  rw [h1]
  refine h3.trans ?_
  congr 1
  show (((cycZ E Ω l (frob h) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = _
  rw [cycZ_of_isFrob hl h isFrob_frob]
  simp
end GlobalTheory.WeilDeligne
