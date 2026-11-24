-- Prove2me | solution 1 for GlobalTheory.Ex.QStr.exists_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:44:44.540858+00:00
-- url     : https://prove2.me/submissions/8e2bec6a-cb7a-49ba-ba9d-c9a6c295f7ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Theorems.Thm_GlobalTheory_Ex_QStr_chr_apply
import Theorems.Thm_GlobalTheory_Ex_QStr_exists_roots

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.QStr
variable {C : Type} [Field C] [IsAlgClosed C] (N : NumD C) {k : ℕ}
namespace GlobalTheory.Ex.QStr
theorem _root_.solution (hk : (k : C) ≠ 0) (y : N.X)
    (h : ∀ t : Multiplicative N.X →* Cˣ, t ^ k = 1 → t (Multiplicative.ofAdd y) = 1) : ∃ z : N.X, y = k • z := by
  classical
  obtain ⟨ζ, hζ, -⟩ := exists_roots C k hk
  let v := Module.finBasis ℤ N.X
  have hd : ∀ i, (k : ℤ) ∣ v.repr y i := fun i => by
    rw [← hζ.zpow_eq_one_iff_dvd]
    have := h (chr v (Pi.mulSingle i ζ)) (by rw [← map_pow, ← Pi.mulSingle_pow, hζ.pow_eq_one, Pi.mulSingle_one, map_one])
    rw [chr_apply, Finset.prod_eq_single i] at this
    · simpa using this
    · intro j _ hj
      simp [Pi.mulSingle_eq_of_ne hj]
    · simp
  choose c hc using hd
  refine ⟨∑ i, c i • v i, ?_⟩
  conv_lhs => rw [← v.sum_repr y]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hc, mul_smul, natCast_zsmul]
end GlobalTheory.Ex.QStr
