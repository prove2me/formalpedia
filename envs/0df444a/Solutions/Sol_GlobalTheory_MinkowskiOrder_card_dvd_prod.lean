-- Prove2me | solution 1 for GlobalTheory.MinkowskiOrder.card_dvd_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:03:05.740246+00:00
-- url     : https://prove2.me/submissions/1f16d3eb-8d37-48c4-97e3-743571c7c77b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsInvariantNatLengthLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardFiniteSubgroupGLIntDvd
import Theorems.Thm_GlobalTheory_end_eq_one_of_pow_eq_one_of_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.MinkowskiOrder
namespace GlobalTheory.MinkowskiOrder
theorem _root_.solution (n : ℕ) (G : Subgroup (GL (Fin n) ℤ)) [Finite G] (l : ℕ) (hl : l.Prime)
    (h3 : 3 ≤ l) : Nat.card G ∣ ∏ i : Fin n, (l ^ n - l ^ (i : ℕ)) := by
  haveI := Fact.mk hl
  let f : G →* GL (Fin n) (ZMod l) :=
    (Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod l))).comp G.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hm : 0 < orderOf g := orderOf_pos g
    have hpow : ((g : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ) ^ orderOf g = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, pow_orderOf_eq_one]
      rfl
    have hent : ∀ i j, (l : ℤ) ∣ (((g : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ) - 1) i j := by
      intro i j
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have h1 := congrArg (fun u : GL (Fin n) (ZMod l) => (u : Matrix (Fin n) (Fin n) (ZMod l)) i j) hg
      have h2 : ((((g : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ) i j : ℤ) : ZMod l)
          = (1 : Matrix (Fin n) (Fin n) (ZMod l)) i j := h1
      rw [Matrix.sub_apply, Int.cast_sub, h2, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    choose B hB using hent
    have key := end_eq_one_of_pow_eq_one_of_congr (Fin n → ℤ)
      (Matrix.toLin' ((g : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ)) (orderOf g) l hm
      (by rw [← Matrix.toLin'_pow, hpow, Matrix.toLin'_one]; rfl) h3 (by
        intro y
        refine ⟨(Matrix.of B).mulVec y, ?_⟩
        have e : ((g : GL (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ) = 1 + l • Matrix.of B := by
          ext i j
          have := hB i j
          rw [Matrix.sub_apply] at this
          rw [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, ← this]
          ring
        rw [Matrix.toLin'_apply, e, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec])
    apply Subtype.ext
    apply Units.ext
    apply Matrix.toLin'.injective
    rw [key]
    exact Matrix.toLin'_one.symm
  have h := Subgroup.card_dvd_of_injective f hf
  rwa [Matrix.card_GL_field, ZMod.card] at h
end GlobalTheory.MinkowskiOrder
