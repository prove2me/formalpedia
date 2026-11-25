-- Prove2me | solution 1 for GlobalTheory.principalTorus_mem_lattice_of_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:03:23.349235+00:00
-- url     : https://prove2.me/submissions/4168c3e4-88a8-4f63-aefa-ec370d4256db

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_PrincipalTorusEqZeroOfImLattice
import Theorems.Thm_GlobalTheory_principalTorus_eq_zero_of_im_lattice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_im_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_im_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_im_antisymm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_im_zero_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
open scoped InnerProductSpace
open GlobalTheory
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory
theorem _root_.solution (X : PT E) {a : Vsp X.dim} (h : ∀ y ∈ X.L, ∃ k : ℤ, (Hf y a).im = k) :
    a ∈ X.L := by
  have hfl : ∀ y ∈ X.L, ((⌊(Hf y a).im⌋ : ℤ) : ℝ) = (Hf y a).im := by
    intro y hy
    obtain ⟨k, hk⟩ := h y hy
    rw [hk, Int.floor_intCast]
  let φ : X.L →+ ℤ :=
    { toFun := fun y => ⌊(Hf (y : Vsp X.dim) a).im⌋
      map_zero' := by simp [Hf_im_zero_left]
      map_add' := by
        intro y y'
        apply Int.cast_injective (α := ℝ)
        push_cast
        rw [hfl _ (X.L.add_mem y.2 y'.2), hfl _ y.2, hfl _ y'.2]
        simp only [Hf_im_add_left] }
  obtain ⟨x0, hx0, hφ⟩ := X.perfect φ
  have h0 : a + x0 = 0 := by
    apply principalTorus_eq_zero_of_im_lattice X
    intro y hy
    have := hφ ⟨y, hy⟩
    simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
    rw [hfl y hy] at this
    rw [Hf_im_add_right, this, Hf_im_antisymm x0 y]
    ring
  have : a = -x0 := eq_neg_of_add_eq_zero_left h0
  rw [this]
  exact X.L.neg_mem hx0
end GlobalTheory
