-- Prove2me | solution 1 for GlobalTheory.AbLaw.CechOne.exists_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:47:59.843714+00:00
-- url     : https://prove2.me/submissions/1bbad7eb-70e6-4e3f-9bee-ba8157912cff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CechHOneVanishesOnOpenOfIsAffineOpen
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_chart_restrict
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CechOne
open SecOn
variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable {M : LB X}
namespace GlobalTheory.AbLaw.CechOne
theorem _root_.solution (hM : M.IsLB) {V U W : X.Opens} (hU : IsAffineOpen U) (hUV : U ≤ V) (i : M.ι)
    (hi : U ≤ M.U i) (t : Γ(X, V)) (hW : W = U ⊓ X.basicOpen t) (φ : SecOn M W) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∃ ρ : SecOn M U, restrict M (hW.le.trans inf_le_left) ρ =
      rs X ((hW.le.trans inf_le_left).trans hUV) t ^ n • φ := by
  have e : W = X.basicOpen (rs X hUV t) := by rw [hW]; exact (X.basicOpen_res t _).symm
  subst e
  have := hU.isLocalization_basicOpen (rs X hUV t)
  obtain ⟨⟨ρ, _, n₀, rfl⟩, h⟩ := IsLocalization.surj (Submonoid.powers (rs X hUV t))
    (chart hM i ((X.basicOpen_le _).trans hi) φ)
  refine ⟨n₀, fun n hn => ⟨(chart hM i hi).symm (rs X hUV t ^ (n - n₀) * ρ), ?_⟩⟩
  have h' : chart hM i ((X.basicOpen_le _).trans hi) φ * rs X (X.basicOpen_le _) (rs X hUV t ^ n₀) =
      rs X (X.basicOpen_le _) ρ := h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  apply (chart hM i ((X.basicOpen_le _).trans hi)).injective
  rw [chart_restrict hM i hi, LinearEquiv.apply_symm_apply, map_smul, smul_eq_mul,
    map_mul, ← h', map_pow, map_pow, rs_rs, Nat.add_sub_cancel_left]
  ring
end GlobalTheory.AbLaw.CechOne
