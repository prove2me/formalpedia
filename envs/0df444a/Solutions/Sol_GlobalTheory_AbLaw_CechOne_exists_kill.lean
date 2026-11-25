-- Prove2me | solution 1 for GlobalTheory.AbLaw.CechOne.exists_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:48:01.132559+00:00
-- url     : https://prove2.me/submissions/c55f9083-8e53-452b-96a6-22cd396f53ba

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CechHOneVanishesOnOpenOfIsAffineOpen
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_chart_restrict
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom



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
    (hi : U ≤ M.U i) (t : Γ(X, V)) (hW : W = U ⊓ X.basicOpen t) (φ : SecOn M U)
    (h : restrict M (hW.le.trans inf_le_left) φ = 0) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → rs X hUV t ^ n • φ = 0 := by
  have e : W = X.basicOpen (rs X hUV t) := by rw [hW]; exact (X.basicOpen_res t _).symm
  subst e
  have := hU.isLocalization_basicOpen (rs X hUV t)
  have h₁ := congrArg (chart hM i ((X.basicOpen_le _).trans hi)) h
  rw [chart_restrict hM i hi, map_zero] at h₁
  obtain ⟨⟨_, n₀, rfl⟩, h'⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (rs X hUV t))
    Γ(X, X.basicOpen (rs X hUV t)) _).1 h₁
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  apply (chart hM i hi).injective
  simp only at h'
  rw [map_smul, smul_eq_mul, map_zero]
  linear_combination rs X hUV t ^ d * h'
end GlobalTheory.AbLaw.CechOne
