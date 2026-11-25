-- Prove2me | solution 1 for GlobalTheory.TorusAlg.frame_eq_autFactor_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:09:33.012416+00:00
-- url     : https://prove2.me/submissions/6f32942c-185e-466d-9029-d074550f79cc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
import Theorems.Thm_GlobalTheory_TorusAlg_thetaChar_eq_theta
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_ex_add
import Theorems.Thm_ReciprocityTheory_PTheta_thetaQuasiPeriod_holds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.TorusAlg
open ReciprocityTheory.PTheta
variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ}
namespace GlobalTheory.TorusAlg
theorem _root_.solution {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L g) (th : L.Sec)
    (hs : τ.IsSymm) (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (hb : ∀ i, b i = 0 ∨ b i = 1 / 2)
    (hΛ : ∀ z, z ∈ u.Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))
    (hth : u.IsFn th (thetaChar τ a b)) (k k' : Fin g → ℤ) (i : L.ι) (z : Fin g → ℂ)
    (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i) (h0 : thetaChar τ a b z ≠ 0) :
    u.fr i z = autFactor (fun i => (a i).re) (fun i => (b i).re) τ k k' z *
      u.fr i (z + τ *ᵥ ofIntVec k + ofIntVec k') := by
  have hl : u.ex (τ *ᵥ ofIntVec k + ofIntVec k') = 1 := (u.ker _).2 ((hΛ _).2 ⟨k', k, add_comm _ _⟩)
  have he : u.ex (z + τ *ᵥ ofIntVec k + ofIntVec k') = u.ex z := by
    rw [add_assoc, u.ex_add, hl, _root_.mul_one]
  have h1 := hth i z hz
  have h2 := hth i (z + τ *ᵥ ofIntVec k + ofIntVec k') (by rw [he]; exact hz)
  rw [he, h1] at h2
  rw [thetaChar_eq_theta τ ha hb] at h2 h0
  simp only [thetaQuasiPeriod_holds _ _ _ z τ k k' hs] at h2 h0
  apply mul_left_cancel₀ h0
  rw [h2]; ring
end GlobalTheory.TorusAlg
