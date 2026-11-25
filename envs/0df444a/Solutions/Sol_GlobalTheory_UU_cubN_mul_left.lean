-- Prove2me | solution 1 for GlobalTheory.UU.cubN_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:05:13.214003+00:00
-- url     : https://prove2.me/submissions/6dc5361b-68fb-4606-adee-5f9e184edbe4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubWeilOneLeft
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU
private theorem isCub_mul_swap_middle {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
    (a b c d y : A) :
    θ a b y * θ (a * b) (c * d) y * θ c d y = θ (a * c) (b * d) y * θ a c y * θ b d y := by
  have e1 : θ a b y * θ (a * b) (c * d) y = θ a (b * (c * d)) y * θ b (c * d) y := by
    rw [_root_.mul_comm]; exact h.coc a b (c * d) y
  have e2 : θ b (c * d) y * θ c d y = θ (b * c) d y * θ b c y := (h.coc b c d y).symm
  have e3 : θ (a * c) (b * d) y * θ a c y = θ a (c * (b * d)) y * θ c (b * d) y := h.coc a c (b * d) y
  have e4 : θ c (b * d) y * θ b d y = θ (c * b) d y * θ c b y := (h.coc c b d y).symm
  rw [e1, _root_.mul_assoc, e2, e3, _root_.mul_assoc, e4, _root_.mul_comm c b, h.s01 c b, mul_left_comm c b d]
private theorem v_sub_one_add_le_v_pow_l_sub_one {U : Type} [CommGroup U] {P B C D Px Px' D' E F : U} {k : ℕ}
    (ih : P * C ^ k = D * Px * Px') (e : D * B * C = D' * E * F) :
    P * B * C ^ (k + 1) = D' * (Px * E) * (Px' * F) := by
  calc P * B * C ^ (k + 1) = (P * C ^ k) * (B * C) := by rw [pow_succ]; ac_rfl
    _ = Px * Px' * (D * B * C) := by rw [ih]; ac_rfl
    _ = D' * (Px * E) * (Px' * F) := by rw [e]; ac_rfl
section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {c : CubicalStr G L} {N : ℕ}
  {T : Over S} {x x' y : T ⟶ G}
end
end GlobalTheory.UU
end
end

set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU
namespace GlobalTheory.UU
theorem _root_.solution {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ) (k : ℕ)
    (x x' y : A) :
    cubN θ k 1 (x * x') y * θ x x' y ^ k = θ (x ^ k) (x' ^ k) y * cubN θ k 1 x y * cubN θ k 1 x' y := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [pow_succ x, pow_succ x', mul_pow x x' k]
    exact v_sub_one_add_le_v_pow_l_sub_one ih (isCub_mul_swap_middle h (x ^ k) (x' ^ k) x x' y)
end GlobalTheory.UU
