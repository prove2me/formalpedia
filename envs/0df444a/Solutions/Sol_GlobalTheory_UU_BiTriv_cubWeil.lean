-- Prove2me | solution 1 for GlobalTheory.UU.BiTriv.cubWeil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:04:12.513625+00:00
-- url     : https://prove2.me/submissions/767e2e49-c7e4-4a82-a163-17a3e0d5ae40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S S' : Scheme.{0}}
attribute [instance] TQ.grp TQ.comm
variable {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] {L : RigLB G} {c : CubicalStr G L} {N : ℕ}
  {T : Over S} {x y : T ⟶ G}
variable {i : H ⟶ G} {z : T.left} {J : (T.left ⟶ G.left) → L.L.ι}
namespace GlobalTheory.UU
namespace BiTriv
theorem _root_.solution [IsMonHom i] (σ : BiTriv c i) {t : T ⟶ H} (ht : t ^ N = 1) (hx : x ^ N = 1) :
    CubWeil c N (t ≫ i) x 1 := by
  refine ⟨by rw [← MonObj.pow_comp, ht, MonObj.one_comp], hx, fun z J hJ => ?_⟩
  have hcub := isCub_cubV c hJ
  have tele : ∀ (f g : ℕ → (T.left.presheaf.stalk z)ˣ) (a : (T.left.presheaf.stalk z)ˣ), f N = f 0 →
      (∀ k, g k = f (k + 1) / f k * a⁻¹) → ∏ k ∈ Finset.range N, g k = (a ^ N)⁻¹ := by
    intro f g a hN hg
    rw [Finset.prod_congr rfl fun k _ => hg k, Finset.prod_mul_distrib, Finset.prod_range_div, hN, div_self',
      Finset.prod_const, Finset.card_range, _root_.one_mul, inv_pow]
  have A : cubN (cubV c z J) N 1 (t ≫ i) x = ((val σ.s (lift t x).left z J) ^ N)⁻¹ := by
    refine tele (fun k => val σ.s (lift (t ^ k) x).left z J) (fun k => cubV c z J (1 * (t ≫ i) ^ k) (t ≫ i) x) _
      (by simp only [ht, pow_zero]) fun k => ?_
    have e := σ.law1 T (t ^ k) t x z J hJ
    rw [← pow_succ] at e
    simp only [_root_.one_mul, ← MonObj.pow_comp]
    rw [e]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_inv]
    abel
  have B : cubN (cubV c z J) N 1 x (t ≫ i) = ((val σ.s (lift t x).left z J) ^ N)⁻¹ := by
    refine tele (fun k => val σ.s (lift t (x ^ k)).left z J) (fun k => cubV c z J (1 * x ^ k) x (t ≫ i)) _
      (by simp only [hx, pow_zero]) fun k => ?_
    have e := σ.law2 T t (x ^ k) x z J hJ
    rw [← pow_succ] at e
    simp only [_root_.one_mul]
    rw [hcub.s12 (x ^ k) x (t ≫ i), hcub.s01 (x ^ k) (t ≫ i) x, e]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_inv]
    abel
  rw [map_one, _root_.one_mul, A, B]
end BiTriv
end GlobalTheory.UU
