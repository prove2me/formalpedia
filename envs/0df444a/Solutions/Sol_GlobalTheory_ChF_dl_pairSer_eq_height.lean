-- Prove2me | solution 1 for GlobalTheory.ChF.dl_pairSer_eq_height
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:34:29.538736+00:00
-- url     : https://prove2.me/submissions/3f5df79c-4f3f-4125-b00f-34a3d31d4066

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NEvalSqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LinearPartPairingSeriesEqHeight
import Theorems.Thm_GlobalTheory_ChF_nv_calculus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChF
namespace GlobalTheory.ChF
theorem _root_.solution : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (p : ℕ) (Tw : ATowerL R₀ p) (Dt : DualTower Tw) (g : ℕ) (Y : ∀ R : LAlg R₀, LHom Tw.O R → (Fin g → (R : Type)) → B.G R) (gb : Module.Basis (Fin g) R₀ B.gg) (S : Matrix (Fin g) (Fin g) (Tw.O : Type)), TanMat B Tw.O Y gb S → ∀ (τ : ℕ → B.G Tw.O) (u : PS (Tw.O : Type) 1 g), MvPowerSeries.constantCoeff u = 1 → PairSer B Tw.O Y p τ u → ∀ ht : B.gg →ₗ[R₀] (Tw.O : Type), (∀ n, B.IsHeight (Dt.Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ n)) ((Tw.q n).1.toLinearMap ∘ₗ ht)) → Sᵀ *ᵥ dl u = fun l => ht (gb l) := by
  intro R₀ _ B p Tw Dt g Y gb S hS τ u hu hP ht hH
  funext l
  rw [← sub_eq_zero]
  refine Tw.sep _ fun n => (Dt.Dp n).free _ ?_
  set Dp := Dt.Dp n
  obtain ⟨z, hz, hz'⟩ := hH n (gb l)
  let s : LHom Tw.O Dp.D := Dp.σ.comp (Tw.q n)
  have hs : ∀ x, s.1 x = Dp.σ.1 ((Tw.q n).1 x) := fun _ => rfl
  have hc : ((p ^ (n + 1) : ℕ) : (Tw.R n : Type)) = 0 := by
    rw [← map_natCast (Tw.π n).1, Tw.char n, map_zero]
  have hp : IsNilpotent (p : (Dp.D : Type)) :=
    ⟨n + 1, by rw [← Nat.cast_pow, ← map_natCast Dp.σ.1, hc, map_zero]⟩
  have hsq : ∀ x y : (Dp.D : Type), x * Dp.η * (y * Dp.η) = 0 := fun x y => by
    rw [_root_.mul_mul_mul_comm, Dp.η_sq, mul_zero]
  have ha : ∀ k, IsNilpotent (s.1 (S k l) * Dp.η) := fun k => ⟨2, by rw [pow_two, hsq]⟩
  rw [hS Dp.D _ s Dp.π Dp.sqZero l Dp.ηk, ← B.map_comp] at hz
  have h1 := hP Dp.D s (fun k => s.1 (S k l) * Dp.η) n z hp ha hz
  have h2 := (nv_calculus _ _ s.1.toRingHom 1 g ![fun k => s.1 (S k l) * Dp.η]
    (fun i j => by simpa using ha j)).2.2.2.2.2 (fun i j i' j' => by simpa using hsq _ _) u
  rw [h2, hz', hu, map_one, add_right_inj, Fintype.sum_prod_type, Fin.sum_univ_one] at h1
  rw [← hs, map_sub, sub_mul, sub_eq_zero]
  refine Eq.trans ?_ h1.symm
  simp only [mulVec, dotProduct, transpose_apply, dl, map_sum, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.cons_val_fin_one, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  ring
end GlobalTheory.ChF
