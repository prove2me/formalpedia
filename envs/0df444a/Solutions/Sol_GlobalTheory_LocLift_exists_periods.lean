-- Prove2me | solution 1 for GlobalTheory.LocLift.exists_periods
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:58:14.902412+00:00
-- url     : https://prove2.me/submissions/ee62b2a4-c3cd-4d98-ad67-24d706dc447d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolLinearLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TwoMulEqOfIsTypeFn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HolomorphicMapModuliLiftsLocallyToPeriods
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_LocLift_HasLifts_lift
import Theorems.Thm_GlobalTheory_LocLift_isHolTo_comp_hom
import Theorems.Thm_GlobalTheory_LocLift_isHolTo_congr
import Theorems.Thm_GlobalTheory_LocLift_isOpen_ne_one
import Theorems.Thm_GlobalTheory_LocLift_mem_homKer
import Theorems.Thm_GlobalTheory_LocLift_one_left
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk
attribute [local simp] GlobalTheory.coe_symplecticGroupMap
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology
open GlobalTheory GlobalTheory.LocLift
noncomputable section
variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {g m : ℕ}
namespace GlobalTheory.LocLift
theorem _root_.solution
    (hLat : ∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (g m : ℕ) (B : Set (Fin m → ℂ)) (b₀ : Fin m → ℂ) (K : (Fin m → ℂ) → AddSubgroup (Fin g → ℂ)) (P : (Fin m → ℂ) → (La →+ (Fin g → ℂ))) (r : ℝ), IsOpen B → b₀ ∈ B → 0 < r → (∀ b ∈ B, ∀ z ∈ K b, ‖z‖ < r → z = 0) → (∀ (b : ℕ → (Fin m → ℂ)) (z : ℕ → (Fin g → ℂ)) (z₀ : Fin g → ℂ), Filter.Tendsto b Filter.atTop (nhds b₀) → Filter.Tendsto z Filter.atTop (nhds z₀) → (∀ i, z i ∈ K (b i)) → z₀ ∈ K b₀) → (∀ x, ContinuousAt (fun b => P b x) b₀) → (∀ b ∈ B, (P b).range ≤ K b) → (P b₀).range = K b₀ → Function.Injective (P b₀) → Submodule.span ℝ (Set.range (P b₀)) = ⊤ → ∀ᶠ b in nhds b₀, (P b).range = K b ∧ Function.Injective (P b) ∧ Submodule.span ℝ (Set.range (P b)) = ⊤ ∧ DiscreteTopology (P b).range)
    [IsSeparated G.hom] {B : Set (Fin m → ℂ)} (hB : IsOpen B) {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B)
    {y : (Fin m → ℂ) → (Sp ℂ ⟶ X)} (hy : IsHolTo B y) {e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ G)} {r : ℝ}
    (hr : 0 < r) (hol : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left))
    (he : ∀ b ∈ B, IsExp (y b) (e b) ∧ ∀ z, ‖z‖ < r → e b z = 1 → z = 0) (hl : HasLifts B y e)
    {La : Type} [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (P₀ : La →+ (Fin g → ℂ))
    (hi : Function.Injective P₀) (hs : Submodule.span ℝ (Set.range P₀) = ⊤) (hk : ∀ z, e b₀ z = 1 ↔ z ∈ P₀.range) :
    ∃ P : (Fin m → ℂ) → (La →+ (Fin g → ℂ)), P b₀ = P₀ ∧ ∀ᶠ b in 𝓝 b₀,
      (∀ x, DifferentiableAt ℂ (fun b => P b x) b) ∧ (∀ z, e b z = 1 ↔ z ∈ (P b).range) ∧
      Function.Injective (P b) ∧ Submodule.span ℝ (Set.range (P b)) = ⊤ ∧ DiscreteTopology (P b).range := by
  classical
  let bs := Module.Free.chooseBasis ℤ La
  choose ζ h1 h2 h3 using fun i => hl.lift (W := B) (β := id) (fun b => (1 : Over.mk (y b) ⟶ G)) (w₀ := b₀)
    (z₀ := P₀ (bs i)) hB hb₀ differentiableOn_id (fun _ h => h)
    (isHolTo_congr (isHolTo_comp_hom hy η[G].left) fun b _ => one_left _) ((hk _).2 ⟨_, rfl⟩)
  let P : (Fin m → ℂ) → (La →+ (Fin g → ℂ)) := fun b => (bs.constr ℤ fun i => ζ i b).toAddMonoidHom
  have hP : ∀ b x, P b x = ∑ i, bs.equivFun x i • ζ i b := fun b x => bs.constr_apply_fintype ℤ _ x
  have hP₀ : P b₀ = P₀ := by
    have : (bs.constr ℤ fun i => ζ i b₀) = P₀.toIntLinearMap := bs.ext fun i => by
      rw [bs.constr_basis, h1]; rfl
    ext1 x
    exact DFunLike.congr_fun this x
  have hd : ∀ᶠ b in 𝓝 b₀, ∀ x, DifferentiableAt ℂ (fun b => P b x) b := by
    filter_upwards [eventually_all.2 fun i => (h2 i).eventually_analyticAt] with b hb x
    simp only [hP]
    exact DifferentiableAt.fun_sum fun i _ => (hb i).differentiableAt.fun_const_smul _
  let K : (Fin m → ℂ) → AddSubgroup (Fin g → ℂ) := fun b => if hb : b ∈ B then homKer (he b hb).1.1 else ⊥
  have hK : ∀ b ∈ B, ∀ z, z ∈ K b ↔ e b z = 1 := fun b hb z => by simp only [K, dif_pos hb, mem_homKer]
  obtain ⟨C, hC, hCo, hC₀⟩ := eventually_nhds_iff.1 ((eventually_all.2 h3).and (hB.mem_nhds hb₀))
  have := hLat La g m C b₀ K P r hCo hC₀ hr
    (fun b hb z hz hn => (he b (hC b hb).2).2 z hn ((hK b (hC b hb).2 z).1 hz)) (fun b z z₀ hb hz hm => ?_)
    (fun x => (hd.self_of_nhds x).continuousAt) (fun b hb => ?_)
    (by rw [hP₀]; ext z; rw [hK b₀ hb₀, hk]) (hP₀ ▸ hi) (hP₀ ▸ hs)
  · refine ⟨P, hP₀, ?_⟩
    filter_upwards [this, hd, hB.mem_nhds hb₀] with b h h' hb
    exact ⟨h', fun z => by rw [h.1, hK b hb], h.2⟩
  · rw [hK b₀ hb₀]
    by_contra hne
    have ho := isOpen_ne_one (y := fun bz : (Fin m → ℂ) × (Fin g → ℂ) => y bz.1) hol
    obtain ⟨i, hi1, hi2⟩ := ((hb.prodMk_nhds hz).eventually (ho.mem_nhds ⟨⟨hb₀, trivial⟩, hne⟩)).exists
    exact hi2 ((hK _ hi1.1 _).1 (hm i))
  · rintro _ ⟨x, rfl⟩
    rw [hP]
    exact sum_mem fun i _ => zsmul_mem ((hK b (hC b hb).2 _).2 ((hC b hb).1 i)) _
end GlobalTheory.LocLift
