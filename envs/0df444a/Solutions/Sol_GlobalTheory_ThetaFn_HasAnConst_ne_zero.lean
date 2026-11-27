-- Prove2me | solution 1 for GlobalTheory.ThetaFn.HasAnConst.ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:38:53.670394+00:00
-- url     : https://prove2.me/submissions/135de9d3-8536-4b3a-b955-b965d55f945b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasAnConstThetaGrpZeroIff
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_mem_twist_chart_iff
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_translPt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
namespace GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter AppellHumbertTrivial
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
private theorem exists_algChart_mem_source (hL : L.IsLB) (f : Sp ℂ ⟶ A.left) : ∃ i, ⊤ ≤ f ⁻¹ᵁ L.U i := by
  obtain ⟨cover, -, -⟩ := hL
  obtain ⟨a0⟩ : Nonempty (PrimeSpectrum ℂ) := inferInstance
  have hmem : f.base a0 ∈ (⨆ i, L.U i) := by
    rw [cover]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
  refine ⟨i, fun a _ => ?_⟩
  have hsub : a = a0 := Subsingleton.elim (α := PrimeSpectrum ℂ) a a0
  rw [hsub]
  exact hi
private theorem valAt'_unit_ne_zero_cusp_form_evaluations {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ U) (f : Γ(X, U)ˣ) : valAt' y U f.val ≠ 0 := by
  unfold valAt'
  rw [dif_pos h]
  unfold valAt
  exact (Units.map ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (y.appLE U ⊤ h).hom).toMonoidHom f).ne_zero
variable {u p} {Hm : Matrix (Fin g) (Fin g) ℂ} {k : ℤ} {Θ : ThetaGrp A L k T} {x : Fin g → ℂ}
end GlobalTheory.ThetaFn
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter AppellHumbertTrivial
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
variable {u p} {Hm : Matrix (Fin g) (Fin g) ℂ} {k : ℤ} {Θ : ThetaGrp A L k T} {x : Fin g → ℂ}
namespace GlobalTheory.ThetaFn
namespace HasAnConst
theorem _root_.solution (hL : L.IsLB) {c : ℂ} (h : HasAnConst u p Hm Θ x c) : c ≠ 0 := by
  obtain ⟨i0, hi0⟩ := exists_algChart_mem_source hL (u.ex 0).left
  obtain ⟨i1, hi1⟩ := exists_algChart_mem_source hL (u.ex (0 + x)).left
  have e := h.2 ![i0, i1] 0 hi0 hi1
  intro hc
  rw [hc, zero_mul, zero_mul] at e
  have hch := (exAt_mem_twist_chart_iff u p (exAt_translPt u h.1 0) ![i0, i1]).2 ⟨hi0, hi1⟩
  have hv := valAt'_unit_ne_zero_cusp_form_evaluations (exAt u p 0) _ hch (Θ.φ.s ![i0, i1])
  exact mul_ne_zero hv (zpow_ne_zero k (u.fr_ne _ _ hi1)) e
end HasAnConst
end GlobalTheory.ThetaFn
