-- Prove2me | solution 1 for GlobalTheory.ThetaFn.HasAnConst.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:33:48.35603+00:00
-- url     : https://prove2.me/submissions/b23f2b8b-7995-4d4c-a6cf-28722512ba3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasAnConstThetaGrpZeroIff
import Theorems.Thm_GlobalTheory_ThetaFn_fockFactor_ne_zero
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
theorem _root_.solution (hL : L.IsLB) {c c' : ℂ} (h : HasAnConst u p Hm Θ x c)
    (h' : HasAnConst u p Hm Θ x c') : c = c' := by
  obtain ⟨i0, hi0⟩ := exists_algChart_mem_source hL (u.ex 0).left
  obtain ⟨i1, hi1⟩ := exists_algChart_mem_source hL (u.ex (0 + x)).left
  have e := h.2 ![i0, i1] 0 hi0 hi1
  have e' := h'.2 ![i0, i1] 0 hi0 hi1
  rw [e] at e'
  have hF := fockFactor_ne_zero Hm k x 0
  have hfr : u.fr (![i0, i1] 0) 0 ^ k ≠ 0 := zpow_ne_zero _ (u.fr_ne _ _ hi0)
  exact mul_right_cancel₀ hF (mul_right_cancel₀ hfr e')
end HasAnConst
end GlobalTheory.ThetaFn
