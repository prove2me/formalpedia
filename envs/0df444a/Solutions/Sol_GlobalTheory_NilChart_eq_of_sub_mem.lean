-- Prove2me | solution 1 for GlobalTheory.NilChart.eq_of_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:52:06.608094+00:00
-- url     : https://prove2.me/submissions/4e2dbd28-a551-43b8-a491-f4d8051a2df7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetPointAddSqZeroEqProdMulTangent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueCoord
import Theorems.Thm_GlobalTheory_NilChart_move
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_mul_eq_zero_of_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.NilChart
open SqZero
variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (hG : Smooth G.hom) {d : ℕ}
  {v : Fin d → (epsR R ⟶ G)} (hv : IsLieBasis v) {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G}
  (hx₁ : ∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m)
  (hx₂ : ∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1)
  (hx₃ : ∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j)
include hG hv hx₁ hx₂ hx₃
namespace GlobalTheory.NilChart
theorem _root_.solution {I J : Ideal B} (hJ : J * I = ⊥) (hle : J ≤ I) {m : ℕ} (ψ ψ' : JetR R (Fin d) m →ₐ[R] B)
    (hψ : ∀ j, ψ (zR m j) ∈ I) (hδ : ∀ j, ψ' (zR m j) - ψ (zR m j) ∈ J)
    (h : spMap ψ ≫ x m = spMap ψ' ≫ x m) : ψ = ψ' := by
  have hJ2 : J ^ 2 = ⊥ := by
    rw [← le_bot_iff, pow_two, ← hJ]
    exact Ideal.mul_mono_right hle
  let c : Fin d → J := fun j => ⟨_, hδ j⟩
  have hc : ∀ j, (c j : B) * (c j : B) = 0 := fun j => mul_eq_zero_of_sq hJ2 (c j).2 (c j).2
  have key := move hG hv hx₁ hx₂ hx₃ hJ hle ψ ψ' hψ (fun j => c j) (fun j => (c j).2) hc
    (fun j => (add_sub_cancel _ _).symm)
  rw [← h] at key
  have h1 : lieExp v (fun j => (c j : B)) hc = 1 := mul_eq_right.1 key.symm
  have h0 : c = 0 := by
    apply (expHom_bijective hv hJ2).1
    rw [map_zero]
    exact congrArg Additive.ofMul (Subtype.ext h1)
  refine jet_ext fun j => ?_
  have : ψ' (zR m j) - ψ (zR m j) = 0 := congrArg Subtype.val (congrFun h0 j)
  exact (sub_eq_zero.1 this).symm
end GlobalTheory.NilChart
