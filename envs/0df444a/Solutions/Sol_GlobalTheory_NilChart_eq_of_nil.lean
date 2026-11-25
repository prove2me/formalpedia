-- Prove2me | solution 1 for GlobalTheory.NilChart.eq_of_nil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:59:23.79379+00:00
-- url     : https://prove2.me/submissions/23a369f4-fb95-4180-adbb-2af6bedd909c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetPointAddSqZeroEqProdMulTangent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueCoord
import Theorems.Thm_GlobalTheory_NilChart_eq_of_sub_mem
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp


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
theorem _root_.solution {N : Ideal B} (hN : IsNilpotent N) {m : ℕ} (ψ ψ' : JetR R (Fin d) m →ₐ[R] B)
    (hψ : ∀ j, ψ (zR m j) ∈ N) (hψ' : ∀ j, ψ' (zR m j) ∈ N)
    (h : spMap ψ ≫ x m = spMap ψ' ≫ x m) : ψ = ψ' := by
  have main : ∀ k j, ψ' (zR m j) - ψ (zR m j) ∈ N ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro j
      rw [zero_add, pow_one]
      exact sub_mem (hψ' j) (hψ j)
    | succ k ih =>
      let q : B →ₐ[R] B ⧸ N ^ (k + 1 + 1) := Ideal.Quotient.mkₐ R _
      have e := eq_of_sub_mem hG hv hx₁ hx₂ hx₃ (I := N.map q) (J := (N ^ (k + 1)).map q)
        (by rw [← Ideal.map_mul, ← pow_succ]; exact Ideal.map_quotient_self _)
        (Ideal.map_mono (Ideal.pow_le_self (by omega)))
        (q.comp ψ) (q.comp ψ') (fun j => Ideal.mem_map_of_mem _ (hψ j))
        (fun j => by
          rw [AlgHom.comp_apply, AlgHom.comp_apply, ← map_sub]
          exact Ideal.mem_map_of_mem _ (ih j))
        (by rw [← spMap_comp, ← spMap_comp, Category.assoc, Category.assoc, h])
      intro j
      exact Ideal.Quotient.eq.1 (AlgHom.congr_fun e (zR m j)).symm
  obtain ⟨n, hn⟩ := hN
  refine jet_ext fun j => ?_
  have := main n j
  rw [pow_succ, hn, zero_mul, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  exact (sub_eq_zero.1 this).symm
end GlobalTheory.NilChart
