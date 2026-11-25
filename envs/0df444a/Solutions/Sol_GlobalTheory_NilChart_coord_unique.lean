-- Prove2me | solution 1 for GlobalTheory.NilChart.coord_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:55.810885+00:00
-- url     : https://prove2.me/submissions/2c1ff1f0-1def-42f3-b161-1e830f47d369

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetPointAddSqZeroEqProdMulTangent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueCoord
import Theorems.Thm_GlobalTheory_NilChart_eq_of_nil
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_zR_mem_ker


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
theorem _root_.solution {m : ℕ} (ψ ψ' : JetR R (Fin d) m →ₐ[R] B) (h : spMap ψ ≫ x m = spMap ψ' ≫ x m) : ψ = ψ' := by
  have nil : ∀ φ : JetR R (Fin d) m →ₐ[R] B, IsNilpotent ((RingHom.ker (jetAug R (Fin d) m)).map φ) := fun φ =>
    ⟨m + 1, by rw [← Ideal.map_pow, ker_jetAug_pow, Ideal.map_bot, Ideal.zero_eq_bot]⟩
  refine eq_of_nil hG hv hx₁ hx₂ hx₃ (N := (RingHom.ker (jetAug R (Fin d) m)).map ψ +
    (RingHom.ker (jetAug R (Fin d) m)).map ψ') ((Commute.all _ _).isNilpotent_add (nil ψ) (nil ψ')) ψ ψ'
    (fun j => Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (zR_mem_ker m j)))
    (fun j => Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (zR_mem_ker m j))) h
end GlobalTheory.NilChart
