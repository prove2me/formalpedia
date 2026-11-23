-- Prove2me | solution 1 for GlobalTheory.ZH.CrdCalc.crd_calculus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:30:43.085354+00:00
-- url     : https://prove2.me/submissions/5e38f284-310d-4f41-a2e6-4d3a6416774b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_crd_exists
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_crd_unique
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_crd_isUnit_iff
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_crd_map
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_crd_smul
import Theorems.Thm_GlobalTheory_ZH_CrdCalc_crd_ratio

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.CrdCalc
variable {R : Type} [CommRing R] {X : Scheme.{0}}
variable {H : LB X} {J : Type} {s : J → H.Sec}
namespace GlobalTheory.ZH.CrdCalc
theorem _root_.solution : (∀ (X : Scheme.{0}) (H : LB X) (J : Type) (s : J → H.Sec), H.IsLB → (∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Sp R ⟶ X), (∃ v, Crd H s x v) ∧ (∀ v v', Crd H s x v → Crd H s x v' → ∃ c : Rˣ, ∀ j, v' j = (c : R) * v j) ∧ ∀ v j, Crd H s x v → (IsUnit (v j) ↔ ⊤ ≤ x ⁻¹ᵁ Out.nonzeroLocus (s j))) ∧ (∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (x : Sp R ⟶ X) (v : J → R), Crd H s x v → Crd H s (spMap φ ≫ x) (fun j => φ (v j))) ∧ (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : J → R) (c : Rˣ), Crd H s x v → Crd H s x (fun j => (c : R) * v j)) ∧ ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : J → R) (i j : J) (W : X.Opens) (r : Γ(X, W)), Crd H s x v → IsRatio (s j) (s i) W r → ⊤ ≤ x ⁻¹ᵁ W → v j = valR x W r * v i) :=
  fun _ _ _ s hH =>
    ⟨fun _ _ _ x => ⟨crd_exists hH s x, fun _ _ => crd_unique, fun _ j => crd_isUnit_iff j⟩,
      fun _ _ _ _ φ _ _ => crd_map φ, fun _ _ _ _ c => crd_smul c, fun _ _ _ _ _ _ _ _ => crd_ratio⟩
end GlobalTheory.ZH.CrdCalc
