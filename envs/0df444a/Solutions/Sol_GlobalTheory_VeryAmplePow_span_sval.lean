-- Prove2me | solution 1 for GlobalTheory.VeryAmplePow.span_sval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:22:13.912531+00:00
-- url     : https://prove2.me/submissions/77bd5890-c63d-458d-a663-ff4fe2b49dc0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem
import Theorems.Thm_GlobalTheory_VeryAmplePow_gs_appTop
import Theorems.Thm_GlobalTheory_VeryAmplePow_gs_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VeryAmplePow
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
namespace GlobalTheory.VeryAmplePow
theorem _root_.solution {a : ℤ} {T : Over S} {I : Type} [Fintype I] (b : I → LB.Sec (LPow A L a T))
    (hb : Submodule.span Γ(T.left, ⊤) (Set.range fun i => (SecM.ofSec A (b i) : SecM A L a T)) = ⊤)
    (s : LB.Sec (LPow A L a T)) : ∃ c : I → Γ(T.left, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J,
      Good L z J → sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s r z J =
        ∑ i, gs (r ≫ (fst T A).left) z ⊤ (c i) *
          sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (b i) r z J := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
    (show SecM.ofSec A s ∈ _ from hb ▸ Submodule.mem_top)
  have hc' : ∀ j, s.f j = ∑ i, liftHom A _ (c i) * (b i).f j := fun j => by
    have := congrArg (fun x : SecM A L a T => x.1 j) hc
    simp only [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply] at this
    exact this.symm
  refine ⟨c, fun Z r z J hJ => ?_⟩
  have hm := hJ.mem (fun _ : Fin 1 => (snd T A).left) r
  refine (congrArg (gs r z _) (hc' _)).trans ((gs_sum r z _ hm _).trans (Finset.sum_congr rfl fun i _ => ?_))
  exact (gs_mul r z _ hm _ _).trans (congrArg (· * _) ((gs_res r z le_top hm _).trans (gs_appTop r _ z _)))
end GlobalTheory.VeryAmplePow
