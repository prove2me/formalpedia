-- Prove2me | solution 1 for GlobalTheory.HomChain.dpolyOf_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:49:45.314928+00:00
-- url     : https://prove2.me/submissions/336a0147-bf11-4e7e-a061-91c6c7980afe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AxisPderivComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_LawRightUnit
import Theorems.Thm_GlobalTheory_HomChain_dof_hom
import Theorems.Thm_GlobalTheory_ChartTrans_ev_C_mul
import Theorems.Thm_GlobalTheory_ChartTrans_ev_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_single_point_zero_constant


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.ChartTrans
open GlobalTheory GlobalTheory.HomChain
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.HomChain
theorem _root_.solution :
    ∀ (k : Type) [CommRing k] (d : ℕ) (G G' : FGLaw k d) (α : Pt k 1 d),
      (∀ i, constantCoeff (α i) = 0) →
      comp1 α (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
        G'.add (comp1 α (pt k (n := 2) d 0)) (comp1 α (pt k (n := 2) d 1)) →
      ∀ (Λ : Type) [Fintype Λ] (u : Λ → Fin d → k) (Q : MvPolynomial Λ k) (g : PS k 1 d),
        DpolyOf G.F u Q (ev (n := 1) ![α] g) =
          ev (n := 1) ![α] (DpolyOf G'.F (fun l => (dLin α).mulVec (u l)) Q g) := by
  intro k _ d G G' α hα hom ι _ u P g
  have hφ : GP α := hα
  have hit : ∀ (v : Fin d → k) (n : ℕ) (g : PS k 1 d),
      (Dof G.F v)^[n] (ev (n := 1) ![α] g) =
        ev (n := 1) ![α] ((Dof G'.F ((dLin α).mulVec v))^[n] g) := by
    intro v n
    induction n with
    | zero => intro g; rfl
    | succ n ih =>
      intro g
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, dof_hom G G' α hα hom, ih]
  have hmon : ∀ m : ι →₀ ℕ, DmonOf G.F u m (ev (n := 1) ![α] g) =
      ev (n := 1) ![α] (DmonOf G'.F (fun l => (dLin α).mulVec (u l)) m g) := by
    intro m
    unfold DmonOf
    induction (Finset.univ : Finset ι).toList with
    | nil => rfl
    | cons a L ih => rw [List.foldr_cons, List.foldr_cons, ih, hit]
  unfold DpolyOf
  rw [ev_sum _ (single_point_zero_constant hφ)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ev_C_mul _ (single_point_zero_constant hφ), hmon]
end GlobalTheory.HomChain
