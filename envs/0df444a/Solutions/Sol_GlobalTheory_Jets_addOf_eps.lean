-- Prove2me | solution 1 for GlobalTheory.Jets.addOf_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:47:19.01609+00:00
-- url     : https://prove2.me/submissions/33b89048-7e4c-4130-8c29-3eec4cd4d617

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ContinuousPderivDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HasSubstAddSqZero
import Theorems.Thm_GlobalTheory_Jets_subst_add_sqZero
import Theorems.Thm_P2M_GlobalTheory_Jets_map_pderiv__1dd9b2916977
import Theorems.Thm_GlobalTheory_Jets_hasSubst_pt_zero
import Theorems.Thm_GlobalTheory_Jets_law_right_unit
import Theorems.Thm_GlobalTheory_Jets_map_ev_pt_zero
import Theorems.Thm_GlobalTheory_Jets_C_eps_mul_self

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.Jets
namespace GlobalTheory.Jets
theorem _root_.solution {R : Type} [CommRing R] {d : ℕ} (G : FGLaw R d) (v : Fin d → R) (j : Fin d) :
    addOf (n := 1) (G.mapF (algebraMap R (DualNumber R))) (pt (DualNumber R) d 0)
        (fun i => C (TrivSqZeroExt.inr (v i) : DualNumber R)) j =
      X ((0 : Fin 1), j) + C (DualNumber.eps : DualNumber R) *
        MvPowerSeries.map (algebraMap R (DualNumber R))
          (∑ i : Fin d, C (v i) *
            ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) (G.F j))) := by
  have h := subst_add_sqZero
    (fun p : Fin 2 × Fin d => (![pt (DualNumber R) d 0, 0] : Fin 2 → Pt (DualNumber R) 1 d) p.1 p.2)
    (fun p : Fin 2 × Fin d => (![0, fun i => C (algebraMap R (DualNumber R) (v i))] :
      Fin 2 → Pt (DualNumber R) 1 d) p.1 p.2)
    (C DualNumber.eps) (C_eps_mul_self R _)
    (fun p => by rw [hasSubst_pt_zero]; exact IsNilpotent.zero)
    (MvPowerSeries.map (algebraMap R (DualNumber R)) (G.F j))
  have h1 := map_ev_pt_zero (algebraMap R (DualNumber R)) (G.F j)
  rw [law_right_unit, map_X] at h1
  rw [h1, map_sum]
  simp only [map_mul, map_C, map_ev_pt_zero, map_pderiv']
  rw [Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, zero_add] at h
  refine Eq.trans ?_ h
  unfold addOf ev FGLaw.mapF
  congr 1
  funext p
  obtain ⟨l, i⟩ := p
  fin_cases l
  · simp
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply,
      zero_add]
    rw [← map_mul]
    congr 1
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
end GlobalTheory.Jets
