-- Prove2me | solution 1 for GlobalTheory.AnArc.Hw_actV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:32:54.952036+00:00
-- url     : https://prove2.me/submissions/ed7c1006-c96f-4b82-80fe-c72a51166aae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Theorems.Thm_GlobalTheory_AnArc_im_Hw_Pw
import Theorems.Thm_GlobalTheory_AnArc_Pw_lattice
import Theorems.Thm_GlobalTheory_AnArc_EF_smul
import Theorems.Thm_GlobalTheory_AnArc_Pw_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Matrix
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution {w : ℂ} (hw : (A.BwMat w).PosDef) (a : O) (v v' : A.V) :
    A.Hw w (A.actV a v) v' = A.Hw w v (A.actV (star a) v') := by
  have hsp := (A.Pw_lattice hw).2.2
  have him : ∀ v v' : A.V, (A.Hw w (A.actV a v) v').im = (A.Hw w v (A.actV (star a) v')).im := by
    intro v v'
    have hv : v ∈ Submodule.span ℝ (Set.range (A.Pw w)) := hsp ▸ Submodule.mem_top
    have hv' : v' ∈ Submodule.span ℝ (Set.range (A.Pw w)) := hsp ▸ Submodule.mem_top
    induction hv, hv' using Submodule.span_induction₂ with
    | mem_mem x y hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      rw [← Pw_smul, ← Pw_smul, A.im_Hw_Pw hw, A.im_Hw_Pw hw, EF_smul]
    | zero_left => simp
    | zero_right => simp
    | add_left x y z _ _ _ h h' => simp only [map_add, LinearMap.add_apply, Complex.add_im, h, h']
    | add_right x y z _ _ _ h h' => simp only [map_add, Complex.add_im, h, h']
    | smul_left r x y _ _ h =>
      rw [← algebraMap_smul ℂ r x]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.coe_algebraMap, Complex.im_ofReal_mul, h]
    | smul_right r x y _ _ h =>
      rw [← algebraMap_smul ℂ r y]
      simp only [map_smul, LinearMap.map_smulₛₗ, smul_eq_mul, Complex.coe_algebraMap, Complex.conj_ofReal,
        Complex.im_ofReal_mul, h]
  refine Complex.ext ?_ (him v v')
  have := him (Complex.I • v) v'
  simpa using this
end GlobalTheory.AnArc
