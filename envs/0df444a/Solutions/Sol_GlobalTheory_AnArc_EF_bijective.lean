-- Prove2me | solution 1 for GlobalTheory.AnArc.EF_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:42:25.259348+00:00
-- url     : https://prove2.me/submissions/7f228900-3a5a-4d3b-8ad6-94dc991dd93a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Theorems.Thm_GlobalTheory_AnArc_EF_apply
import Theorems.Thm_GlobalTheory_AnArc_La_eq_add_parts


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
theorem _root_.solution : Function.Bijective A.EF := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro v hv
    have h : ∀ v', A.EF v v' = 0 := fun v' => by rw [hv]; rfl
    refine La.ext ?_ (AddMonoidHom.ext fun x => ?_) ?_
    · refine (Module.Free.chooseBasis ℤ A.X).ext_elem fun i => ?_
      have := h (La.mk 0 ((Module.Free.chooseBasis ℤ A.X).coord i).toAddMonoidHom 0)
      simpa [EF_apply] using this
    · have := h (La.mk x 0 0)
      simpa [EF_apply] using this
    · refine A.Ef_bij.1 (LinearMap.ext fun m => ?_)
      have := h (La.mk 0 0 m)
      simpa [EF_apply] using this
  · intro φ
    let φ₁ : A.X →+ ℤ := AddMonoidHom.mk' (fun y => φ (La.mk y 0 0)) fun y y' => by
      rw [← map_add]; congr 1; ext <;> simp
    let φ₂ : Module.Dual ℤ (Module.Dual ℤ A.X) :=
      (AddMonoidHom.mk' (fun n : Module.Dual ℤ A.X => φ (La.mk 0 n.toAddMonoidHom 0)) fun n n' => by
        rw [← map_add]; congr 1; ext <;> simp).toIntLinearMap
    let φ₃ : Module.Dual ℤ A.abelian₂ :=
      (AddMonoidHom.mk' (fun l : A.abelian₂ => φ (La.mk 0 0 l)) fun n n' => by
        rw [← map_add]; congr 1; ext <;> simp).toIntLinearMap
    obtain ⟨y, hy⟩ := (Module.evalEquiv ℤ A.X).surjective φ₂
    obtain ⟨l, hl⟩ := A.Ef_bij.2 φ₃
    refine ⟨La.mk y (-φ₁) l, LinearMap.ext fun v => ?_⟩
    have h2 : v.n y = φ (La.mk 0 v.n 0) := congrArg (fun f => f v.n.toIntLinearMap) hy
    have h3 : A.Ef l v.l = φ (La.mk 0 0 v.l) := congrArg (fun f => f v.l) hl
    conv_rhs => rw [La.eq_add_parts v, map_add, map_add]
    rw [EF_apply, La.mk_y, La.mk_n, La.mk_l, h2, h3]
    simp [φ₁]; ring
end GlobalTheory.AnArc
