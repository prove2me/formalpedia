-- Prove2me | solution 1 for GlobalTheory.TangentOrigin.tangent_bijection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:15:47.334551+00:00
-- url     : https://prove2.me/submissions/bce4152a-be02-4239-a420-252b9652271f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Theorems.Thm_GlobalTheory_TangentOrigin_ext_evalPt
import Theorems.Thm_GlobalTheory_TangentOrigin_exists_evalPt_eq
import Theorems.Thm_GlobalTheory_TangentOrigin_eq_spMap_of_evalPt
import Theorems.Thm_GlobalTheory_TangentOrigin_top_le_preimage_iff
import Theorems.Thm_GlobalTheory_TangentOrigin_ex_zero_left
import Theorems.Thm_GlobalTheory_TangentOrigin_jet_fst
import Theorems.Thm_GlobalTheory_TangentOrigin_jet_snd
import Theorems.Thm_GlobalTheory_TangentOrigin_jet_const
import Theorems.Thm_GlobalTheory_TangentOrigin_tangent_mem_iff
import Theorems.Thm_GlobalTheory_TangentOrigin_tangent_fst
import Theorems.Thm_GlobalTheory_TangentOrigin_tangent_const
import Theorems.Thm_GlobalTheory_TangentOrigin_isDiff_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.TangentOrigin
namespace GlobalTheory.TangentOrigin
theorem _root_.solution :
    (∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), (∃ (U : A.left.Opens) (t : Fin g → Γ(A.left, U)), IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U ∧ (∀ D : Γ(A.left, U) →+ ℂ, (∀ a, D (constFn A.hom U a) = 0) → (∀ f f', D (f * f') = valAt' (u.ex 0).left U f * D f' + valAt' (u.ex 0).left U f' * D f) → (∀ i, D (t i) = 0) → D = 0) ∧ HasFDerivAt (fun w i => valAt' (u.ex w).left U (t i)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v)) := by
  rintro A _ L g u ⟨U, t, hU, h0, huniq, ht⟩
  have hjet : ∀ w i, (jet u w U h0 (t i)).snd = w i := by
    intro w i
    have := (hasFDerivAt_pi'.1 ht i).fderiv
    rw [jet_snd, this]
    rfl
  refine ⟨fun v hv => ?_, fun w => ?_⟩
  · have h := (tangent_mem_iff (u := u) hv U).2 h0
    refine ⟨fun i => (evalPt (R := DualNumber ℂ) v.left U h (t i)).snd, ?_, fun w hw => ?_⟩
    · set w : Fin g → ℂ := fun i => (evalPt (R := DualNumber ℂ) v.left U h (t i)).snd with hw
      refine (isDiff_iff hv hU h h0 w).2 ?_
      let D : Γ(A.left, U) →+ ℂ :=
        { toFun := fun f => (evalPt (R := DualNumber ℂ) v.left U h f).snd - (jet u w U h0 f).snd
          map_zero' := by simp
          map_add' := fun f f' => by
            simp only [map_add, TrivSqZeroExt.snd_add]
            ring }
      have hD : ∀ f, D f =
          (evalPt (R := DualNumber ℂ) v.left U h f).snd - (jet u w U h0 f).snd := fun _ => rfl
      have hz : D = 0 := by
        apply huniq
        · intro a
          rw [hD, tangent_const, jet_const, sub_self]
        · intro f f'
          rw [hD, hD, hD, map_mul, map_mul, DualNumber.snd_mul, DualNumber.snd_mul,
            tangent_fst hv h h0, tangent_fst hv h h0, jet_fst, jet_fst, valAt'_eq_evalPt _ _ h0,
            valAt'_eq_evalPt _ _ h0]
          ring
        · intro i
          rw [hD, hjet, sub_self]
      refine RingHom.ext fun f => TrivSqZeroExt.ext (tangent_fst hv h h0 f) ?_
      have := hD f
      rw [hz] at this
      exact sub_eq_zero.1 this.symm
    · replace hw := (isDiff_iff hv hU h h0 w).1 hw
      funext i
      rw [hw, hjet]
  · obtain ⟨x, hx, hxe⟩ := exists_evalPt_eq hU (jet u w U h0)
    have hover : x ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := by
      refine eq_spMap_of_evalPt _ _ fun a => ?_
      rw [← evalPt_constFn A.hom x U hx, hxe, jet_const]
    let v : epsR ℂ ⟶ A := Over.homMk x hover
    have hv : IsTangent v := by
      refine Eq.trans ?_ (ex_zero_left u)
      refine ext_evalPt hU ((top_le_preimage_iff x U).1 hx) h0 (RingHom.ext fun f => ?_)
      refine (evalPt_spMap_comp fstC x U hx _ f).trans ?_
      rw [hxe]
      rfl
    refine ⟨v, ⟨hv, (isDiff_iff hv hU hx h0 w).2 hxe⟩, ?_⟩
    rintro v' ⟨hv', hd'⟩
    have h' := (tangent_mem_iff (u := u) hv' U).2 h0
    rw [isDiff_iff hv' hU h' h0] at hd'
    exact Over.OverMorphism.ext (ext_evalPt hU h' hx (hd'.trans hxe.symm))
end GlobalTheory.TangentOrigin
