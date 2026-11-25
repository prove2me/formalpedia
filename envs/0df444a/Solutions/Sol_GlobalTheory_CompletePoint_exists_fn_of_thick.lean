-- Prove2me | solution 1 for GlobalTheory.CompletePoint.exists_fn_of_thick
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:28:09.488806+00:00
-- url     : https://prove2.me/submissions/ef1406aa-2a04-4434-8a18-c9b525ed162b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueTorusExtensionPointOfGroupPoint
import Theorems.Thm_GlobalTheory_CompletePoint_iso_appTop
import Theorems.Thm_GlobalTheory_CompletePoint_iso_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompletePoint
variable {R : Type} [CommRing R] (I : Ideal R)
namespace GlobalTheory.CompletePoint
theorem _root_.solution [IsPrecomplete I R] (a : ∀ e, Γ(Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ⊤))
    (h : ∀ e, (thickTrans R I e).appTop.hom (a (e + 1)) = a e) :
    ∃ b : Γ(Spec (CommRingCat.of R), ⊤), ∀ e, (thick R I e).appTop.hom b = a e := by
  choose r hr using fun e => Ideal.Quotient.mk_surjective
    ((Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (e + 1)))).hom.hom (a e))
  have hs : ∀ e, r e - r (e + 1) ∈ I ^ (e + 1) := fun e => by
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (e + 1)))).hom.hom (h e)
    rw [iso_appTop, ← hr, ← hr, Ideal.Quotient.factor_mk] at this
    exact Ideal.Quotient.eq.1 this.symm
  have hle : ∀ {m n : ℕ}, m ≤ n → r m - r n ∈ I ^ (m + 1) := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := add_mem ih (Ideal.pow_le_pow_right (Nat.succ_le_succ hmn) (hs n))
      simpa using this
  obtain ⟨l, hl⟩ := IsPrecomplete.prec (I := I) (M := R) inferInstance (f := r) fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    exact Ideal.pow_le_pow_right m.le_succ (hle hmn)
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom l, fun e => iso_injective _ ?_⟩
  have h1 := hl (e + 1)
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  rw [iso_appTop, ← hr, Iso.inv_hom_id_apply, eq_comm, Ideal.Quotient.eq]
  simpa using add_mem (hs e) h1
end GlobalTheory.CompletePoint
