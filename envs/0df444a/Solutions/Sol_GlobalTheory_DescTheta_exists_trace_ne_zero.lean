-- Prove2me | solution 1 for GlobalTheory.DescTheta.exists_trace_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:33:41.031031+00:00
-- url     : https://prove2.me/submissions/783197af-4acb-4173-886a-9b0e7e9eab3a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSumSmulSeparatingInertia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSecOnNonvanishingOfTameQuotient
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_exists_sum_smul_separating_inertia
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.DescTheta
open GlobalTheory.LB
namespace GlobalTheory.DescTheta
theorem _root_.solution {Γ B A K : Type} [Group Γ] [Fintype Γ] [CommRing B] [CommRing A]
    [Field K] [MulSemiringAction Γ B] [MulSemiringAction Γ A] (f : B →+* A)
    (hf : ∀ (g : Γ) b, f (g • b) = g • f b) (ev : A →+* K)
    (hc : (Nat.card ((RingHom.ker (ev.comp f)).inertia Γ) : K) ≠ 0) (x : A)
    (hI : ∀ g ∈ (RingHom.ker (ev.comp f)).inertia Γ, ev (g • x) = ev x) (hx : ev x ≠ 0) :
    ∃ c : B, ev (∑ g : Γ, g • (f c * x)) ≠ 0 := by
  classical
  obtain ⟨n, c, d, s, hs, h⟩ := exists_sum_smul_separating_inertia Γ B _
    (RingHom.ker_isPrime (ev.comp f))
  by_contra! H
  have h1 : ∑ j, ev (f (d j)) * ev (∑ g : Γ, g • (f (c j) * x)) = 0 := by
    simp only [H, mul_zero, Finset.sum_const_zero]
  have h2 : ∑ j, ev (f (d j)) * ev (∑ g : Γ, g • (f (c j) * x)) =
      ∑ g : Γ, ev (f (∑ j, d j * g • c j)) * ev (g • x) := by
    simp only [map_sum, Finset.mul_sum, Finset.sum_mul, smul_mul', map_mul, hf, _root_.mul_assoc]
    rw [Finset.sum_comm]
  have h3 : ∀ g : Γ, ev (f (∑ j, d j * g • c j)) * ev (g • x) =
      if g ∈ (RingHom.ker (ev.comp f)).inertia Γ then ev (f s) * ev x else 0 := by
    intro g
    split_ifs with hg
    · have := (h g).1 hg
      rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
      rw [hI g hg]
      exact congrArg (· * ev x) this
    · have : ev (f (∑ j, d j * g • c j)) = 0 := (h g).2 hg
      rw [this, zero_mul]
  rw [h2] at h1
  simp only [h3] at h1
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← Fintype.card_subtype,
    ← Nat.card_eq_fintype_card] at h1
  exact mul_ne_zero hc (mul_ne_zero hs hx) h1
end GlobalTheory.DescTheta
