-- Prove2me | solution 1 for GlobalTheory.TorusTransfer.eq_zero_of_fderiv_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:46:29.742244+00:00
-- url     : https://prove2.me/submissions/d2c3f18e-d2c8-4025-b13f-d822139f73b3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTestFunctionsSubsetOfMemNhds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEtaleCoordsVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LevelThreeSeparatesPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FderivEqZeroOfAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_PolarisedTorusAlgebraicOfParts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqZeroOfFderivEqZero
import Theorems.Thm_GlobalTheory_TorusTransfer_fderiv_eq_zero_at
import Theorems.Thm_GlobalTheory_TangentOrigin_ex_zero
import Theorems.Thm_GlobalTheory_existsUnique_point_of_ringHom
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_GlobalTheory_top_le_preimage_iff_mem
import Theorems.Thm_P2M_GlobalTheory_valAt__constFn_1b31686fad50
import Theorems.Thm_P2M_GlobalTheory_valAt__eq_valAtHom_eb5802171cfc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real CategoryTheory.Obj
open GlobalTheory GlobalTheory.TorusTransfer
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.TorusTransfer
theorem _root_.solution (w : Fin g → ℂ)
    (hw : ∀ (U : A.left.Opens) (f : Γ(A.left, U)), ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w = 0) : w = 0 := by
  obtain ⟨_, ⟨U, hU, rfl⟩, h0, -⟩ := A.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((u.ex 0).left (default : PrimeSpectrum ℂ))) isOpen_univ
  have h0' : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := (top_le_preimage_iff_mem _ _).2 h0
  have hc : Continuous fun t : ℂ => t • w := by fun_prop
  have hO : IsOpen {t : ℂ | ⊤ ≤ (u.ex (t • w)).left ⁻¹ᵁ U} := (u.hol U 0).1.preimage hc
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO 0 (by simpa using h0')
  have hmem : ∀ t ∈ Metric.ball (0 : ℂ) r, t • w ∈ u.Λ := by
    intro t ht
    rw [← u.ker, ← TangentOrigin.ex_zero u]
    have hval : ∀ f : Γ(A.left, U), valAt' (u.ex (t • w)).left U f = valAt' (u.ex 0).left U f := by
      intro f
      have hd : ∀ s ∈ Metric.ball (0 : ℂ) r,
          HasDerivAt (fun s : ℂ => valAt' (u.ex (s • w)).left U f) 0 s := by
        intro s hs
        have h1 : DifferentiableAt ℂ (fun z => valAt' (u.ex z).left U f) (s • w) :=
          (u.hol U f).2.differentiableAt ((u.hol U f).1.mem_nhds (hball hs))
        have h2 : HasDerivAt (fun s : ℂ => s • w) w s := by
          simpa using (hasDerivAt_id s).smul_const w
        have h3 := h1.hasFDerivAt.comp_hasDerivAt s h2
        rw [fderiv_eq_zero_at u w hw _ U f (hball hs)] at h3
        exact h3
      have := Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) r).isPreconnected
        (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt) (fun s hs => (hd s hs).deriv)
        ht (Metric.mem_ball_self hr)
      simpa using this
    exact (existsUnique_point_of_ringHom A U hU (valAtHom _ U h0')
      (fun a => by
        rw [← valAt'_eq_valAtHom]
        exact valAt'_constFn _ _ (Over.w (u.ex 0)) U a h0')).unique
      ⟨hball ht, fun f => by rw [hval, valAt'_eq_valAtHom]⟩
      ⟨h0', fun f => valAt'_eq_valAtHom _ h0' f⟩
  have := u.discrete
  obtain ⟨V, hV, hV'⟩ := (isOpen_induced_iff (f := ((↑) : u.Λ → Fin g → ℂ))).1 (isOpen_discrete ({0} : Set u.Λ))
  have hV0 : (0 : Fin g → ℂ) ∈ V := by
    have : (0 : u.Λ) ∈ ((↑) : u.Λ → Fin g → ℂ) ⁻¹' V := by rw [hV']; rfl
    exact this
  have hev : ∀ᶠ t : ℂ in 𝓝[≠] 0, t • w ∈ V ∧ t ∈ Metric.ball (0 : ℂ) r :=
    nhdsWithin_le_nhds (Filter.inter_mem ((hV.preimage hc).mem_nhds (by simpa using hV0)) (Metric.ball_mem_nhds _ hr))
  obtain ⟨t, ⟨h1, h2⟩, h3⟩ := (hev.and self_mem_nhdsWithin).exists
  have h4 : (⟨t • w, hmem t h2⟩ : u.Λ) ∈ ((↑) : u.Λ → Fin g → ℂ) ⁻¹' V := h1
  rw [hV'] at h4
  exact (smul_eq_zero.1 (congrArg Subtype.val h4)).resolve_left h3
end GlobalTheory.TorusTransfer
