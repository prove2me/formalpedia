-- Prove2me | solution 1 for GlobalTheory.ThetaBundleSec.exists_fn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:08:37.137799+00:00
-- url     : https://prove2.me/submissions/cc7d1c21-83e9-414f-872f-d15639648ca5

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EqZeroOfForallAlgHomComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowThetaFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfComplexPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SectionsPowEqThetaLevelChar
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mul
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_pow
import Theorems.Thm_GlobalTheory_SectionTheta_quot_eq
import Theorems.Thm_GlobalTheory_ThetaBundleSym_HasFactor_mul
import Theorems.Thm_GlobalTheory_ThetaBundleSym_HasFactor_pow
import Theorems.Thm_GlobalTheory_top_le_preimage_iff_mem
import Theorems.Thm_P2M_GlobalTheory_valAt__rules_bb0546efa0f1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaBundleSec
open ThetaBundleSym
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}
namespace GlobalTheory.ThetaBundleSec
theorem _root_.solution (u : HolUnif A L g) (hL : L.IsLB) (n : ℕ) (s : (lbPow L n).Sec) :
    ∃ θ, Differentiable ℂ θ ∧ u.IsFnPow n s θ ∧ (∀ θ', u.IsFnPow n s θ' → θ' = θ) ∧
      ∀ z w c, u.ex w = u.ex z → (∀ i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u.fr i z = c * u.fr i w) →
        θ w = c ^ n * θ z := by
  have hcov : ∀ z, ∃ j : (lbPow L n).ι, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U j := by
    intro z
    have hmem : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ ⨆ i, L.U i := by
      rw [hL.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
    refine ⟨fun _ => i, ?_⟩
    rw [Cartier.lbPow_U]
    exact (top_le_preimage_iff_mem _ _).2 hi
  have hU : ∀ z (j : (lbPow L n).ι), ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U j →
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j PUnit.unit) := fun z j hj => Cartier.lbPow_U L n j ▸ hj
  choose c hc using hcov
  let θ : (Fin g → ℂ) → ℂ := fun z =>
    valAt' (u.ex z).left ((lbPow L n).U (c z)) (s.f (c z)) / u.fr (c z PUnit.unit) z ^ n
  have hθ : ∀ (j : (lbPow L n).ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U j →
      θ z = valAt' (u.ex z).left ((lbPow L n).U j) (s.f j) / u.fr (j PUnit.unit) z ^ n :=
    fun j z hj => SectionTheta.quot_eq u z (valAt'_rules _ _).2.1 (valAt'_rules _ _).2.2.1 n s _ _ (hc z) hj
  have hfn : u.IsFnPow n s θ := by
    intro j z hj
    rw [hθ j z hj, div_mul_cancel₀ _ (pow_ne_zero n (u.fr_ne _ z (hU z j hj)))]
  refine ⟨θ, fun z => ?_, hfn, fun θ' hθ' => ?_, fun z w k hzw hk => ?_⟩
  · obtain ⟨ho, hd⟩ := u.hol _ (s.f (c z))
    have hn := ho.mem_nhds (hc z)
    have hd2 : DifferentiableOn ℂ (u.fr (c z PUnit.unit))
        {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ (lbPow L n).U (c z)} :=
      (u.fr_hol _).mono fun w hw => hU w _ hw
    have hq := (hd.differentiableAt hn).mul (((hd2.differentiableAt hn).pow n).inv
      (pow_ne_zero n (u.fr_ne _ z (hU z _ (hc z)))))
    refine hq.congr_of_eventuallyEq ?_
    filter_upwards [hn] with w hw
    exact (hθ _ w hw).trans (div_eq_mul_inv _ _)
  · funext z
    have h1 := hfn (c z) z (hc z)
    rw [hθ' (c z) z (hc z)] at h1
    exact mul_right_cancel₀ (pow_ne_zero n (u.fr_ne _ z (hU z _ (hc z)))) h1
  · have h1 := hfn (c z) z (hc z)
    have hc' : ⊤ ≤ (u.ex w).left ⁻¹ᵁ (lbPow L n).U (c z) := by
      rw [hzw]; exact hc z
    have h2 := hfn (c z) w hc'
    rw [hzw, h1, hk _ (hU z _ (hc z)), mul_pow, ← _root_.mul_assoc] at h2
    have h3 := mul_right_cancel₀ (pow_ne_zero n (u.fr_ne _ _ (hU _ _ hc'))) h2
    rw [← h3, _root_.mul_comm]
end GlobalTheory.ThetaBundleSec
