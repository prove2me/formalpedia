-- Prove2me | solution 1 for GlobalTheory.SelfCube.form_eq_zero_of_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:55:55.047009+00:00
-- url     : https://prove2.me/submissions/836dd71a-2cf2-4426-a3b6-3994a92a9b8c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube
import Theorems.Thm_GlobalTheory_SelfCube_quad_nonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
namespace GlobalTheory.SelfCube
private theorem exists_bound_of_continuous_lattice_periodic {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (h : (Fin g → ℂ) → ℝ) (hc : Continuous h)
    (hp : ∀ z, ∀ l ∈ Λ, h (z + l) = h z) : ∃ M, ∀ z, h z ≤ M := by
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Module.Free.ChooseBasisIndex ℤ Λ) ℝ (Fin g → ℂ),
      Submodule.span ℤ (Set.range b) = Λ :=
    ⟨_, (Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis_span ℝ⟩
  have hK : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
    (ZSpan.fundamentalDomain_isBounded b).isCompact_closure
  obtain ⟨M, hM⟩ := (hK.image hc).bddAbove
  refine ⟨M, fun z => ?_⟩
  have hfl : (ZSpan.floor b z : Fin g → ℂ) ∈ Λ := by
    exact Eq.mp (congrArg (fun S : Submodule ℤ (Fin g → ℂ) => (ZSpan.floor b z : Fin g → ℂ) ∈ S) hb)
      (ZSpan.floor b z).2
  have hz : z = ZSpan.fract b z + (ZSpan.floor b z : Fin g → ℂ) := by
    rw [ZSpan.fract_apply]; abel
  rw [hz, hp _ _ hfl]
  exact hM ⟨_, subset_closure (ZSpan.fract_mem_fundamentalDomain b z), rfl⟩
section Herm
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
end Herm
open GlobalTheory.CubeValues
end GlobalTheory.SelfCube
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.SelfCube
namespace GlobalTheory.SelfCube
theorem _root_.solution {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ψ : (Fin g → ℂ) → ℂ) (hψ : Differentiable ℂ ψ) (h0 : ∀ z, ψ z ≠ 0)
    (D : (Fin g → ℂ) → (Fin g → ℂ) → ℂ) (hc : Continuous fun z => D z z)
    (hadd : ∀ z z' w, D (z + z') w = D z w + D z' w)
    (hsm : ∀ (t : ℂ) z w, D (t • z) w = t * D z w)
    (hst : ∀ z w, D w z = starRingEnd ℂ (D z w))
    (ρ : Λ → ℂ) (hρ : ∀ l, ‖ρ l‖ = 1)
    (hper : ∀ z (l : Λ), ψ (z + l) = ρ l * cexp (π * D z l + π / 2 * D l l) * ψ z) :
    (∀ z w, D z w = 0) ∧ ∀ l, ρ l = 1 := by
  have hadd2 : ∀ z w w', D z (w + w') = D z w + D z w' := fun z w w' => by
    rw [hst, hadd, map_add, ← hst, ← hst]
  have hsm2 : ∀ (t : ℂ) z w, D z (t • w) = starRingEnd ℂ t * D z w := fun t z w => by
    rw [hst, hsm, map_mul, ← hst]
  have hdiag_im : ∀ z, (D z z).im = 0 := fun z => by
    have := congrArg Complex.im (hst z z)
    rw [Complex.conj_im] at this
    linarith
  set q : (Fin g → ℂ) → ℝ := fun z => π / 2 * (D z z).re with hqdef
  have hqc : Continuous q := continuous_const.mul (Complex.continuous_re.comp hc)
  have hqs : ∀ (t : ℂ) w, q (t • w) = ‖t‖ ^ 2 * q w := fun t w => by
    simp only [hqdef, hsm, hsm2]
    rw [← _root_.mul_assoc, Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]
    ring
  have hexpand : ∀ z l, D (z + l) (z + l) = D z z + D z l + D l z + D l l := fun z l => by
    rw [hadd, hadd2, hadd2]; ring
  have hreal : ∀ z l, (D l z).re = (D z l).re := fun z l => by rw [hst, Complex.conj_re]
  have hnorm : ∀ z (l : Λ),
      ‖ψ (z + l)‖ = Real.exp (π * (D z l).re + π / 2 * (D l l).re) * ‖ψ z‖ := fun z l => by
    rw [hper, norm_mul, norm_mul, hρ, _root_.one_mul, Complex.norm_exp]
    congr 2
    simp [Complex.add_re, Complex.mul_re, hdiag_im]
  have hper_q : ∀ z (l : Λ),
      ‖ψ (z + l)‖ * Real.exp (-q (z + l)) = ‖ψ z‖ * Real.exp (-q z) := fun z l => by
    rw [hnorm, mul_comm (Real.exp _) _, _root_.mul_assoc, ← Real.exp_add]
    congr 2
    simp only [hqdef, hexpand, Complex.add_re, hreal z l]
    ring
  have hq1 : ∀ w, 0 ≤ q w := fun w =>
    quad_nonneg Λ ψ hψ (h0 0) q hqc hqs (fun z l hl => hper_q z ⟨l, hl⟩) w
  have hq2 : ∀ w, 0 ≤ -q w := fun w =>
    quad_nonneg Λ (fun z => (ψ z)⁻¹) (hψ.inv h0) (inv_ne_zero (h0 0)) (fun z => -q z) hqc.neg
      (fun t w => by simp only [hqs]; ring) (fun z l hl => by
        have := hper_q z ⟨l, hl⟩
        simp only [norm_inv, neg_neg]
        have e1 : Real.exp (q (z + l)) = (Real.exp (-q (z + l)))⁻¹ := by rw [Real.exp_neg, inv_inv]
        have e2 : Real.exp (q z) = (Real.exp (-q z))⁻¹ := by rw [Real.exp_neg, inv_inv]
        rw [e1, e2, ← mul_inv, ← mul_inv]
        exact congrArg _ this) w
  have hdiag : ∀ z, D z z = 0 := fun z => by
    have hre : (D z z).re = 0 := by
      have h3 : q z = 0 := le_antisymm (by linarith [hq2 z]) (hq1 z)
      simp only [hqdef] at h3
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd h (by positivity)
      · exact h
    exact Complex.ext_iff.2 ⟨by simpa using hre, by simpa using hdiag_im z⟩
  have hD0 : ∀ z w, D z w = 0 := fun z w => by
    have e1 := hexpand z w
    rw [hdiag, hdiag, hdiag] at e1
    have e2 := hexpand (I • z) w
    rw [hdiag, hdiag, hdiag, hsm, hsm2, Complex.conj_I] at e2
    have hb : D w z = -D z w := by linear_combination (-1 : ℂ) * e1
    rw [hb] at e2
    have h2 : (2 * I) * D z w = 0 := by linear_combination -e2
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h (mul_ne_zero two_ne_zero I_ne_zero)
    · exact h
  have hper' : ∀ z (l : Λ), ψ (z + l) = ρ l * ψ z := fun z l => by
    rw [hper, hD0, hD0]; simp
  obtain ⟨M, hM⟩ := exists_bound_of_continuous_lattice_periodic Λ (fun z => ‖ψ z‖) hψ.continuous.norm (fun z l hl =>
    (congrArg norm (hper' z ⟨l, hl⟩)).trans (by rw [norm_mul, hρ, _root_.one_mul]))
  have hb : Bornology.IsBounded (Set.range ψ) := by
    rw [isBounded_iff_forall_norm_le]
    exact ⟨M, by rintro _ ⟨z, rfl⟩; exact hM z⟩
  have hconst : ∀ z, ψ z = ψ 0 := fun z => hψ.apply_eq_apply_of_bounded hb z 0
  refine ⟨hD0, fun l => ?_⟩
  have h4 := hper' 0 l
  rw [hconst (0 + (l : Fin g → ℂ))] at h4
  exact mul_right_cancel₀ (h0 0) (h4.symm.trans (_root_.one_mul _).symm)
end GlobalTheory.SelfCube
