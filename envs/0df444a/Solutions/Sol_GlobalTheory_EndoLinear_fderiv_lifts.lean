-- Prove2me | solution 1 for GlobalTheory.EndoLinear.fderiv_lifts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:48.277392+00:00
-- url     : https://prove2.me/submissions/524bd1bc-f181-40ae-a8c6-50d77b8c2abb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearLift

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
open GlobalTheory GlobalTheory.EndoLinear
namespace GlobalTheory.EndoLinear
theorem _root_.solution {E E' M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
    [NormedSpace ℂ E'] [Group M] (ex : E' → M) (hex : ∀ z w, ex (z + w) = ex z * ex w)
    (Λ : Submodule ℤ E') (hker : ∀ z, ex z = 1 ↔ z ∈ Λ) (hd : DiscreteTopology Λ)
    (a : E → M) (ha : ∀ z w, a (z + w) = a z * a w) (G : E → E') (h0 : G 0 = 0)
    (hG : DifferentiableAt ℂ G 0) (hev : ∀ᶠ w in 𝓝 0, ex (G w) = a w) (z : E) :
    ex (fderiv ℂ G 0 z) = a z := by
  have hc : ContinuousAt G 0 := hG.continuousAt
  have h2 : Tendsto (fun w : E => w + w) (𝓝 0) (𝓝 0) := by
    have : Continuous (fun w : E => w + w) := by fun_prop
    simpa using this.tendsto 0
  have hG0 : Tendsto G (𝓝 0) (𝓝 0) := by simpa [h0] using hc.tendsto
  have hD : Tendsto (fun w : E => G (w + w) - (G w + G w)) (𝓝 0) (𝓝 0) := by
    simpa using (hG0.comp h2).sub (hG0.add hG0)
  have hmem : ∀ᶠ w in 𝓝 (0 : E), G (w + w) - (G w + G w) ∈ Λ := by
    filter_upwards [hev, h2.eventually hev] with w hw hw2
    rw [← hker]
    have h := hex (G (w + w) - (G w + G w)) (G w + G w)
    rw [sub_add_cancel, hw2, hex (G w), hw, ha] at h
    exact (mul_eq_right.mp h.symm)
  have hiso : ∀ᶠ y in 𝓝 (0 : E'), y ∈ Λ → y = 0 := by
    have ho : IsOpen ({0} : Set Λ) := isOpen_discrete _
    obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.mp ho
    have h0t : (0 : E') ∈ t := by
      have : (0 : Λ) ∈ Subtype.val ⁻¹' t := by rw [hts]; rfl
      exact this
    filter_upwards [ht.mem_nhds h0t] with y hy hyΛ
    have : (⟨y, hyΛ⟩ : Λ) ∈ Subtype.val ⁻¹' t := hy
    rw [hts] at this
    exact congrArg Subtype.val this
  have hdbl : ∀ᶠ w in 𝓝 (0 : E), G (w + w) = G w + G w := by
    filter_upwards [hmem, hD.eventually hiso] with w h1 h2
    exact sub_eq_zero.mp (h2 h1)
  set c : ℕ → ℂ := fun n => (2 : ℂ) ^ n with hcdef
  have hcn : Tendsto (fun n => ‖c n‖) atTop atTop := by
    simp only [hcdef, norm_pow, Complex.norm_ofNat]
    exact tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  have hz : Tendsto (fun n => (c n)⁻¹ • z) atTop (𝓝 0) := by
    have : Tendsto (fun n => (c n)⁻¹) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [norm_inv]
      exact hcn.inv_tendsto_atTop
    simpa using this.smul_const z
  have hhalf : ∀ n, (c n)⁻¹ • z = (c (n + 1))⁻¹ • z + (c (n + 1))⁻¹ • z := by
    intro n
    rw [← add_smul]
    congr 1
    simp only [hcdef, pow_succ]
    field_simp
    norm_num
  have hlim : Tendsto (fun n => c n • G ((c n)⁻¹ • z)) atTop (𝓝 (fderiv ℂ G 0 z)) := by
    have := hG.hasFDerivAt.lim z hcn
    simpa [h0] using this
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hz.eventually (hdbl.and hev))
  have hconst : ∀ n, N ≤ n → c n • G ((c n)⁻¹ • z) = c N • G ((c N)⁻¹ • z) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      rw [← ih, hhalf n, (hN (n + 1) (by omega)).1, ← two_smul ℂ, smul_smul]
      simp only [hcdef, pow_succ]
  have hF : fderiv ℂ G 0 z = c N • G ((c N)⁻¹ • z) := by
    refine tendsto_nhds_unique hlim ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn using (hconst n hn).symm
  have hpow : ∀ (n : ℕ) (x : E') (y : E), ex x = a y → ex (c n • x) = a (c n • y) := by
    intro n x y h
    induction n with
    | zero => simpa [hcdef] using h
    | succ n ih =>
      have e : c (n + 1) = c n + c n := by simp only [hcdef, pow_succ]; ring
      rw [e, add_smul, add_smul, hex, ha, ih]
  rw [hF, hpow N _ _ (hN N le_rfl).2, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero), one_smul]
end GlobalTheory.EndoLinear
