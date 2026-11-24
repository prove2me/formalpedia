-- Prove2me | solution 1 for GlobalTheory.SW.Decay.exists_fourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:45:40.383778+00:00
-- url     : https://prove2.me/submissions/ea527c77-0b43-44ec-b545-2743aea26257

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NormDetDenomLeRankOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsFourierExpansionHolomorphicTubeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsIntegralBasisHermitianMatricesDualStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TracePairingGeDetImPowHermitianHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableExpNegTraceTotallyPositiveHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DecayOfVanishingAtCusps
import Theorems.Thm_GlobalTheory_SW_Decay_herm_map
import Theorems.Thm_GlobalTheory_SW_Decay_imH_of_herm
import Theorems.Thm_GlobalTheory_SW_Decay_imH_xy
import Theorems.Thm_GlobalTheory_SW_Decay_pr_im
import Theorems.Thm_GlobalTheory_IsSiegel_smul
import Theorems.Thm_GlobalTheory_T_exists_fourier_expansion_holomorphic_tube
import Theorems.Thm_GlobalTheory_T_exists_integral_basis_hermitian_matrices_dual
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhB_posDef_eventually


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Decay
open MeasureTheory
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {N : ℕ}
namespace GlobalTheory.SW.Decay
theorem _root_.solution (hΨ : IsType Ψ) (N R : ℕ) (hR : 0 < R) :
    ∃ (m c : ℕ) (T : (Fin m → ℤ) → Matrix (Fin N) (Fin N) E) (X : (Fin m → ℝ) → CM Ψ N N),
      0 < c ∧ Function.Injective T ∧ (∀ ν, ccT (T ν) = T ν ∧ Den c (T ν)) ∧ Continuous X ∧
      (∀ x τ, (X x τ).IsHermitian) ∧ ∀ f : CM Ψ N N → ℂ,
        DifferentiableOn ℂ (fun Z : CF Ψ N N => f Z) {Z | (Z : CM Ψ N N) ∈ Hn Ψ N} →
        (∀ y : Matrix (Fin N) (Fin N) E, IntM y → ccT y = y → ∀ Z ∈ Hn Ψ N,
          f (fun τ => Z τ + ((R : E) • y).map τ.1) = f Z) →
        ∃ a : (Fin m → ℤ) → ℂ, (∀ ν, IsCoef X f (T ν) (a ν)) ∧
          ∀ Z ∈ Hn Ψ N, HasSum (fun ν => a ν * cexp (2 * π * I * pr (T ν) Z)) (f Z) := by
  obtain ⟨m, β, T, c, hc, h1, hd, hZ⟩ := GlobalTheory.T.exists_integral_basis_hermitian_matrices_dual E Ψ hΨ N R hR
  choose hβ hT hD y hy hyc hβy using h1
  set Φ : (Fin m → ℂ) → CM Ψ N N := fun z τ => ∑ j, z j • (β j).map τ.1 with hΦ
  set co : CM Ψ N N → Fin m → ℂ := fun Z j => pr (T j) Z with hco
  have hΦco : ∀ Z, Φ (co Z) = Z := fun Z => (hZ Z).symm
  have hcoΦ : ∀ z, co (Φ z) = z := by
    intro z
    funext i
    simp only [hco, hΦ, pr, Matrix.mul_sum, Matrix.mul_smul, trace_sum, trace_smul, smul_eq_mul]
    rw [Finset.sum_comm]
    have : ∀ j, ∑ τ : Ψ, z j * ((T i).map τ.1 * (β j).map τ.1).trace =
        z j * if i = j then 1 else 0 := by
      intro j
      rw [← hd i j, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [← Matrix.map_mul, AddMonoidHom.map_trace]
    simp only [this]
    simp
  set TT : (Fin m → ℤ) → Matrix (Fin N) (Fin N) E := fun ν => ∑ i, (ν i : E) • T i with hTT
  have hpr : ∀ ν Z, pr (TT ν) Z = ∑ i, (ν i : ℂ) * co Z i := by
    intro ν Z
    have : ∀ τ : Ψ, (TT ν).map τ.1 = ∑ i, (ν i : ℂ) • (T i).map τ.1 := by
      intro τ; ext a b; simp [hTT, Matrix.sum_apply]
    simp only [pr, this, hco, Matrix.sum_mul, Matrix.smul_mul, trace_sum, trace_smul, smul_eq_mul,
      Finset.mul_sum]
    exact Finset.sum_comm
  have hherm : ∀ (x : Fin m → ℝ) τ, (Φ (fun i => (x i : ℂ)) τ).IsHermitian := by
    intro x τ
    simp only [hΦ, Matrix.IsHermitian, conjTranspose_sum, conjTranspose_smul,
      (herm_map (hβ _) _).eq, star_def, conj_ofReal]
  have hadd : ∀ z w, Φ (z + w) = fun τ => Φ z τ + Φ w τ := by
    intro z w; funext τ; simp [hΦ, add_smul, Finset.sum_add_distrib]
  have hxy : ∀ x y : Fin m → ℝ, Φ (fun i => (x i : ℂ) + I * y i) =
      fun τ => Φ (fun i => (x i : ℂ)) τ + I • Φ (fun i => (y i : ℂ)) τ := by
    intro x y; funext τ
    simp only [hΦ, add_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
  have him : ∀ z τ, imH (Φ z τ) = Φ (fun i => ((z i).im : ℂ)) τ := by
    intro z τ
    have : z = fun i => ((z i).re : ℂ) + I * (z i).im := by
      funext i; rw [mul_comm, re_add_im]
    conv_lhs => rw [this, hxy]
    exact imH_xy (hherm _ τ) (hherm _ τ)
  have hΦd : Differentiable ℂ (fun (z : Fin m → ℂ) (τ : Ψ) (a b : Fin N) => Φ z τ a b) := by
    refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
    simp only [hΦ, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    fun_prop
  have hXc : Continuous fun x : Fin m → ℝ => Φ (fun i => (x i : ℂ)) :=
    hΦd.continuous.comp (continuous_pi fun i => continuous_ofReal.comp (continuous_apply i))
  have hint : ∀ k : ℤ, IsIntegral ℤ (k : E) := fun k => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := k)
  have hccT : ∀ (S : Fin m → Matrix (Fin N) (Fin N) E) (ν : Fin m → ℤ), (∀ i, ccT (S i) = S i) →
      ccT (∑ i, (ν i : E) • S i) = ∑ i, (ν i : E) • S i := by
    intro S ν hS
    ext a b
    have : ∀ i, cc (S i b a) = S i a b := fun i => congrFun (congrFun (hS i) a) b
    simp only [cc] at this
    simp [ccT, cc, Matrix.sum_apply, this]
  have hIntM : ∀ (S : Fin m → Matrix (Fin N) (Fin N) E) (ν : Fin m → ℤ), (∀ i, IntM (S i)) →
      IntM (∑ i, (ν i : E) • S i) := by
    intro S ν hS a b
    rw [Matrix.sum_apply]
    exact IsIntegral.sum _ fun i _ => (hint _).mul (hS i a b)
  refine ⟨m, c, TT, fun x => Φ (fun i => (x i : ℂ)), hc, ?_, fun ν => ⟨hccT T ν hT, ?_⟩, hXc,
    hherm, fun f hf hper => ?_⟩
  · intro ν μ h
    funext j
    have h1 := hpr ν (Φ (Pi.single j 1))
    rw [h, hpr, hcoΦ] at h1
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at h1
    exact_mod_cast h1.symm
  · have := hIntM (fun i => (c : E) • T i) ν hD
    simpa only [Den, hTT, Finset.smul_sum, smul_comm (c : E)] using this
  set Ω : Set (Fin m → ℝ) := {y | ∀ τ, (Φ (fun i => (y i : ℂ)) τ).PosDef} with hΩ
  have hmem : ∀ z : Fin m → ℂ, (fun i => (z i).im) ∈ Ω ↔ Φ z ∈ Hn Ψ N := by
    intro z; simp only [hΩ, Hn, Set.mem_setOf_eq, him]
  have hopen : IsOpen Ω := by
    refine isOpen_iff_mem_nhds.2 fun x0 hx0 => ?_
    exact Filter.eventually_all.2 fun τ => ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.posDef_eventually
      (fun x : Fin m → ℝ => Φ (fun i => (x i : ℂ)) τ)
      (fun a b => (((continuous_apply τ).comp hXc).matrix_elem a b)) (fun x => hherm x τ) x0 (hx0 τ)
  have hconv : Convex ℝ Ω := by
    intro x hx y hy s t hs ht hst τ
    have e : Φ (fun i => (((s • x + t • y) i : ℝ) : ℂ)) τ =
        (s : ℂ) • Φ (fun i => (x i : ℂ)) τ + (t : ℂ) • Φ (fun i => (y i : ℂ)) τ := by
      simp only [hΦ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ofReal_add, ofReal_mul, add_smul,
        Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
    rw [e]
    rcases hs.eq_or_lt with h0 | h0
    · have : t = 1 := by linarith
      subst this h0
      simpa using hy τ
    · exact ((hx τ).smul (by exact_mod_cast h0)).add_posSemidef
        ((hy τ).posSemidef.smul (by exact_mod_cast ht))
  obtain ⟨a, ha1, ha2⟩ := GlobalTheory.T.exists_fourier_expansion_holomorphic_tube (Fin m) Ω (fun z => f (Φ z)) hopen hconv
    (hf.comp hΦd.differentiableOn fun z hz => (hmem z).1 hz) (by
      intro z hz k
      have := hper _ (hIntM y k hy) (hccT y k hyc) _ ((hmem z).1 hz)
      rw [← this]
      change f (Φ _) = _
      rw [hadd]
      congr 1
      funext τ
      congr 1
      ext a b
      simp only [hΦ, hβy, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
        map_mul, map_sum, map_natCast, map_intCast, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
  refine ⟨a, fun ν Y hY => ?_, fun Z hZ' => ?_⟩
  · have hre : (fun i => (((co Y i).re : ℝ) : ℂ)) = co Y := by
      funext i
      refine Complex.ext (by simp) ?_
      simp [hco, pr_im (hT i), imH_of_herm (hY _).1]
    have hYe : Φ (fun i => (((co Y i).re : ℝ) : ℂ)) = Y := by rw [hre, hΦco]
    rw [ha2 (fun i => (co Y i).re) (fun τ => by rw [hYe]; exact hY τ) ν]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have e := hxy x (fun i => (co Y i).re)
    rw [hYe] at e
    simp only []
    rw [← e, hpr, hcoΦ]
  · have := ha1 (co Z) ((hmem _).2 (by rwa [hΦco]))
    simpa only [hΦco, hpr] using this
end GlobalTheory.SW.Decay
