-- Prove2me | solution 1 for GlobalTheory.LocalLift.exists_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:05:06.943936+00:00
-- url     : https://prove2.me/submissions/6d6cd924-e6e2-47a0-9ddd-0fa9923264a3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTestFunctionsSubsetOfMemNhds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEtaleCoordsVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HolDifferentiableAt
import Theorems.Thm_GlobalTheory_LocalLift_hol_eventually_mem
import Theorems.Thm_GlobalTheory_LocalLift_hol_differentiableAt
import Theorems.Thm_GlobalTheory_HolChart_exists_etale_coords_vanishing
import Theorems.Thm_GlobalTheory_HolChart_hol_of_affine
import Theorems.Thm_GlobalTheory_TangentOrigin_eq_spMap_of_evalPt
import Theorems.Thm_GlobalTheory_TangentOrigin_exists_evalPt_eq
import Theorems.Thm_GlobalTheory_TangentOrigin_ext_evalPt
import Theorems.Thm_GlobalTheory_exists_holomorphic_section_of_etale
import Theorems.Thm_GlobalTheory_top_le_preimage_iff_mem
import Theorems.Thm_P2M_GlobalTheory_valAt__constFn_1b31686fad50
import Theorems.Thm_P2M_GlobalTheory_valAt__rules_bb0546efa0f1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology GlobalTheory.TangentOrigin
noncomputable section
open GlobalTheory GlobalTheory.LocalLift
variable {Y : Scheme.{0}}
namespace GlobalTheory.LocalLift
theorem _root_.solution (s : Y ⟶ Sp ℂ) [Smooth s] (x : Sp ℂ ⟶ Y) (hx : x ≫ s = 𝟙 _) :
    ∃ (n : ℕ) (U : Y.Opens) (t : Fin n → Γ(Y, U)) (W : Set (Fin n → ℂ)) (p : (Fin n → ℂ) → (Sp ℂ ⟶ Y)),
      IsAffineOpen U ∧ ⊤ ≤ x ⁻¹ᵁ U ∧ 0 ∈ W ∧ p 0 = x ∧ IsHolTo W p ∧ (∀ w, p w ≫ s = 𝟙 _) ∧
      (∀ w ∈ W, ∀ i, valAt' (p w) U (t i) = w i) ∧
      ∀ (g : ℕ) (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)), (∀ z, e z ≫ s = 𝟙 _) → IsHolTo Set.univ e → e 0 = x →
        ∀ᶠ z in 𝓝 (0 : Fin g → ℂ), e z = p (fun i => valAt' (e z) U (t i)) := by
  obtain ⟨U₀, -, U, hU, hp, hle, hsm⟩ := Smooth.exists_isStandardSmooth s (x (default : PrimeSpectrum ℂ))
  have hU₀ : U₀ = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : s (x (default : PrimeSpectrum ℂ)) ∈ U₀ := hle hp
    have h2 : y = s (x (default : PrimeSpectrum ℂ)) :=
      Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [h2]; exact h1
  subst hU₀
  obtain ⟨n, hn⟩ : ∃ n, RingHom.IsStandardSmoothOfRelativeDimension n (s.appLE ⊤ U hle).hom := by
    let _ := (s.appLE ⊤ U hle).hom.toAlgebra
    have : Algebra.IsStandardSmooth Γ(Sp ℂ, ⊤) Γ(Y, U) := hsm
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := this
    exact ⟨P.dimension, _, _, _, ‹_›, P, rfl⟩
  let c : ℂ →+* Γ(Y, U) :=
    (s.appLE ⊤ U hle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have hcc : ∀ a, constFn s U a = c a := fun a => rfl
  have hc : c.IsStandardSmoothOfRelativeDimension n :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 (s.appLE ⊤ U hle).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv hn
  have hpts : ∀ (y : Sp ℂ ⟶ Y) (hy : ⊤ ≤ y ⁻¹ᵁ U), y ≫ s = 𝟙 _ → ∀ a, evalPt y U hy (c a) = a := by
    intro y hy hys a
    rw [← valAt'_eq_evalPt, ← hcc]
    exact valAt'_constFn y s hys U a hy
  have hxU : ⊤ ≤ x ⁻¹ᵁ U := (top_le_preimage_iff_mem x U).2 hp
  obtain ⟨φ, hφc, hφ, hφ0⟩ := HolChart.exists_etale_coords_vanishing c hc (evalPt x U hxU) (hpts x hxU hx)
  let _ : Algebra ℂ Γ(Y, U) := c.toAlgebra
  let _ : Algebra (MvPolynomial (Fin n) ℂ) Γ(Y, U) := φ.toAlgebra
  have _ : IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(Y, U) :=
    IsScalarTower.of_algebraMap_eq' hφc.symm
  have _ : Algebra.Etale (MvPolynomial (Fin n) ℂ) Γ(Y, U) := hφ
  let eA : Γ(Y, U) →ₐ[ℂ] ℂ := { evalPt x U hxU with commutes' := hpts x hxU hx }
  obtain ⟨W, σ, m, f, ε, hW, hW0, hσ0, hε, hσd, hσt, hσs⟩ :=
    exists_holomorphic_section_of_etale n Γ(Y, U) eA hφ0
  choose p hpU hpσ using fun w => exists_evalPt_eq hU (σ w).toRingHom
  have hval : ∀ w a, valAt' (p w) U a = σ w a := fun w a => by
    rw [valAt'_eq_evalPt _ _ (hpU w), hpσ]; rfl
  refine ⟨n, U, fun i => φ (MvPolynomial.X i), W, p, hU, hxU, hW0, ?_, ?_, ?_, ?_, ?_⟩
  · refine ext_evalPt hU (hpU 0) hxU ?_
    rw [hpσ, hσ0]
  · intro V a
    refine HolChart.hol_of_affine valAt'_rules hU hW p (fun w _ => hpU w) (fun b => ?_) V a
    simpa only [hval] using hσd b
  · intro w
    refine (eq_spMap_of_evalPt _ (RingHom.id ℂ) fun a => ?_).trans (Spec.map_id _)
    rw [← evalPt_constFn s (p w) U (hpU w), hpσ, hcc]
    exact (σ w).commutes a
  · intro w hw i
    rw [hval]; exact hσt w hw i
  · intro g e hes he he0
    have h0 : ⊤ ≤ e 0 ⁻¹ᵁ U := he0 ▸ hxU
    have hk : ∀ᶠ z in 𝓝 (0 : Fin g → ℂ), ∀ k, ‖valAt' (e z) U (f k) - eA (f k)‖ < ε := by
      refine eventually_all.2 fun k => ?_
      have h1 := (hol_differentiableAt he (Set.mem_univ _) h0 (f k)).continuousAt
      have h2 : valAt' (e 0) U (f k) = eA (f k) := by
        rw [he0, valAt'_eq_evalPt _ _ hxU]; rfl
      have := h1.eventually (Metric.ball_mem_nhds _ hε)
      simpa only [Metric.mem_ball, dist_eq_norm, h2] using this
    filter_upwards [hk, hol_eventually_mem he (Set.mem_univ _) h0] with z hz hzU
    let xA : Γ(Y, U) →ₐ[ℂ] ℂ := { evalPt (e z) U hzU.2 with commutes' := hpts _ hzU.2 (hes z) }
    have hxA : ∀ a, xA a = valAt' (e z) U a := fun a => (valAt'_eq_evalPt _ _ hzU.2 a).symm
    obtain ⟨w, hw, hxw⟩ := hσs xA (fun k => by rw [hxA]; exact hz k)
    have hwe : (fun i => valAt' (e z) U (φ (MvPolynomial.X i))) = w := by
      funext i
      rw [← hxA, hxw]; exact hσt w hw i
    rw [hwe]
    refine ext_evalPt hU hzU.2 (hpU w) ?_
    rw [hpσ, ← hxw]
end GlobalTheory.LocalLift
