-- Prove2me | solution 1 for GlobalTheory.LevelDict.sections_eq_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:35:24.836324+00:00
-- url     : https://prove2.me/submissions/07781b72-b5f2-4e9d-88c2-44475a7e109f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_LevBasis
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_UnimodularAndTangentOfIsAH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LevelThreeSeparatesTangentVectors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_LineBundlePowSectionsEqThetaLevel
import Theorems.Thm_P2M_GlobalTheory_LevelDict_valAt__powSecEquiv_5d24a446204e
import Theorems.Thm_GlobalTheory_LevelDict_transfer
import Theorems.Thm_GlobalTheory_LevelDict_ext_of_ne_zero
import Theorems.Thm_GlobalTheory_LevelDict_exists_frame_ratio
import Theorems.Thm_GlobalTheory_LevelDict_isLevel_thetaChar
import Theorems.Thm_GlobalTheory_PullHermitian_exists_chart
import Theorems.Thm_GlobalTheory_UnifCompare_injective
import Theorems.Thm_GlobalTheory_UnifCompare_mem_iff
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
import Theorems.Thm_GlobalTheory_existsUnique_linear_lift_of_isHolTo
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_GlobalTheory_top_le_preimage_mono
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_ex_add
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.LevelDict
namespace GlobalTheory.LevelDict
theorem _root_.solution : ThetaUnifAV → ∀ (g : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (l : ℕ), charHalf g a b → Wit x h u τ a b → (∀ s : RR x l, ∃! F, IsLevel τ a b l F ∧ FnPw x u s F) ∧ ∀ F, IsLevel τ a b l F → ∃! s : RR x l, FnPw x u s F := by
  intro hT g x h u τ a b l hab ⟨hs, hp, hΛ, _, hth, _⟩
  subst h
  obtain ⟨u₀, H₀, χ₀, -, hu₀, -, hv, hw, -, hsec, -⟩ := hT x.P x.rig x.rig_gen
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo x.P.A x.P.isAb x.P.L x.P.g x.P.g u₀ hv hw u.ex u.ex_add
    (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  let e : (Fin x.P.g → ℂ) ≃ₗ[ℂ] (Fin x.P.g → ℂ) := LinearEquiv.ofInjectiveEndo F (UnifCompare.injective u u₀ F hF)
  have he : ∀ z, e z = F z := fun z => rfl
  have hed : Differentiable ℂ e := (LinearMap.toContinuousLinearMap F).differentiable
  have hed' : Differentiable ℂ e.symm := (LinearMap.toContinuousLinearMap e.symm.toLinearMap).differentiable
  obtain ⟨r, hr, hr0, hrf⟩ := exists_frame_ratio x.P.isLB u u₀ F hF
  obtain ⟨hθ, hθ0⟩ := isLevel_thetaChar hs hp hab
  let G : ((Fin x.P.g → ℂ) → ℂ) ≃ ((Fin x.P.g → ℂ) → ℂ) :=
    { toFun := fun f z => f (e z) * r z ^ l
      invFun := fun f w => f (e.symm w) * (r (e.symm w) ^ l)⁻¹
      left_inv := fun f => funext fun w => by
        simp only [e.apply_symm_apply]
        exact mul_inv_cancel_right₀ (pow_ne_zero _ (hr0 _)) _
      right_inv := fun f => funext fun z => by
        simp only [e.symm_apply_apply]
        exact inv_mul_cancel_right₀ (pow_ne_zero _ (hr0 _)) _ }
  have hG : ∀ f z, G f z = f (e z) * r z ^ l := fun _ _ => rfl

  have key : ∀ (m n : Fin x.P.g → ℤ) (k : u₀.Λ), (k : Fin x.P.g → ℂ) =
      e ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) → ∀ z,
      χ₀ k * Complex.exp (Real.pi * hermForm H₀ (e z) k + Real.pi / 2 * hermForm H₀ k k) *
        r (z + ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))) =
      Complex.exp (2 * Real.pi * Complex.I * (a ⬝ᵥ (fun i => (m i : ℂ)) - b ⬝ᵥ (fun i => (n i : ℂ)) -
        ((fun i => (n i : ℂ)) ⬝ᵥ τ.mulVec (fun i => (n i : ℂ))) / 2 - (fun i => (n i : ℂ)) ⬝ᵥ z)) * r z := by
    intro m n k hk
    have hec := hed.continuous
    have hrc := hr.continuous
    refine ext_of_ne_zero hθ.1 hθ0 ?_ ?_ fun z hz => ?_
    · unfold hermForm
      fun_prop
    · fun_prop
    · have h1 := hθ.2 m n z
      rw [pow_one] at h1
      set w := (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)) with hw
      have hper : u.ex (z + w) = u.ex z := by
        rw [u.ex_add, (u.ker w).2 ((hΛ w).2 ⟨m, n, hw⟩), _root_.mul_one]
      obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex z).left x.P.isLB
      have hi' : ⊤ ≤ (u.ex (z + w)).left ⁻¹ᵁ x.P.L.U i := by rwa [hper]
      have h2 := hth i z hi
      have h3 := hth i _ hi'
      rw [hper, h2, h1] at h3
      have h4 := hu₀.2.2.2 k i (e z) (by rw [he, hF]; exact hi)
      rw [hk, ← map_add, he, he (z + w), hrf i z hi, hrf i _ hi', ← he, ← hk] at h4
      refine mul_right_cancel₀ (mul_ne_zero hz (u.fr_ne i _ hi')) ?_
      unfold hermForm
      linear_combination r z * h3 - thetaChar τ a b z * h4
  refine transfer (powSecEquiv x.P.L l) G (fun f => ?_) (fun s f => ?_) (hsec l)
  on_goal 1 => refine ⟨fun hf => ⟨?_, fun k w => ?_⟩, fun hf => ⟨?_, fun m n z => ?_⟩⟩
  on_goal 5 => refine ⟨fun hf j w hj => ?_, fun hf i z hi => ?_⟩
  · rw [← G.symm_apply_apply f]
    exact (hf.1.comp hed').mul (((hr.comp hed').pow l).inv fun w => pow_ne_zero _ (hr0 _))
  · obtain ⟨z, rfl⟩ := e.surjective w
    obtain ⟨m, n, hmn⟩ := (hΛ (e.symm k)).1 ((UnifCompare.mem_iff u u₀ F hF _).1 (by
      rw [← he, e.apply_symm_apply]; exact k.2))
    have hk := e.symm_apply_eq.1 hmn
    have h1 := hf.2 m n z
    rw [hG, hG, map_add, ← hk, mul_comm (f (e z)), ← _root_.mul_assoc, ← mul_pow, ← key m n k hk z, mul_pow] at h1
    refine mul_right_cancel₀ (pow_ne_zero l (hr0 _)) (h1.trans ?_)
    ring
  · exact (hf.1.comp hed).mul (hr.pow l)
  · have hk := (UnifCompare.mem_iff u u₀ F hF _).2 ((hΛ _).2 ⟨m, n, rfl⟩)
    have h1 := hf.2 ⟨e _, hk⟩ (e z)
    rw [hG, hG, map_add, mul_comm (f (e z)), ← _root_.mul_assoc, ← mul_pow, ← key m n ⟨e _, hk⟩ rfl z, mul_pow, h1]
    ring
  · obtain ⟨z, rfl⟩ := e.surjective w
    rw [he] at hj ⊢
    rw [hF] at hj ⊢
    have hi := top_le_preimage_mono _ (powChart_le _ _ j) hj
    rw [← valAt'_powSecEquiv _ _ s _ j hi, hrf _ z hi, mul_pow, ← _root_.mul_assoc]
    exact hf _ z hi
  · have h1 := hf (fun _ => i) (F z) (by rw [hF]; exact top_le_preimage_mono _ (le_powChart _ _ fun _ => i) hi)
    rw [hF, hrf i z hi, mul_pow, ← _root_.mul_assoc] at h1
    exact (valAt'_powSecEquiv _ _ s _ (fun _ => i) hi).trans h1
end GlobalTheory.LevelDict
