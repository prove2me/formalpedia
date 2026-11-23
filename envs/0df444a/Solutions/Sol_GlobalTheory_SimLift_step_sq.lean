-- Prove2me | solution 1 for GlobalTheory.SimLift.step_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:09.338995+00:00
-- url     : https://prove2.me/submissions/fa913e4d-8f3d-4260-a48f-54a2dc5e60b9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ModNOfDvdModulus
import Theorems.Thm_GlobalTheory_SimLift_form_skew
import Theorems.Thm_GlobalTheory_SimLift_exists_rep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.SimLift
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
namespace GlobalTheory.SimLift
theorem _root_.solution {n : ℕ} (hn : 0 < n) {f : D.La →ₗ[𝓞 E] D.La} {ν : ℤ} (hf : IsSimMod D n f ν) :
    ∃ f', IsSimMod D (n * n) f' ν ∧ ∀ a, D.ModN n (f' a - f a) := by
  obtain ⟨hc, hB⟩ := hf
  have hc2 : IsCoprime ν ((n * n : ℕ) : ℤ) := by
    push_cast; exact hc.mul_right hc
  obtain ⟨κ, t, hκ⟩ := hc
  choose B hB using hB
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨u, hu⟩ := exists_rep D B
    (fun a a' b => by
      apply mul_left_cancel₀ hn'
      rw [mul_add, ← hB, ← hB, ← hB]
      simp only [map_add, LinearMap.add_apply]; ring)
    (fun a b b' => by
      apply mul_left_cancel₀ hn'
      rw [mul_add, ← hB, ← hB, ← hB]
      simp only [map_add]; ring)
    (fun c a b => by
      apply mul_left_cancel₀ hn'
      rw [← hB, ← hB, f.map_smul, f.map_smul, D.adj, D.adj])
  have hskew : ∀ a b, B a b = -B b a := fun a b => by
    apply mul_left_cancel₀ hn'
    rw [mul_neg, ← hB, ← hB, form_skew D (f a), form_skew D a]; ring
  have hsa : ∀ a b, D.EF a (u b) = D.EF (u a) b := fun a b => by
    rw [form_skew D a, hu, hu, hskew a b]
  set v : D.La →ₗ[𝓞 E] D.La := H.w0 • u with hv
  have hkey : ∀ a b, D.EF (v a) b + D.EF a (v b) = B a b := fun a b => by
    have h1 : D.EF a (v b) = D.EF ((1 - H.w0) • u a) b := by
      have hb : H.bar (1 - H.w0) = H.w0 := by
        rw [map_sub, map_one, HostModel.cmHost_bar_halfIntegerGenerator]; ring
      rw [← u.map_smul, ← hsa, D.adj, hb, hv, LinearMap.smul_apply]
    rw [h1, ← LinearMap.add_apply, ← map_add, hv, LinearMap.smul_apply, ← add_smul, ← hu]
    simp
  have hff : ∀ a b, D.EF (f a) (f b) = ν * D.EF a b + n * B a b := fun a b => by
    rw [← hB]; ring
  refine ⟨f - ((n : ℤ) * κ) • (f ∘ₗ v), ⟨hc2, fun a b => ?_⟩, fun a => ⟨-(κ • f (v a)), ?_⟩⟩
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sub, map_zsmul,
      smul_eq_mul, hff]
    refine ⟨t * B a b - κ * (B (v a) b + B a (v b)) +
      κ * κ * (ν * D.EF (v a) (v b) + n * B (v a) (v b)), ?_⟩
    push_cast
    linear_combination (-(n : ℤ) * κ * ν) * hkey a b - (n : ℤ) * B a b * hκ
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    rw [mul_smul, natCast_zsmul, smul_neg]; abel
end GlobalTheory.SimLift
