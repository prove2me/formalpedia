-- Prove2me | solution 1 for GlobalTheory.InvBilinTest.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:51:24.691616+00:00
-- url     : https://prove2.me/submissions/3d1ab0c9-2409-498b-b39f-dbe43af4b5bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantCosetInd
import Theorems.Thm_GlobalTheory_InvBilinTest_cosetInd_apply
import Theorems.Thm_GlobalTheory_InvBilinTest_isLocallyConstant_cosetInd
import Theorems.Thm_GlobalTheory_InvBilinTest_integral_ite
import Theorems.Thm_GlobalTheory_OpTrace_eq_of_forall_dual
import Theorems.Thm_GlobalTheory_OpTrace_map_lcIntegral
import Theorems.Thm_GlobalTheory_PRep_IsSmooth_map_smoothOp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace
noncomputable section
open GlobalTheory GlobalTheory.InvBilinTest
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
variable [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
  {Y : Type} [AddCommGroup Y] [Module ℂ Y]
namespace GlobalTheory.InvBilinTest
theorem _root_.solution [μ.IsMulRightInvariant] (hπ : IsSmooth π) (B : SB G →ₗ[ℂ] V →ₗ[ℂ] Y)
    (hB : ∀ (g : G) (φ ψ : SB G) (v : V), (∀ x, ψ.1 x = φ.1 (x * g)) → B ψ (π g v) = B φ v)
    (K : Subgroup G) (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G))
    (φ : SB G) (hφ : ∀ k ∈ K, ∀ g, φ.1 (k * g) = φ.1 g) (v : V) :
    B (cosetInd K ho hK 1) (smoothOp π μ φ.1 v) = (μ.real K : ℂ) • B φ v := by
  classical
  have hF : IsLocallyConstant fun g => φ.1 g • cosetInd K ho hK g :=
    φ.2.1.comp₂ (isLocallyConstant_cosetInd K ho hK) (· • ·)
  have hc : HasCompactSupport fun g => φ.1 g • cosetInd K ho hK g :=
    HasCompactSupport.intro φ.2.2 fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]
  have h1 : lcIntegral μ (fun g => φ.1 g • cosetInd K ho hK g) = (μ.real K : ℂ) • φ := by
    refine Subtype.ext (funext fun x => ?_)
    have := map_lcIntegral (μ := μ) hF hc (LinearMap.proj (R := ℂ) (φ := fun _ : G => ℂ) x ∘ₗ (SB G).subtype)
    refine this.trans ?_
    show ∫ g, φ.1 g * (cosetInd K ho hK g).1 x ∂μ = (μ.real K : ℂ) * φ.1 x
    rw [← integral_ite K ho, ← integral_mul_right_eq_self _ x]
    congr 1
    ext g
    rw [cosetInd_apply]
    by_cases hg : g ∈ K
    · simp [hg, hφ g hg]
    · simp [hg]
  refine eq_of_forall_dual fun l => ?_
  have h2 := map_lcIntegral (μ := μ) hF hc (l ∘ₗ B.flip v)
  have h3 := hπ.map_smoothOp (μ := μ) φ.2.1 φ.2.2 (l ∘ₗ B (cosetInd K ho hK 1)) v
  rw [h1] at h2
  simp only [LinearMap.comp_apply, map_smul, LinearMap.flip_apply] at h2 h3 ⊢
  rw [h2, h3]
  congr 1
  ext g
  rw [hB g (cosetInd K ho hK g) (cosetInd K ho hK 1) v fun x => by simp [cosetInd_apply]]
end GlobalTheory.InvBilinTest
