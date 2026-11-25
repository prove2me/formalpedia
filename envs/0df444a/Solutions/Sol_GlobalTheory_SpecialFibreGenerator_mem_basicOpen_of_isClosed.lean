-- Prove2me | solution 1 for GlobalTheory.SpecialFibreGenerator.mem_basicOpen_of_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:20:41.239804+00:00
-- url     : https://prove2.me/submissions/a6cf9003-1b66-4a86-99ae-a9abedf39166

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecGeneratesSpecialFibre
import Theorems.Thm_GlobalTheory_SpecialFibreGenerator_mem_basicOpen_of_chart
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineX
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineY
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originW
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originZ



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false
open GlobalTheory
open GlobalTheory.SpecialFibreGenerator
open TopologicalSpace Opposite
variable {X Y : Scheme.{0}}
namespace GlobalTheory.SpecialFibreGenerator
theorem _root_.solution [AlgebraicGeometry.IsIntegral X] {t : Γ(X, ⊤)} {ξ : X}
    (hξ : ∀ x : X, x ∉ X.basicOpen t ↔ ξ ⤳ x)
    (hp : ∀ U : X.Opens, IsAffineOpen U → ξ ∈ U →
      Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
    {L : LB X} (s : L.Sec) {b : L.ι} (hb : ξ ∈ X.basicOpen (s.f b)) {Z : Set X} (hZ : IsClosed Z)
    (hZt : Z ⊆ X.basicOpen t)
    (hs : ∀ y ∈ X.basicOpen t, y ∉ Z → ∃ c, y ∈ X.basicOpen (s.f c))
    {x : X} (hx : x ∉ X.basicOpen t) {a : L.ι} (ha : x ∈ L.U a) : x ∈ X.basicOpen (s.f a) := by
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset
    (U := L.U a ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩) (x := x) ⟨ha, fun h ↦ hx (hZt h)⟩
  have hWa : W ≤ L.U a := fun y hy ↦ (hWU hy).1
  have hξW : ξ ∈ W := ((hξ x).1 hx).mem_open W.isOpen hxW
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hpr := hp W hW hξW
  set p := X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t with hpd
  set σ := X.presheaf.map (homOfLE hWa).op (s.f a) with hσd
  have hpb : X.basicOpen p = W ⊓ X.basicOpen t := X.basicOpen_res _ _
  have hσb : X.basicOpen σ = W ⊓ X.basicOpen (s.f a) := X.basicOpen_res _ _
  have hle : X.basicOpen p ≤ X.basicOpen σ := fun y hy ↦ by
    obtain ⟨h₁, h₂⟩ := hpb.le hy
    obtain ⟨c, hc⟩ := hs y h₂ (hWU h₁).2
    exact hσb.ge ⟨h₁, mem_basicOpen_of_chart s (hWa h₁) hc⟩
  have hrad : p ∈ (Ideal.span {σ}).radical := by
    rw [← PrimeSpectrum.basicOpen_le_basicOpen_iff]
    have := hW.fromSpec.preimage_mono hle
    rwa [hW.fromSpec_preimage_basicOpen, hW.fromSpec_preimage_basicOpen] at this
  obtain ⟨m, hm⟩ := hrad
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow hpr m).1 (Ideal.mem_span_singleton.1 hm)
  obtain rfl | hi0 := eq_or_ne i 0
  · have hu : IsUnit σ := associated_one_iff_isUnit.1 (by simpa using hi)
    exact (hσb.le ((X.basicOpen_of_isUnit hu).ge hxW)).2
  · obtain ⟨q, hq⟩ := (dvd_pow_self p hi0).trans hi.symm.dvd
    have h₁ : ξ ∈ X.basicOpen σ := hσb.ge ⟨hξW, mem_basicOpen_of_chart s (hWa hξW) hb⟩
    rw [hq, Scheme.basicOpen_mul] at h₁
    exact absurd (hpb.le h₁.1).2 ((hξ ξ).2 specializes_rfl)
end GlobalTheory.SpecialFibreGenerator
