-- Prove2me | solution 1 for GlobalTheory.MassOrth.exists_max_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:13:07.892008+00:00
-- url     : https://prove2.me/submissions/c56e0bac-a6f8-4c7e-9371-57e154fc9b0f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaxVector
import Theorems.Thm_GlobalTheory_MassOrth_bound_of_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.MassOrth
variable {K V Γ : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
namespace GlobalTheory.MassOrth
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (θ : K) (hθ : θ ∈ biInt v)
    (hθ' : v (θ - star θ) = 1) (Λ : Submodule (biInt v) V) (hΛ : Λ.FG) :
    ∃ x ∈ Λ, ∀ y ∈ Λ, ∀ z ∈ Λ, v (h y z) ≤ v (h x x) := by
  obtain ⟨T, rfl⟩ := hΛ
  rcases T.eq_empty_or_nonempty with rfl | hT
  · refine ⟨0, Submodule.zero_mem _, fun y hy z hz => ?_⟩
    have : y = 0 := by simpa using hy
    simp [this]
  obtain ⟨⟨x, y⟩, hxy, hmax⟩ := (T ×ˢ T).exists_max_image (fun p => v (h p.1 p.2)) (hT.product hT)
  obtain ⟨hx, hy⟩ := Finset.mem_product.1 hxy
  have hb := bound_of_span v h (T : Set V) (v (h x y))
    (fun a ha b hb => hmax (a, b) (Finset.mem_product.2 ⟨ha, hb⟩))
  by_contra hcon
  have hlt : ∀ w ∈ Submodule.span (biInt v) (T : Set V), v (h w w) < v (h x y) := by
    intro w hw
    by_contra hn
    exact hcon ⟨w, hw, fun a ha b hb' => (hb a ha b hb').trans (not_lt.1 hn)⟩
  have hx' : x ∈ Submodule.span (biInt v) (T : Set V) := Submodule.subset_span hx
  have hy' : y ∈ Submodule.span (biInt v) (T : Set V) := Submodule.subset_span hy
  have hyx : h y x = star (h x y) := (hs.eq x y).symm
  have key : ∀ c ∈ biInt v, v (c * h x y + star c * star (h x y)) < v (h x y) := by
    intro c hc
    have hcy : c • y ∈ Submodule.span (biInt v) (T : Set V) :=
      Submodule.smul_mem _ (⟨c, hc⟩ : biInt v) hy'
    have e : c * h x y + star c * star (h x y) =
        h (x + c • y) (x + c • y) - h x x - h (c • y) (c • y) := by
      simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        RingHom.id_apply, hyx, starRingEnd_apply]
      ring
    rw [e]
    exact v.map_sub_lt (v.map_sub_lt (hlt _ (Submodule.add_mem _ hx' hcy)) (hlt _ hx')) (hlt _ hcy)
  have k1 := key 1 (biInt v).one_mem
  have k2 := key θ hθ
  have k3 : v (star θ * (1 * h x y + star 1 * star (h x y))) < v (h x y) := by
    rw [map_mul]
    exact lt_of_le_of_lt ((mul_le_mul' hθ.2 le_rfl).trans (by simp)) k1
  have k4 := v.map_sub_lt k2 k3
  have e : θ * h x y + star θ * star (h x y) - star θ * (1 * h x y + star 1 * star (h x y)) =
      (θ - star θ) * h x y := by
    rw [star_one]; ring
  rw [e, map_mul, hθ', one_mul] at k4
  exact lt_irrefl _ k4
end GlobalTheory.MassOrth
