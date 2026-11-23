-- Prove2me | solution 1 for GlobalTheory.LocalQuad.denseRange_finite_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:49.105526+00:00
-- url     : https://prove2.me/submissions/a0fd82bb-4f9c-46de-8eed-e8fd731652b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsForallAbvSubLt
import Theorems.Thm_GlobalTheory_LocalQuad_Approx_exists_forall_abv_sub_lt
import Theorems.Thm_GlobalTheory_LocalQuad_Approx_abv_inl
import Theorems.Thm_GlobalTheory_LocalQuad_Approx_abv_isNontrivial
import Theorems.Thm_GlobalTheory_LocalQuad_Approx_abv_pairwise

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open NumberField IsDedekindDomain
open scoped Matrix WithZero
variable {F : Type} [Field F] [NumberField F]
namespace _root_.GlobalTheory.LocalQuad
theorem _root_.solution (F : Type) [Field F] [NumberField F]
    (T : Finset (HeightOneSpectrum (𝓞 F))) :
    DenseRange (fun x : F =>
      ((fun v : T => algebraMap F (v.1.adicCompletion F) x, fun σ : F →+* ℝ => σ x) :
        ((v : T) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ))) := by
  classical
  rw [Metric.denseRange_iff]
  rintro ⟨a, b⟩ r hr
  have hr2 : 0 < r / 2 := half_pos hr
  choose y hy using fun v : T ↦
    (HeightOneSpectrum.denseRange_algebraMap (K := F) v.1).exists_dist_lt (a v) hr2
  choose q hq using fun σ : F →+* ℝ ↦ exists_rat_btwn (show b σ - r / 2 < b σ + r / 2 by linarith)
  let z : T ⊕ (F →+* ℝ) → F := fun i ↦ match i with
    | Sum.inl v => y v
    | Sum.inr σ => (q σ : F)
  obtain ⟨x, hx⟩ := _root_.GlobalTheory.LocalQuad.Approx.exists_forall_abv_sub_lt
    (_root_.GlobalTheory.LocalQuad.Approx.abv_isNontrivial T)
    (_root_.GlobalTheory.LocalQuad.Approx.abv_pairwise T) z hr2
  refine ⟨x, ?_⟩
  rw [Prod.dist_eq, max_lt_iff]
  constructor
  · rw [dist_pi_lt_iff hr]
    intro v
    have hxv := hx (Sum.inl v)
    rw [_root_.GlobalTheory.LocalQuad.Approx.abv_inl, map_sub, ← dist_eq_norm] at hxv
    calc dist (a v) (algebraMap F (v.1.adicCompletion F) x)
        ≤ dist (a v) (algebraMap F (v.1.adicCompletion F) (y v)) +
          dist (algebraMap F (v.1.adicCompletion F) (y v)) (algebraMap F (v.1.adicCompletion F) x) :=
          dist_triangle _ _ _
      _ < r / 2 + r / 2 := add_lt_add (hy v) hxv
      _ = r := add_halves r
  · rw [dist_pi_lt_iff hr]
    intro σ
    have hxσ := hx (Sum.inr σ)
    change InfinitePlace.mk (Complex.ofRealHom.comp σ) ((q σ : F) - x) < r / 2 at hxσ
    rw [InfinitePlace.apply] at hxσ
    simp only [RingHom.comp_apply, map_sub, map_ratCast, Complex.ofRealHom_eq_coe] at hxσ
    rw [← Complex.ofReal_ratCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hxσ
    rw [Real.dist_eq]
    have hqσ := hq σ
    rw [abs_lt] at hxσ ⊢
    constructor <;> linarith [hxσ.1, hxσ.2, hqσ.1, hqσ.2]
end _root_.GlobalTheory.LocalQuad
