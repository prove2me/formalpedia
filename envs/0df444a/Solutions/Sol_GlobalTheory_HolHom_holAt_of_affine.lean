-- Prove2me | solution 1 for GlobalTheory.HolHom.holAt_of_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:55:06.838514+00:00
-- url     : https://prove2.me/submissions/329bd58b-00b2-40c6-8392-c84c8e5c87f5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_valR_res
import Theorems.Thm_GlobalTheory_HolHom_le_preimage_iff
import Theorems.Thm_GlobalTheory_HolHom_le_basicOpen_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolHom
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
namespace GlobalTheory.HolHom
theorem _root_.solution {c : V → (Sp ℂ ⟶ X)} {z : V} {P : X.Opens} (hP : IsAffineOpen P) (h₀ : ⊤ ≤ c z ⁻¹ᵁ P)
    (hev : ∀ᶠ t in 𝓝 z, ⊤ ≤ c t ⁻¹ᵁ P) (hd : ∀ g : Γ(X, P), DifferentiableAt ℂ (fun t => valAt' (c t) P g) z) :
    HolAt c z := by
  intro U hU
  obtain ⟨s, hsU, hs₀⟩ := hP.exists_basicOpen_le (V := U) ⟨_, (le_preimage_iff _ U).1 hU⟩ ((le_preimage_iff _ P).1 h₀)
  have hs : valAt' (c z) P s ≠ 0 := (le_basicOpen_iff _ h₀ s).1 ((le_preimage_iff _ _).2 hs₀)
  have hN : ∀ᶠ t in 𝓝 z, ⊤ ≤ c t ⁻¹ᵁ X.basicOpen s := by
    filter_upwards [hev, (hd s).continuousAt.eventually_ne hs] with t h1 h2 using (le_basicOpen_iff _ h1 s).2 h2
  refine ⟨hN.mono fun t ht => le_trans ht ((c t).preimage_mono hsU), fun f => ?_⟩
  obtain ⟨n, g, hg⟩ := exists_eq_pow_mul_of_isAffineOpen X P hP s ((X.presheaf.map (homOfLE hsU).op).hom f)
  have key : ∀ᶠ t in 𝓝 z, valAt' (c t) U f = valAt' (c t) P g / valAt' (c t) P s ^ n := by
    filter_upwards [hev, hN] with t hp ht
    have hne := (le_basicOpen_iff _ hp s).1 ht
    have h1 := valR_res (c t) (X.basicOpen_le s) g ht
    have h2 := valR_res (c t) (X.basicOpen_le s) s ht
    have h3 := valR_res (c t) hsU f ht
    have hg' : (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom g =
        (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom s ^ n * (X.presheaf.map (homOfLE hsU).op).hom f := hg
    rw [eq_div_iff (pow_ne_zero n hne)]
    simp only [valAt'_eq_valR]
    rw [← h1, ← h2, ← h3, hg', valR_eq _ _ ht, valR_eq _ _ ht, valR_eq _ _ ht, map_mul, map_pow, mul_comm]
  simp only [div_eq_mul_inv] at key
  exact ((hd g).fun_mul (((hd s).fun_pow n).fun_inv (pow_ne_zero n hs))).congr_of_eventuallyEq key
end GlobalTheory.HolHom
