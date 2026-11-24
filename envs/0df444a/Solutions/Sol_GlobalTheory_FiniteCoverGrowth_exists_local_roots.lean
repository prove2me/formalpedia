-- Prove2me | solution 1 for GlobalTheory.FiniteCoverGrowth.exists_local_roots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:45:21.691273+00:00
-- url     : https://prove2.me/submissions/fea672de-f093-4ee6-bad1-5b5878942e2d

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IntegralAndRationalOfPolynomialGrowth
import Theorems.Thm_GlobalTheory_FiniteCoverGrowth_exists_local_root
import Theorems.Thm_GlobalTheory_FiniteCoverGrowth_card_roots

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.FiniteCoverGrowth
namespace GlobalTheory.FiniteCoverGrowth
theorem _root_.solution {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (hp : p.Monic)
    (x₀ : Fin d → ℂ) (hs : (p.map (MvPolynomial.eval x₀)).Separable) :
    ∃ y : Fin p.natDegree → (Fin d → ℂ) → ℂ, (∀ i, DifferentiableAt ℂ (y i) x₀) ∧
      ∀ᶠ x in 𝓝 x₀, Function.Injective (fun i => y i x) ∧
        (p.map (MvPolynomial.eval x)).roots.toFinset = Finset.univ.image (fun i => y i x) := by
  classical
  have hc := card_roots (hp.map (MvPolynomial.eval x₀)) hs
  rw [hp.natDegree_map] at hc
  let e := (Finset.equivFinOfCardEq hc).symm
  have hroot : ∀ i, (p.map (MvPolynomial.eval x₀)).eval (e i : ℂ) = 0 := fun i =>
    Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.1 (e i).2)
  choose y hy0 hyd hyr using fun i => exists_local_root p x₀ (e i) (hroot i)
    (by simpa using hs.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := (e i : ℂ)) (by simpa using hroot i))
  refine ⟨y, hyd, ?_⟩
  have hne : ∀ᶠ x in 𝓝 x₀, ∀ i j, i ≠ j → y i x ≠ y j x := by
    simp only [eventually_all]
    intro i j hij
    refine ((hyd i).continuousAt.ne_iff_eventually_ne (hyd j).continuousAt).1 ?_
    rw [hy0, hy0]
    exact fun h => hij (e.injective (Subtype.ext h))
  filter_upwards [hne, eventually_all.2 hyr] with x h1 h2
  have hinj : Function.Injective (fun i => y i x) := fun i j h => by
    by_contra hij; exact h1 i j hij h
  refine ⟨hinj, (Finset.eq_of_subset_of_card_le ?_ ?_).symm⟩
  · intro a ha
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
    exact Multiset.mem_toFinset.2 ((Polynomial.mem_roots (hp.map _).ne_zero).2 (h2 i))
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    refine (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans ?_)
    rw [hp.natDegree_map]
end GlobalTheory.FiniteCoverGrowth
