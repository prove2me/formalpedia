-- Prove2me | solution 1 for GlobalTheory.ResultantNorm.eq_of_countP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:56:34.681674+00:00
-- url     : https://prove2.me/submissions/82a0139a-e3f5-4d40-bc3d-296ae0e65ae4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEq

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
open GlobalTheory
open GlobalTheory.ResultantNorm
open Polynomial Filter Topology
namespace GlobalTheory.ResultantNorm
theorem _root_.solution {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    [DecidableEq Ω] (n : ℕ) : ∀ (a b : Multiset Ω) (P Q : K[X]), a.card = n →
      P.map (algebraMap K Ω) = (a.map fun x => X - C x).prod →
      Q.map (algebraMap K Ω) = (b.map fun x => X - C x).prod →
      (∀ G : K[X], a.countP (fun x => aeval x G = 0) = b.countP (fun x => aeval x G = 0)) →
      P = Q := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b P Q hn hP hQ h
  have hinj := map_injective (algebraMap K Ω) (algebraMap K Ω).injective
  by_cases ha : a = 0
  · have h0 := h 0
    subst ha
    simp at h0
    have hb : b = 0 := by
      rw [← Multiset.card_eq_zero]
      simpa using h0.symm
    subst hb
    exact hinj (hP.trans hQ.symm)
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero ha
  have hxi : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  set G := minpoly K x with hG
  have hpos : 0 < b.countP (fun y => aeval y G = 0) := by
    rw [← h G]; exact Multiset.countP_pos.2 ⟨x, hx, minpoly.aeval K x⟩
  obtain ⟨y, hy, hyG⟩ := Multiset.countP_pos.1 hpos
  have hGy : G = minpoly K y :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hxi) hyG (minpoly.monic hxi)
  have hGm : (G.map (algebraMap K Ω)).Monic := (minpoly.monic hxi).map _
  have key : ∀ (c : Multiset Ω) (R : K[X]) (z : Ω), z ∈ c → G = minpoly K z →
      R.map (algebraMap K Ω) = (c.map fun x => X - C x).prod →
      ∃ (c' : Multiset Ω) (R' : K[X]), R = G * R' ∧ c = (G.map (algebraMap K Ω)).roots + c' ∧
        R'.map (algebraMap K Ω) = (c'.map fun x => X - C x).prod := by
    intro c R z hz hGz hR
    have hs : (R.map (algebraMap K Ω)).Splits := by
      rw [hR]; exact Splits.multisetProd (by
        intro f hf; obtain ⟨x, -, rfl⟩ := Multiset.mem_map.1 hf; exact Splits.X_sub_C x)
    have hm : (R.map (algebraMap K Ω)).Monic := by
      rw [hR]; exact monic_multisetProd_X_sub_C c
    have hr : (R.map (algebraMap K Ω)).roots = c := by
      rw [hR]; exact roots_multiset_prod_X_sub_C c
    have hz0 : aeval z R = 0 := by
      rw [← hr] at hz
      have := (mem_roots hm.ne_zero).1 hz
      rwa [IsRoot.def, eval_map_algebraMap] at this
    obtain ⟨R', hR'⟩ : G ∣ R := hGz ▸ minpoly.dvd K z hz0
    have hmul : R.map (algebraMap K Ω) = G.map (algebraMap K Ω) * R'.map (algebraMap K Ω) := by
      rw [hR', Polynomial.map_mul]
    refine ⟨(R'.map (algebraMap K Ω)).roots, R', hR', ?_, ?_⟩
    · rw [← hr, ← roots_mul (hmul ▸ hm.ne_zero), ← hmul]
    · exact (hs.of_dvd hm.ne_zero ⟨_, by rw [hmul, mul_comm]⟩).eq_prod_roots_of_monic
        (hGm.of_mul_monic_left (hmul ▸ hm))
  obtain ⟨a', P', hP1, hP2, hP3⟩ := key a P x hx hG hP
  obtain ⟨b', Q', hQ1, hQ2, hQ3⟩ := key b Q y hy hGy hQ
  have hxr : x ∈ (G.map (algebraMap K Ω)).roots := by
    rw [mem_roots hGm.ne_zero, IsRoot.def, eval_map_algebraMap]; exact minpoly.aeval K x
  have hlt : a'.card < n := by
    have := Multiset.card_pos_iff_exists_mem.2 ⟨x, hxr⟩
    rw [← hn, hP2, Multiset.card_add]; omega
  rw [hP1, hQ1, ih _ hlt a' b' P' Q' rfl hP3 hQ3 fun H => ?_]
  have := h H
  rw [hP2, hQ2, Multiset.countP_add, Multiset.countP_add] at this
  omega
end GlobalTheory.ResultantNorm
