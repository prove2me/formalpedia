-- Prove2me | solution 1 for N25.cusp_complex_endpoint_exhausts_poles
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:10.980207+00:00
-- url     : https://prove2.me/submissions/9dcca12d-6b2f-46cb-8152-b520bc670ee1

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Theorems.Thm_N25_finite_limit_iff_nonnegative_of_normalized_leading
import Theorems.Thm_ModularCurve_exists_tendsto_realizeOf_mul_exp_of_not_mem_toValuationSubring
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve CongruenceSubgroup

open scoped MatrixGroups Topology

namespace N25

private theorem mem_iff_order_nonnegative {F : Type*} [Field F] [Algebra ℂ F]
    (P : Place ℂ F) (x : F) : x ∈ P.toValuationSubring ↔ 0 ≤ P.ord x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  constructor
  · intro hm
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible P.toValuationSubring
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨x, hm⟩ : P.toValuationSubring)) (by simpa [Subtype.ext_iff] using hx) hπ
    have he : x = ((u : P.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
      have h := congrArg Subtype.val hu
      push_cast at h
      rw [zpow_natCast]
      exact h
    rw [he, P.ord_unit_smul_zpow u hπ (n : ℤ)]
    exact Int.natCast_nonneg n
  · intro hn
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible P.toValuationSubring
    obtain ⟨u, hu⟩ := P.exists_unit_mul_zpow hx hπ
    rw [hu, show P.ord x = ((P.ord x).toNat : ℤ) from (Int.toNat_of_nonneg hn).symm,
      zpow_natCast]
    exact mul_mem (u : P.toValuationSubring).2 (pow_mem (π : P.toValuationSubring).2 _)

/-- Every actual complex j-pole is one of the analytically characterized cusp endpoints. -/
theorem _root_.solution
    (endpoint : SL(2, ℤ) → AlgebraicCurve.Place ℂ
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField 25 N25.H25)))
    (hmem : ∀ (B : SL(2, ℤ))
      (x : ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField 25 N25.H25)),
      x ∈ (endpoint B).toValuationSubring ↔ ∃ L : ℂ, Filter.Tendsto
        (fun τ : UpperHalfPlane => ModularCurve.realizeOf (CohCarrier.GammaH 25 N25.H25)
          (x : LaurentSeries ℂ) (B • τ)) UpperHalfPlane.atImInfty (nhds L))
    (j : ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField 25 N25.H25))
    (hj : (j : LaurentSeries ℂ) = ModularCurve.jqModC ℂ)
    (P : AlgebraicCurve.Place ℂ
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField 25 N25.H25)))
    (hP : P.ord j < 0) :
    ∃ B : SL(2, ℤ), endpoint B = P := by
  let Γ := CohCarrier.GammaH 25 N25.H25
  let F₀ := xHFunctionField 25 N25.H25
  have hΓ : IsCongruenceSubgroup Γ :=
    isCongruenceSubgroup_trans (Gamma1 25) Γ (Gamma1_le_GammaH 25 N25.H25) (Gamma1_is_congruence 25)
  letI : Γ.FiniteIndex := hΓ.finiteIndex
  have hT : ModularGroup.T ∈ Γ := translation_mem_GammaH 25 N25.H25
  have hdeg := finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
    ℂ 25 N25.H25 j hj
  have hPnot : j ∉ P.toValuationSubring := by
    intro hm
    exact (not_le_of_gt hP) ((mem_iff_order_nonnegative P j).mp hm)
  obtain ⟨σ, h, hh, hperiod, hordj, hlead⟩ :=
    exists_tendsto_realizeOf_mul_exp_of_not_mem_toValuationSubring
      Γ hT hΓ F₀ rfl j hj hdeg P hPnot
  refine ⟨σ, ?_⟩
  apply Place.ext
  apply SetLike.ext
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [hmem, mem_iff_order_nonnegative P x]
  obtain ⟨L, hL, ht⟩ := hlead x hx
  let a : ℝ := (P.ord x : ℝ) / (h : ℝ)
  let f : UpperHalfPlane → ℂ := fun τ => realizeOf Γ (x : LaurentSeries ℂ) (σ • τ)
  have he :
      (fun τ : UpperHalfPlane => f τ /
        Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (τ : ℂ))) =
      (fun τ : UpperHalfPlane => realizeOf Γ (x : LaurentSeries ℂ) (σ • τ) *
        Complex.exp (-(2 * Real.pi * Complex.I * (P.ord x : ℂ) * (τ : ℂ) / (h : ℂ)))) := by
    funext τ
    dsimp only [f, a]
    rw [div_eq_mul_inv, ← Complex.exp_neg]
    congr 2
    push_cast
    ring
  have ht' : Filter.Tendsto
      (fun τ : UpperHalfPlane => f τ /
        Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (τ : ℂ)))
      UpperHalfPlane.atImInfty (nhds L) := by
    rw [he]
    exact ht
  have hs := finite_limit_iff_nonnegative_of_normalized_leading f a L hL ht'
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
  have hsign : 0 ≤ a ↔ 0 ≤ P.ord x := by
    dsimp only [a]
    rw [le_div_iff₀ hhR, zero_mul]
    exact_mod_cast (Iff.rfl : 0 ≤ P.ord x ↔ 0 ≤ P.ord x)
  exact hs.trans hsign

end N25
