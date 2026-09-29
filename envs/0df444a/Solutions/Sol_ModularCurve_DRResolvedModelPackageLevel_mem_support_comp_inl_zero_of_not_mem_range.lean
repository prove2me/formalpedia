-- Prove2me | solution 1 for ModularCurve.DRResolvedModelPackageLevel.mem_support_comp_inl_zero_of_not_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/2b9a8fa9-12b2-599f-991d-5cd4ef12c65d

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRResolvedModelPackageLevel_mem_support_comp_inl_zero_of_not_mem_range

set_option autoImplicit false

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (𝔛reg : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ)
    (t : Spec (CommRingCat.of O) ⟶ 𝔛reg.Y) (ht : t ≫ 𝔛reg.toBase = 𝟙 _)
    (hout : (t ≫ 𝔛reg.toDR).base (IsLocalRing.closedPoint O) ∉ Set.range (𝔓.comp κ (toκ.comp ρO) 1 ≫ DRLevel.bcMap ρO toκ).base) :
    t.base (IsLocalRing.closedPoint O) ∈ ((𝔛reg.comp (Sum.inl 0)).support : Set ↥𝔛reg.Y) ∧
      ∀ w, w ≠ Sum.inl 0 → t.base (IsLocalRing.closedPoint O) ∉ ((𝔛reg.comp w).support : Set ↥𝔛reg.Y) := by
  set y₀ : ↥𝔛reg.Y := t.base (IsLocalRing.closedPoint O) with hy₀
  have hy₀base : 𝔛reg.toBase.base y₀ = IsLocalRing.closedPoint O := by
    change (t ≫ 𝔛reg.toBase).base (IsLocalRing.closedPoint O) = _
    rw [ht]; rfl
  have htoDR : (t ≫ 𝔛reg.toDR).base (IsLocalRing.closedPoint O) = 𝔛reg.toDR.base y₀ := rfl

  have hpm : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := by rw [hϖ]; exact Ideal.subset_span rfl
  have hker : RingHom.ker toκ = IsLocalRing.maximalIdeal O := by
    refine ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (RingHom.ker_ne_top toκ) ?_).symm
    rw [hϖ, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_natCast]
    exact CharP.cast_eq_zero κ p
  have hpt : (Spec.map (CommRingCat.ofHom toκ)).base (IsLocalRing.closedPoint κ) = IsLocalRing.closedPoint O := by
    apply PrimeSpectrum.ext
    change Ideal.comap toκ (IsLocalRing.closedPoint κ).asIdeal = (IsLocalRing.closedPoint O).asIdeal
    rw [show (IsLocalRing.closedPoint κ).asIdeal = ⊥ from Ideal.eq_bot_of_prime _]
    exact hker

  have hexc : ∀ (n : 𝔛reg.node) (i : Fin (𝔛reg.width n - 1)), y₀ ∉ ((𝔛reg.comp (Sum.inr ⟨n, i⟩)).support : Set ↥𝔛reg.Y) := by
    intro n i hmem
    apply hout
    rw [htoDR, 𝔛reg.exc_image n i y₀ hmem]
    refine ⟨(pullback.snd (𝔓.comp κ (toκ.comp ρO) 0) (𝔓.comp κ (toκ.comp ρO) 1)).base (𝔛reg.nodeEquiv n), ?_⟩
    have hc := congrArg (fun h => (h ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv n))
      (pullback.condition (f := 𝔓.comp κ (toκ.comp ρO) 0) (g := 𝔓.comp κ (toκ.comp ρO) 1))
    simp only [Category.assoc] at hc
    exact hc.symm

  have hstr : y₀ ∉ ((𝔛reg.comp (Sum.inl 1)).support : Set ↥𝔛reg.Y) := by
    intro hmem
    obtain ⟨e, _, _, hec⟩ := 𝔛reg.strict_iso 1
    have hmem' : y₀ ∈ Set.range (𝔛reg.comp (Sum.inl 1)).subschemeι.base := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hmem
    obtain ⟨y₁, hy₁⟩ := hmem'
    obtain ⟨z, hz₁, -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := (𝔛reg.comp (Sum.inl 1)).subschemeι ≫ 𝔛reg.toBase) (g := Spec.map (CommRingCat.ofHom toκ))
      y₁ (IsLocalRing.closedPoint κ) (by
        rw [hpt]
        change 𝔛reg.toBase.base ((𝔛reg.comp (Sum.inl 1)).subschemeι.base y₁) = _
        rw [hy₁, hy₀base])
    apply hout
    refine ⟨e.base z, ?_⟩
    rw [htoDR]
    change (e ≫ 𝔓.comp κ (toκ.comp ρO) 1 ≫ DRLevel.bcMap ρO toκ).base z = _
    rw [hec]
    change 𝔛reg.toDR.base ((𝔛reg.comp (Sum.inl 1)).subschemeι.base ((pullback.fst ((𝔛reg.comp (Sum.inl 1)).subschemeι ≫ 𝔛reg.toBase) (Spec.map (CommRingCat.ofHom toκ))).base z)) = _
    rw [hz₁, hy₁]

  have hsome : ∃ v, y₀ ∈ ((𝔛reg.comp v).support : Set ↥𝔛reg.Y) := by
    obtain ⟨U, hU, hyU, -⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := y₀) (U := ⊤) trivial
    have hprod : y₀ ∈ (∏ v, 𝔛reg.comp v).support := by
      rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hyU, 𝔛reg.comp_prod ⟨U, hU⟩,
        Scheme.mem_zeroLocus_iff]
      intro f hf
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hf
      rw [Scheme.basicOpen_mul]
      rintro ⟨-, hyp⟩

      have h1 : ((p : ℕ) : Γ(𝔛reg.Y, U)) = 𝔛reg.Y.presheaf.map (homOfLE le_top).op
          (𝔛reg.toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ((p : ℕ) : O))) := by
        simp only [map_natCast]
      rw [h1, Scheme.basicOpen_res, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine] at hyp
      have h2 : 𝔛reg.toBase.base y₀ ∈ PrimeSpectrum.basicOpen ((p : ℕ) : O) := hyp.2
      rw [hy₀base] at h2
      exact h2 hpm

    have key : ∀ (s : Finset (X0MqComponents 𝔛reg.width)),
        y₀ ∈ (∏ v ∈ s, 𝔛reg.comp v).support → ∃ v ∈ s, y₀ ∈ ((𝔛reg.comp v).support : Set ↥𝔛reg.Y) := by
      intro s
      induction s using Finset.cons_induction with
      | empty =>
        intro h
        simp only [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top] at h
        exact h.elim
      | cons a s has ih =>
        intro h
        rw [Finset.prod_cons, Scheme.IdealSheafData.support_mul] at h
        rcases h with h | h
        · exact ⟨a, Finset.mem_cons_self a s, h⟩
        · obtain ⟨v, hv, hv'⟩ := ih h
          exact ⟨v, Finset.mem_cons.mpr (Or.inr hv), hv'⟩
    obtain ⟨v, -, hv⟩ := key Finset.univ hprod
    exact ⟨v, hv⟩

  have hothers : ∀ w, w ≠ Sum.inl 0 → y₀ ∉ ((𝔛reg.comp w).support : Set ↥𝔛reg.Y) := by
    rintro (j | ⟨n, j⟩) hw
    · have hj : j = 1 := by
        have hne : j ≠ 0 := fun h => hw (by rw [h])
        fin_cases j <;> simp_all
      subst hj
      exact hstr
    · exact hexc n j
  refine ⟨?_, hothers⟩
  obtain ⟨v, hv⟩ := hsome
  by_contra hnot
  exact hothers v (fun h => hnot (h ▸ hv)) hv

#print axioms solution

end S_ModularCurve_DRResolvedModelPackageLevel_mem_support_comp_inl_zero_of_not_mem_range
end P2MW
export P2MW.S_ModularCurve_DRResolvedModelPackageLevel_mem_support_comp_inl_zero_of_not_mem_range (solution)
