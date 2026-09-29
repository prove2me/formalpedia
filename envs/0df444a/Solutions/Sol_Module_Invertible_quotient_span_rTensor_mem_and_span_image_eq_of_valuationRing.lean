-- Prove2me | solution 1 for Module.Invertible.quotient_span_rTensor_mem_and_span_image_eq_of_valuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/6e3bd450-eb0f-5cda-a162-b10ff4e13f49

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Invertible_quotient_span_rTensor_mem_and_span_image_eq_of_valuationRing

set_option autoImplicit false

open TensorProduct

universe u v w

theorem VAAux.span_pair_eq_span_singleton (V : Type v) [CommRing V] [IsDomain V] [ValuationRing V]
    (L : Type v) [Field L] [Algebra V L] [IsFractionRing V L] (a g : L) :
    ∃ h : L, Submodule.span V {a, g} = Submodule.span V {h} := by
  classical
  obtain ⟨x, d, hd, hx⟩ := IsFractionRing.div_surjective (A := V) a
  obtain ⟨y, d', hd', hy⟩ := IsFractionRing.div_surjective (A := V) g
  have hd0 : algebraMap V L d ≠ 0 := IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors L le_rfl hd
  have hd'0 : algebraMap V L d' ≠ 0 := IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors L le_rfl hd'

  rcases ValuationRing.dvd_total (x * d') (y * d) with ⟨c, hc⟩ | ⟨c, hc⟩
  ·
    refine ⟨a, ?_⟩
    have hg : g = c • a := by
      rw [← hx, ← hy, Algebra.smul_def]
      field_simp
      have := congrArg (algebraMap V L) hc
      simp only [map_mul] at this
      linear_combination this
    rw [hg]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro z (rfl | rfl)
      · exact Submodule.subset_span rfl
      · exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    · exact Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  · refine ⟨g, ?_⟩
    have ha : a = c • g := by
      rw [← hx, ← hy, Algebra.smul_def]
      field_simp
      have := congrArg (algebraMap V L) hc
      simp only [map_mul] at this
      linear_combination this
    rw [ha]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro z (rfl | rfl)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
      · exact Submodule.subset_span rfl
    · exact Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl))

theorem VAAux.exists_span_eq_span_singleton (V : Type v) [CommRing V] [IsDomain V] [ValuationRing V]
    (L : Type v) [Field L] [Algebra V L] [IsFractionRing V L] (s : Finset L) :
    ∃ g : L, Submodule.span V (s : Set L) = Submodule.span V {g} := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨g, hg⟩ := ih
    obtain ⟨h, hh⟩ := VAAux.span_pair_eq_span_singleton V L a g
    refine ⟨h, ?_⟩
    rw [Finset.coe_insert, Submodule.span_insert, hg, ← Submodule.span_insert, hh]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem solution
    {𝒪 : Type u} [CommRing 𝒪]
    (V : Type v) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra 𝒪 V]
    (L : Type v) [Field L] [Algebra 𝒪 L] [Algebra V L] [IsScalarTower 𝒪 V L] [IsFractionRing V L]
    (M : Type w) [AddCommGroup M] [Module 𝒪 M] [Module.Finite 𝒪 M]
    (N : Submodule L (L ⊗[𝒪] M)) (hN : Module.Invertible L ((L ⊗[𝒪] M) ⧸ N)) :
    Module.Invertible V ((V ⊗[𝒪] M) ⧸ Submodule.span V
        {x : V ⊗[𝒪] M | LinearMap.rTensor M (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap x ∈ N}) ∧
      Submodule.span L (LinearMap.rTensor M (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap ''
        (Submodule.span V {x : V ⊗[𝒪] M | LinearMap.rTensor M (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap x ∈ N} :
          Set (V ⊗[𝒪] M))) = N := by
  classical

  set φ : V ⊗[𝒪] M →ₗ[𝒪] L ⊗[𝒪] M := LinearMap.rTensor M (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap with hφ
  set S : Set (V ⊗[𝒪] M) := {x : V ⊗[𝒪] M | φ x ∈ N} with hS

  let e : L ⊗[V] (V ⊗[𝒪] M) ≃ₗ[L] L ⊗[𝒪] M := TensorProduct.AlgebraTensorModule.cancelBaseChange 𝒪 V L L M
  let ι : V ⊗[𝒪] M →ₗ[V] L ⊗[V] (V ⊗[𝒪] M) := TensorProduct.mk V L (V ⊗[𝒪] M) 1
  let φV : V ⊗[𝒪] M →ₗ[V] L ⊗[𝒪] M := (e.restrictScalars V).toLinearMap ∘ₗ ι
  have hφV : ∀ x, φV x = φ x := by
    intro x
    show e (1 ⊗ₜ[V] x) = φ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, hφ, LinearMap.rTensor_tmul]
      simp [Algebra.smul_def]
    | add x y hx hy => rw [TensorProduct.tmul_add, map_add, hx, hy, map_add]

  let N₀ : Submodule V (V ⊗[𝒪] M) := (N.restrictScalars V).comap φV
  have hN₀S : (N₀ : Set (V ⊗[𝒪] M)) = S := by
    ext x; simp [N₀, hS, hφV]
  have hspanS : Submodule.span V S = N₀ := by
    rw [← hN₀S, Submodule.span_eq]
  rw [hspanS]

  haveI : IsLocalizedModule (nonZeroDivisors V) ι := inferInstance
  constructor
  ·
    haveI : Module.Free L ((L ⊗[𝒪] M) ⧸ N) := Module.Free.of_divisionRing L _
    have hfr : Module.finrank L ((L ⊗[𝒪] M) ⧸ N) = 1 := Module.Invertible.finrank_eq_one L _
    haveI : Module.Finite L ((L ⊗[𝒪] M) ⧸ N) := Module.finite_of_finrank_pos (by rw [hfr]; exact one_pos)
    let eQ : ((L ⊗[𝒪] M) ⧸ N) ≃ₗ[L] L := LinearEquiv.ofFinrankEq _ _ (by rw [hfr, Module.finrank_self])

    let ψ : V ⊗[𝒪] M →ₗ[V] L := (eQ.restrictScalars V).toLinearMap ∘ₗ ((N.mkQ).restrictScalars V ∘ₗ φV)
    have hψ : ∀ x, ψ x = eQ (N.mkQ (φV x)) := fun _ => rfl
    have hkerψ : LinearMap.ker ψ = N₀ := by
      ext x
      rw [LinearMap.mem_ker, hψ, map_eq_zero_iff _ eQ.injective, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      rfl
    let I : Submodule V L := LinearMap.range ψ
    have eI : ((V ⊗[𝒪] M) ⧸ N₀) ≃ₗ[V] ↥I := (Submodule.quotEquivOfEq _ _ hkerψ.symm).trans ψ.quotKerEquivRange

    haveI : Module.Finite V (V ⊗[𝒪] M) := inferInstance
    have hIfg : I.FG := Module.Finite.iff_fg.mp inferInstance
    obtain ⟨t, ht⟩ := hIfg
    obtain ⟨g, hg⟩ := VAAux.exists_span_eq_span_singleton V L t
    have hIg : I = Submodule.span V {g} := by rw [← ht, hg]

    have hg0 : g ≠ 0 := by
      intro hg0
      have hI0 : I = ⊥ := by rw [hIg, hg0, Submodule.span_singleton_eq_bot]
      have hφN : ∀ p : V ⊗[𝒪] M, φ p ∈ N := by
        intro p
        have : ψ p ∈ I := LinearMap.mem_range_self ψ p
        rw [hI0, Submodule.mem_bot, hψ, map_eq_zero_iff _ eQ.injective, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero, hφV] at this
        exact this
      have hNtop : N = ⊤ := by
        rw [eq_top_iff]
        intro n _
        obtain ⟨⟨p, s⟩, hps⟩ := IsLocalizedModule.surj (nonZeroDivisors V) ι (e.symm n)
        have hs0 : (algebraMap V L s) ≠ 0 :=
          IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors L le_rfl s.2
        have h1 : algebraMap V L s • n = φ p := by
          have := congrArg e hps
          simp only [Submonoid.smul_def] at this
          rw [← algebraMap_smul (A := L), map_smul, LinearEquiv.apply_symm_apply] at this
          rw [← hφV]; exact this
        have : n = (algebraMap V L s)⁻¹ • φ p := by rw [← h1, smul_smul, inv_mul_cancel₀ hs0, one_smul]
        rw [this]; exact N.smul_mem _ (hφN p)
      haveI : Subsingleton ((L ⊗[𝒪] M) ⧸ N) := Submodule.Quotient.subsingleton_iff.mpr hNtop
      have := Module.finrank_zero_of_subsingleton (R := L) (M := (L ⊗[𝒪] M) ⧸ N)
      rw [hfr] at this
      exact one_ne_zero this

    have eIV : ↥I ≃ₗ[V] V := (LinearEquiv.ofEq _ _ hIg).trans (LinearEquiv.toSpanNonzeroSingleton V L g hg0).symm
    exact Module.Invertible.congr (eI.trans eIV).symm
  ·
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have : φV x ∈ N := hx
      rwa [hφV] at this
    · intro n hn
      obtain ⟨⟨p, s⟩, hps⟩ := IsLocalizedModule.surj (nonZeroDivisors V) ι (e.symm n)

      have hs0 : (algebraMap V L s) ≠ 0 :=
        IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors L le_rfl s.2
      have h1 : algebraMap V L s • n = φ p := by
        have := congrArg e hps
        simp only [Submonoid.smul_def] at this
        rw [← algebraMap_smul (A := L), map_smul, LinearEquiv.apply_symm_apply] at this
        rw [← hφV]; exact this
      have hpS : p ∈ N₀ := by
        show φV p ∈ N
        rw [hφV, ← h1]; exact N.smul_mem _ hn
      have : n = (algebraMap V L s)⁻¹ • φ p := by rw [← h1, smul_smul, inv_mul_cancel₀ hs0, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, hpS, rfl⟩)

end S_Module_Invertible_quotient_span_rTensor_mem_and_span_image_eq_of_valuationRing
end P2MW
export P2MW.S_Module_Invertible_quotient_span_rTensor_mem_and_span_image_eq_of_valuationRing (solution)
