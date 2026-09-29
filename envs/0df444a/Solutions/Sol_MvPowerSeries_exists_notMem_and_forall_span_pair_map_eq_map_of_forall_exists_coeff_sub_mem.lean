-- Prove2me | solution 1 for MvPowerSeries.exists_notMem_and_forall_span_pair_map_eq_map_of_forall_exists_coeff_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/584a630b-5dd6-55f9-a58e-01301dce1c39

import Mathlib
import Theorems.Thm_MvPowerSeries_isNoetherianRing_fin_of_isNoetherianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_exists_notMem_and_forall_span_pair_map_eq_map_of_forall_exists_coeff_sub_mem

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace Nak2GenAux

variable {R : Type} [CommRing R]

noncomputable def emm (𝔫 : Ideal R) : Ideal (MvPowerSeries (Fin 2) R) :=
  Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) R)) ⊔
    𝔫.map (algebraMap R (MvPowerSeries (Fin 2) R))

theorem X_mem_emm (𝔫 : Ideal R) (i : Fin 2) :
    (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ∈ emm 𝔫 :=
  Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)

theorem algebraMap_mem_emm (𝔫 : Ideal R) {n : R} (hn : n ∈ 𝔫) :
    algebraMap R (MvPowerSeries (Fin 2) R) n ∈ emm 𝔫 :=
  Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hn)

theorem constantCoeff_mem_of_mem_emm (𝔫 : Ideal R) {t : MvPowerSeries (Fin 2) R}
    (ht : t ∈ emm 𝔫) : MvPowerSeries.constantCoeff t ∈ 𝔫 := by
  have h : emm 𝔫 ≤ 𝔫.comap (MvPowerSeries.constantCoeff : MvPowerSeries (Fin 2) R →+* R) := by
    refine sup_le ?_ ?_
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap, MvPowerSeries.constantCoeff_X]
      exact zero_mem _
    · rw [Ideal.map_le_iff_le_comap]
      intro n hn
      simp only [Ideal.mem_comap, MvPowerSeries.algebraMap_apply, MvPowerSeries.constantCoeff_C,
        Algebra.algebraMap_self, RingHom.id_apply]
      exact hn
  exact h ht

theorem mem_mul_of_coeff_mem [IsNoetherianRing R] (J : Ideal (MvPowerSeries (Fin 2) R))
    (hproj : Module.Projective R (MvPowerSeries (Fin 2) R ⧸ J)) (𝔫 : Ideal R)
    {e : MvPowerSeries (Fin 2) R} (he : e ∈ J) (hcoef : ∀ d, MvPowerSeries.coeff d e ∈ 𝔫) :
    e ∈ emm 𝔫 * J := by
  classical

  obtain ⟨k, n, hn⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian 𝔫)
  have hnmem : ∀ l, n l ∈ 𝔫 := fun l => hn ▸ Submodule.subset_span ⟨l, rfl⟩
  have hc : ∀ d, ∃ c : Fin k → R, ∑ l, c l * n l = MvPowerSeries.coeff d e := by
    intro d
    have := hcoef d
    rw [← hn, Submodule.mem_span_range_iff_exists_fun] at this
    simpa only [smul_eq_mul] using this
  choose u hu using hc
  let E : Fin k → MvPowerSeries (Fin 2) R := fun l => show MvPowerSeries (Fin 2) R from fun d => u d l
  have hE : e = ∑ l, n l • E l := by
    ext d
    simp only [map_sum, map_smul, smul_eq_mul]
    rw [← hu d]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
    rfl

  haveI := hproj
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    (Ideal.Quotient.mkₐ R J).toLinearMap LinearMap.id (Ideal.Quotient.mkₐ_surjective R J)
  have h2 : ∀ y, Ideal.Quotient.mk J (s y) = y := fun y => by
    simpa using LinearMap.congr_fun hs y
  let π : MvPowerSeries (Fin 2) R →ₗ[R] MvPowerSeries (Fin 2) R :=
    LinearMap.id - s ∘ₗ (Ideal.Quotient.mkₐ R J).toLinearMap
  have hπJ : ∀ a, π a ∈ J := by
    intro a
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, map_sub, h2, sub_self]
  have hπid : ∀ a ∈ J, π a = a := by
    intro a ha
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr ha,
      map_zero, sub_zero]
  rw [← hπid e he, hE, map_sum]
  refine Ideal.sum_mem _ fun l _ => ?_
  rw [map_smul, Algebra.smul_def]
  exact Ideal.mul_mem_mul (algebraMap_mem_emm 𝔫 (hnmem l)) (hπJ _)

theorem main [IsNoetherianRing R] (J : Ideal (MvPowerSeries (Fin 2) R))
    (hproj : Module.Projective R (MvPowerSeries (Fin 2) R ⧸ J))
    (𝔫 : Ideal R) (h𝔫 : 𝔫 ≠ ⊤)
    (r : Fin 2 → MvPowerSeries (Fin 2) R) (hr : ∀ j, r j ∈ J)
    (hgen : ∀ f ∈ J, ∃ (a b : Fin 2 → MvPowerSeries (Fin 2) R), (∀ i, b i ∈ J) ∧
      ∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d (f - (∑ j, a j * r j + ∑ i, MvPowerSeries.X i * b i)) ∈ 𝔫) :
    ∃ g : R, g ∉ 𝔫 ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'], IsUnit (algebraMap R R' g) →
      Ideal.span (Set.range fun j => MvPowerSeries.map (algebraMap R R') (r j)) =
        J.map (MvPowerSeries.map (algebraMap R R')) := by
  classical
  haveI : IsNoetherianRing (MvPowerSeries (Fin 2) R) :=
    MvPowerSeries.isNoetherianRing_fin_of_isNoetherianRing R 2
  set N : Ideal (MvPowerSeries (Fin 2) R) := Ideal.span (Set.range r) with hNdef
  have hJfg : (J : Submodule (MvPowerSeries (Fin 2) R) (MvPowerSeries (Fin 2) R)).FG :=
    IsNoetherian.noetherian J

  have hle : J ≤ N ⊔ emm 𝔫 • J := by
    intro f hf
    obtain ⟨a, b, hb, hcoef⟩ := hgen f hf
    set e := f - (∑ j, a j * r j + ∑ i, MvPowerSeries.X i * b i) with hedef
    have he : e ∈ J :=
      J.sub_mem hf (J.add_mem (J.sum_mem fun j _ => J.mul_mem_left _ (hr j))
        (J.sum_mem fun i _ => J.mul_mem_left _ (hb i)))
    have he' : e ∈ emm 𝔫 * J := mem_mul_of_coeff_mem J hproj 𝔫 he hcoef
    have hf' : f = ∑ j, a j * r j + (∑ i, MvPowerSeries.X i * b i + e) := by
      rw [hedef]; abel
    rw [hf']
    refine Submodule.add_mem_sup (Ideal.sum_mem _ fun j _ =>
      Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)) ?_
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => ?_) he'
    exact Submodule.smul_mem_smul (X_mem_emm 𝔫 i) (hb i)

  obtain ⟨t, ht1, htJ⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hJfg le_rfl hle
  refine ⟨MvPowerSeries.constantCoeff t, ?_, ?_⟩
  · intro hg
    have h1 : MvPowerSeries.constantCoeff (t - 1) ∈ 𝔫 := constantCoeff_mem_of_mem_emm 𝔫 ht1
    rw [map_sub, map_one] at h1
    apply h𝔫
    rw [Ideal.eq_top_iff_one]
    have := 𝔫.sub_mem hg h1
    rwa [sub_sub_cancel] at this
  · intro R' _ _ hu
    set φ : MvPowerSeries (Fin 2) R →+* MvPowerSeries (Fin 2) R' :=
      MvPowerSeries.map (algebraMap R R') with hφ
    have htu : IsUnit (φ t) := by
      rw [MvPowerSeries.isUnit_iff_constantCoeff, hφ, MvPowerSeries.constantCoeff_map]
      exact hu
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact Ideal.mem_map_of_mem _ (hr j)
    · have hspan : Ideal.span (Set.range fun j => φ (r j)) = N.map φ := by
        rw [hNdef, Ideal.map_span, ← Set.range_comp]
        rfl
      rw [hspan, Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap]
      have htf : t • f ∈ N := htJ (Submodule.smul_mem_pointwise_smul f t J hf)
      rw [smul_eq_mul] at htf
      have hφf : φ f = ↑(htu.unit⁻¹) * φ (t * f) := by
        rw [map_mul, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
      rw [hφf]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ htf)

end Nak2GenAux

theorem solution
    {R : Type} [CommRing R] [IsNoetherianRing R] (J : Ideal (MvPowerSeries (Fin 2) R))
    (hproj : Module.Projective R (MvPowerSeries (Fin 2) R ⧸ J))
    (𝔫 : Ideal R) (h𝔫 : 𝔫 ≠ ⊤)
    (r : Fin 2 → MvPowerSeries (Fin 2) R) (hr : ∀ j, r j ∈ J)
    (hgen : ∀ f ∈ J, ∃ (a b : Fin 2 → MvPowerSeries (Fin 2) R), (∀ i, b i ∈ J) ∧
      ∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d (f - (∑ j, a j * r j + ∑ i, MvPowerSeries.X i * b i)) ∈ 𝔫) :
    ∃ g : R, g ∉ 𝔫 ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'], IsUnit (algebraMap R R' g) →
      Ideal.span (Set.range fun j => MvPowerSeries.map (algebraMap R R') (r j)) =
        J.map (MvPowerSeries.map (algebraMap R R')) :=
  Nak2GenAux.main J hproj 𝔫 h𝔫 r hr hgen

end S_MvPowerSeries_exists_notMem_and_forall_span_pair_map_eq_map_of_forall_exists_coeff_sub_mem
end P2MW
export P2MW.S_MvPowerSeries_exists_notMem_and_forall_span_pair_map_eq_map_of_forall_exists_coeff_sub_mem (solution)
