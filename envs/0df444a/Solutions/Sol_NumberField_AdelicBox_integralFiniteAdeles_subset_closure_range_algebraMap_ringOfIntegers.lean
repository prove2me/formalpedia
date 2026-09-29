-- Prove2me | solution 1 for NumberField.AdelicBox.integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/1b45c8a8-ab41-589c-9810-faabd180a978

import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicBox_integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers

open NumberField NumberField.AdelicBox IsDedekindDomain Filter Topology MonoidWithZeroHom
open scoped Classical nonZeroDivisors Topology

noncomputable section

theorem solution (F : Type) [Field F] [NumberField F] :
    integralFiniteAdeles (𝓞 F) F
      ⊆ closure (Set.range (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F))) := by
  intro z hz
  rw [mem_closure_iff_nhds]
  intro U hU
  have hUS : U ∩ integralFiniteAdeles (𝓞 F) F ∈ 𝓝 z :=
    Filter.inter_mem hU ((isOpen_integralFiniteAdeles F).mem_nhds hz)
  obtain ⟨z', hz'⟩ := RestrictedProduct.exists_structureMap_eq_of_forall
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) hz
  have hemb := RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := Filter.cofinite)
  have hpull : RestrictedProduct.structureMap _ _ _ ⁻¹' (U ∩ integralFiniteAdeles (𝓞 F) F)
      ∈ 𝓝 z' := by
    rw [hemb.nhds_eq_comap, hz']; exact Filter.preimage_mem_comap hUS
  rw [nhds_pi, Filter.mem_pi] at hpull
  obtain ⟨T, hTfin, W, hW, hWsub⟩ := hpull

  have hWγ : ∀ v ∈ T, ∃ γ : WithZero (Multiplicative ℤ), γ ≠ 0 ∧
      ∀ w : v.adicCompletionIntegers F,
        Valued.v ((w : v.adicCompletion F) - (z' v : v.adicCompletion F)) < γ → w ∈ W v := by
    intro v _
    have hWv : W v ∈ 𝓝 (z' v) := hW v
    rw [nhds_subtype] at hWv
    obtain ⟨O, hO, hOW⟩ := hWv
    obtain ⟨γ₀, hγ₀⟩ := Valued.mem_nhds.mp hO
    refine ⟨ValueGroup₀.embedding γ₀.1, ValueGroup₀.embedding_unit_ne_zero γ₀, fun w hw => ?_⟩
    refine hOW (hγ₀ ?_)
    simp only [Set.mem_setOf_eq]
    rwa [Valuation.restrict_lt_iff_lt_embedding]
  choose γ hγne hγ using hWγ

  have hNv : ∀ v (hv : v ∈ T), ∃ r : 𝓞 F, r ≠ 0 ∧ v.intValuation r < γ v hv := by
    intro v hv
    obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.mp (hγne v hv)
    obtain ⟨π, hπI, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    obtain ⟨k, hk⟩ := WithZero.ne_zero_iff_exists.mp (v.intValuation_ne_zero π hπ0)
    have hk_le : Multiplicative.toAdd k ≤ -1 := by
      have hlt : v.intValuation π < 1 :=
        (HeightOneSpectrum.intValuation_lt_one_iff_mem v π).mpr hπI
      rw [← hk, ← WithZero.coe_one, WithZero.coe_lt_coe] at hlt
      have := Multiplicative.toAdd_lt.mpr hlt
      rw [toAdd_one] at this; omega
    let N : ℕ := (1 - Multiplicative.toAdd m).toNat + 1
    refine ⟨π ^ N, pow_ne_zero _ hπ0, ?_⟩
    rw [map_pow, ← hk, ← WithZero.coe_pow, ← hm, WithZero.coe_lt_coe,
      ← Multiplicative.toAdd_lt, toAdd_pow, nsmul_eq_mul]
    have hN1 : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero _)
    have hNm : (N : ℤ) ≥ 1 - Multiplicative.toAdd m := by
      simp only [N]; push_cast
      rcases le_or_gt (1 - Multiplicative.toAdd m) 0 with hle | hgt
      · simp only [Int.toNat_of_nonpos hle]; omega
      · rw [Int.toNat_of_nonneg hgt.le]; omega
    calc (N : ℤ) * Multiplicative.toAdd k
        ≤ (N : ℤ) * (-1) := by nlinarith [hk_le, hN1]
      _ = -(N : ℤ) := by ring
      _ ≤ Multiplicative.toAdd m - 1 := by linarith [hNm]
      _ < Multiplicative.toAdd m := by omega
  choose r hr0 hrval using hNv
  let Tf := hTfin.toFinset
  have hTmem : ∀ v ∈ Tf, v ∈ T := fun v hv => hTfin.mem_toFinset.mp hv
  set s : 𝓞 F := ∏ v ∈ Tf.attach, r v.1 (hTmem v.1 v.2) with hs_def
  have hs_ne : s ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun v _ => hr0 v.1 (hTmem v.1 v.2))
  have hsval : ∀ v (hv : v ∈ T), v.intValuation s < γ v hv := by
    intro v hv
    have hvTf : v ∈ Tf := hTfin.mem_toFinset.mpr hv
    rw [hs_def, map_prod]
    have hmem : (⟨v, hvTf⟩ : {x // x ∈ Tf}) ∈ Tf.attach := Finset.mem_attach _ _
    calc (∏ w ∈ Tf.attach, v.intValuation (r w.1 (hTmem w.1 w.2)))
        ≤ v.intValuation (r v (hTmem v hvTf)) := by
          rw [← Finset.mul_prod_erase _ _ hmem]
          exact mul_le_of_le_one_right zero_le'
            (Finset.prod_le_one (fun w _ => zero_le') (fun w _ => v.intValuation_le_one _))
      _ < γ v hv := hrval v (hTmem v hvTf)

  obtain ⟨a, ha⟩ := exists_forall_valued_sub_le (R := 𝓞 F) (K := F) hz hs_ne
  refine ⟨algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) a, ?_, a, rfl⟩
  have hιa_S : ∀ w : HeightOneSpectrum (𝓞 F),
      (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) a) w ∈
        (w.adicCompletionIntegers F : Set (w.adicCompletion F)) :=
    fun w => algebraMap_mem_adicCompletionIntegers (𝓞 F) F w a
  obtain ⟨a', ha'⟩ := RestrictedProduct.exists_structureMap_eq_of_forall
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) hιa_S
  suffices h : a' ∈ T.pi W by
    have := hWsub h; rw [Set.mem_preimage, ha'] at this; exact this.1
  intro v hv
  apply hγ v hv
  have ha'v : (a' v : v.adicCompletion F)
      = (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) a) v := by rw [← ha']; rfl
  have hz'v : (z' v : v.adicCompletion F) = z v := by rw [← hz']; rfl
  rw [ha'v, hz'v]
  calc Valued.v ((algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) a) v - z v)
      = Valued.v (z v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) := by
        rw [Valuation.map_sub_swap]; congr 2
    _ ≤ Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s)) := ha v
    _ < γ v hv := by rw [valued_algebraMap]; exact hsval v hv

end
end S_NumberField_AdelicBox_integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers
end P2MW
export P2MW.S_NumberField_AdelicBox_integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers (solution)
